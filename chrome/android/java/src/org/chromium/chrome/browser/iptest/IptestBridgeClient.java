// Copyright 2026 The IP-TEST Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

package org.chromium.chrome.browser.iptest;

import android.content.Context;
import android.content.Intent;

import org.chromium.base.CommandLine;
import org.chromium.base.Log;
import org.chromium.base.ThreadUtils;
import org.chromium.chrome.browser.browsing_data.BrowsingDataBridge;
import org.chromium.chrome.browser.browsing_data.BrowsingDataType;
import org.chromium.chrome.browser.ChromeTabbedActivity;
import org.chromium.chrome.browser.profiles.Profile;
import org.chromium.chrome.browser.tab.EmptyTabObserver;
import org.chromium.chrome.browser.tab.Tab;
import org.chromium.chrome.browser.tab.TabLaunchType;
import org.chromium.chrome.browser.tab.TabSelectionType;
import org.chromium.chrome.browser.tabmodel.TabModel;
import org.chromium.chrome.browser.tabmodel.TabModelUtils;
import org.chromium.chrome.browser.browsing_data.TimePeriod;
import org.chromium.content_public.browser.LoadUrlParams;
import org.chromium.content_public.browser.NavigationHandle;
import org.chromium.content_public.browser.RenderFrameHost;
import org.chromium.content_public.browser.WebContents;
import org.chromium.url.GURL;

import org.json.JSONArray;
import org.json.JSONObject;
import org.json.JSONTokener;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.lang.ref.WeakReference;
import java.net.HttpURLConnection;
import java.net.URL;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.concurrent.Callable;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Native IP-TEST bridge for the dedicated browser fork.
 *
 * <p>The bridge is inert unless the launcher intent includes a serial, hub URL and token. It
 * long-polls the local HUB over adb reverse and executes the first command set directly in
 * Chromium without DevTools, remote-debugging flags or extension page globals.
 */
public final class IptestBridgeClient {
    public static final String EXTRA_SERIAL = "iptest_serial";
    public static final String EXTRA_HUB_URL = "iptest_hub_url";
    public static final String EXTRA_TOKEN = "iptest_token";

    private static final String TAG = "IptestBridgeClient";
    private static final String BRIDGE_VERSION = "native-v1";
    private static final String SWITCH_IN_PROCESS_GPU = "in-process-gpu";
    private static final Object LOCK = new Object();
    private static final long START_RETRY_DELAY_MS = 300;
    private static final long START_RETRY_DEADLINE_MS = 60000;

    private static IptestBridgeClient sClient;
    private static PendingLaunch sPendingLaunch;
    private static boolean sPendingRetryScheduled;

    private WeakReference<ChromeTabbedActivity> mActivity;
    private final Context mAppContext;
    private final String mSerial;
    private final String mHubUrl;
    private final String mToken;
    private final String mPackageName;
    private final List<JSONObject> mBridgeLogs = new ArrayList<>();
    private volatile boolean mStopped;
    private volatile boolean mPreferIsolatedWorldEval;
    private volatile int mAutomationTabId = -1;
    private volatile boolean mRendererResponsive = true;
    private volatile long mLastLoadStoppedAt;
    private volatile long mLastPageLoadFinishedAt;
    private volatile long mLastNavigationFinishedAt;
    private volatile String mLastKnownUrl = "";
    private volatile String mLastNavigationEvent = "";
    private volatile String mLastNavigationError = "";
    private volatile String mLastCrash = "";
    private Tab mObservedTab;
    private final EmptyTabObserver mAutomationTabObserver =
            new EmptyTabObserver() {
                @Override
                public void onContentChanged(Tab tab) {
                    recordTabSnapshot(tab, "content_changed");
                }

                @Override
                public void onLoadStopped(Tab tab, boolean toDifferentDocument) {
                    mLastLoadStoppedAt = System.currentTimeMillis();
                    recordTabSnapshot(tab, "load_stopped");
                }

                @Override
                public void onPageLoadFinished(Tab tab, GURL url) {
                    mLastPageLoadFinishedAt = System.currentTimeMillis();
                    mLastKnownUrl = url == null ? "" : String.valueOf(url);
                    recordTabSnapshot(tab, "page_load_finished");
                }

                @Override
                public void onDidFinishNavigationInPrimaryMainFrame(
                        Tab tab, NavigationHandle navigation) {
                    mLastNavigationFinishedAt = System.currentTimeMillis();
                    mLastNavigationEvent = "primary_main_frame_finished";
                    if (navigation != null) {
                        GURL url = navigation.getUrl();
                        mLastKnownUrl = url == null ? "" : String.valueOf(url);
                        if (navigation.isErrorPage() || navigation.errorCode() != 0) {
                            mLastNavigationError =
                                    "navigation_error:"
                                            + navigation.errorCode()
                                            + ":"
                                            + navigation.errorDescription();
                        } else {
                            mLastNavigationError = "";
                        }
                    }
                    recordTabSnapshot(tab, "navigation_finished");
                }

                @Override
                public void onPageLoadFailed(Tab tab, int errorCode) {
                    mLastNavigationError = "page_load_failed:" + errorCode;
                    recordTabSnapshot(tab, "page_load_failed");
                }

                @Override
                public void onCrash(Tab tab) {
                    mLastCrash = "tab_crash:" + System.currentTimeMillis();
                    mRendererResponsive = false;
                    recordTabSnapshot(tab, "tab_crash");
                }

                @Override
                public void onRendererResponsiveStateChanged(Tab tab, boolean isResponsive) {
                    mRendererResponsive = isResponsive;
                    recordTabSnapshot(tab, isResponsive ? "renderer_responsive" : "renderer_unresponsive");
                }
            };

    private static final class PendingLaunch {
        final WeakReference<ChromeTabbedActivity> activity;
        final String serial;
        final String hubUrl;
        final String token;
        final long createdAt;
        int attempts;

        PendingLaunch(ChromeTabbedActivity activity, String serial, String hubUrl, String token) {
            this.activity = new WeakReference<>(activity);
            this.serial = serial;
            this.hubUrl = hubUrl;
            this.token = token;
            this.createdAt = System.currentTimeMillis();
        }
    }

    private IptestBridgeClient(
            ChromeTabbedActivity activity, String serial, String hubUrl, String token) {
        mActivity = new WeakReference<>(activity);
        mAppContext = activity.getApplicationContext();
        mSerial = serial;
        mHubUrl = trimTrailingSlash(hubUrl);
        mToken = token;
        mPackageName = mAppContext.getPackageName();
    }

    /** Starts or refreshes the singleton bridge when an IP-TEST launcher intent is present. */
    public static boolean maybeStartFromIntent(ChromeTabbedActivity activity, Intent intent) {
        if (activity == null || intent == null) return false;
        String serial = intent.getStringExtra(EXTRA_SERIAL);
        String hubUrl = intent.getStringExtra(EXTRA_HUB_URL);
        String token = intent.getStringExtra(EXTRA_TOKEN);
        if (isBlank(serial) || isBlank(hubUrl) || isBlank(token)) return false;
        ensureIptestCommandLineSwitches();

        synchronized (LOCK) {
            String trimmedSerial = serial.trim();
            String trimmedHubUrl = hubUrl.trim();
            String trimmedToken = token.trim();
            if (!isActivityReadyForBridge(activity)) {
                sPendingLaunch =
                        new PendingLaunch(activity, trimmedSerial, trimmedHubUrl, trimmedToken);
                schedulePendingStartLocked();
                return true;
            }
            startOrRefreshLocked(activity, trimmedSerial, trimmedHubUrl, trimmedToken);
        }
        return true;
    }

    private static void ensureIptestCommandLineSwitches() {
        try {
            CommandLine commandLine = CommandLine.getInstance();
            if (!commandLine.hasSwitch(SWITCH_IN_PROCESS_GPU)) {
                commandLine.appendSwitch(SWITCH_IN_PROCESS_GPU);
            }
        } catch (Throwable t) {
            Log.w(TAG, "Failed to apply IP-TEST command line switches", t);
        }
    }

    private static void startOrRefreshLocked(
            ChromeTabbedActivity activity, String serial, String hubUrl, String token) {
        sPendingLaunch = null;
        if (sClient != null && sClient.matches(serial, hubUrl, token)) {
            sClient.updateActivity(activity);
            sClient.resetAutomationTabBestEffort("activity_refreshed");
            return;
        }
        if (sClient != null) sClient.stop();
        sClient = new IptestBridgeClient(activity, serial, hubUrl, token);
        sClient.start();
    }

    private static void schedulePendingStartLocked() {
        if (sPendingRetryScheduled) return;
        sPendingRetryScheduled = true;
        ThreadUtils.postOnUiThreadDelayed(
                () -> {
                    synchronized (LOCK) {
                        sPendingRetryScheduled = false;
                        PendingLaunch pending = sPendingLaunch;
                        if (pending == null) return;
                        ChromeTabbedActivity activity = pending.activity.get();
                        long ageMs = System.currentTimeMillis() - pending.createdAt;
                        if (activity == null || ageMs > START_RETRY_DEADLINE_MS) {
                            sPendingLaunch = null;
                            Log.w(TAG, "Dropping pending IP-TEST bridge launch; activityReady=%s ageMs=%d",
                                    activity != null, ageMs);
                            return;
                        }
                        if (isActivityReadyForBridge(activity)) {
                            startOrRefreshLocked(
                                    activity, pending.serial, pending.hubUrl, pending.token);
                            return;
                        }
                        pending.attempts++;
                        schedulePendingStartLocked();
                    }
                },
                START_RETRY_DELAY_MS);
    }

    private static boolean isActivityReadyForBridge(ChromeTabbedActivity activity) {
        try {
            return activity != null
                    && activity.didFinishNativeInitialization()
                    && activity.areTabModelsInitialized()
                    && activity.getActivityTab() != null;
        } catch (Throwable ignored) {
            return false;
        }
    }

    private void updateActivity(ChromeTabbedActivity activity) {
        mActivity = new WeakReference<>(activity);
    }

    private boolean matches(String serial, String hubUrl, String token) {
        return mSerial.equals(serial)
                && mHubUrl.equals(trimTrailingSlash(hubUrl))
                && mToken.equals(token);
    }

    private void start() {
        Thread thread = new Thread(this::runLoop, "IPTEST-BrowserBridge");
        thread.setDaemon(true);
        thread.start();
    }

    private void stop() {
        mStopped = true;
    }

    private void runLoop() {
        int failures = 0;
        while (!mStopped) {
            try {
                register();
                failures = 0;
                while (!mStopped) {
                    JSONObject response =
                            postJson(
                                    "/api/iptest-browser/" + encode(mSerial) + "/next-command",
                                    new JSONObject()
                                            .put("token", mToken)
                                            .put("timeoutMs", 25000),
                                    32000);
                    JSONObject command = response.optJSONObject("command");
                    if (command == null) continue;
                    handleCommand(command);
                }
            } catch (Exception e) {
                failures++;
                Log.w(TAG, "Bridge loop failed: %s", e.toString());
                sleep(Math.min(30000, 1000L * failures));
            }
        }
    }

    private void register() throws Exception {
        postJson(
                "/api/iptest-browser/register",
                new JSONObject()
                        .put("serial", mSerial)
                        .put("token", mToken)
                        .put("packageName", mPackageName)
                        .put("browserVersion", "ultimatum-native")
                        .put("userAgent", System.getProperty("http.agent", ""))
                        .put("bridgeVersion", BRIDGE_VERSION),
                10000);
    }

    private void handleCommand(JSONObject command) {
        String id = command.optString("id", "");
        String name = command.optString("command", "");
        JSONObject payload = command.optJSONObject("payload");
        if (payload == null) payload = new JSONObject();
        try {
            Log.i(TAG, "Command start: %s id=%s state=%s", name, id, readActivityState());
            Object result = executeCommandWithWatchdog(name, payload);
            Log.i(TAG, "Command success: %s id=%s", name, id);
            submitResult(id, true, result, null);
        } catch (Exception e) {
            Log.w(TAG, "Command failed: %s id=%s error=%s state=%s", name, id, e.toString(), readActivityState());
            submitResult(id, false, null, e.toString());
        }
    }

    private Object executeCommandWithWatchdog(String name, JSONObject payload) throws Exception {
        long timeoutMs = commandTimeoutMs(name, payload);
        FutureTask<Object> task = new FutureTask<>(() -> executeCommand(name, payload));
        Thread thread = new Thread(task, "IPTEST-BrowserCommand-" + name);
        thread.setDaemon(true);
        thread.start();
        try {
            return task.get(timeoutMs, TimeUnit.MILLISECONDS);
        } catch (TimeoutException e) {
            task.cancel(true);
            mRendererResponsive = false;
            mLastNavigationError = "command_timeout:" + name;
            resetAutomationTabBestEffort("command_timeout:" + name);
            throw new IllegalStateException(
                    "native_command_timeout:" + name + " after " + timeoutMs + "ms " + readActivityState());
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof Exception) throw (Exception) cause;
            throw new IllegalStateException(cause == null ? e.toString() : cause.toString(), cause);
        }
    }

    private long commandTimeoutMs(String name, JSONObject payload) {
        long requested = payload.optLong("timeoutMs", 0);
        if (requested > 0) return clamp(requested + 5000, 5000, 60000);
        switch (name) {
            case "cleanup":
                return 40000;
            case "navigate":
                return 45000;
            case "evaluate":
            case "evaluatePage":
            case "evaluateInternal":
                return 20000;
            case "getNativeState":
            case "waitForNativeReady":
            case "resetAutomationTab":
            case "getBrowserInfo":
                return 10000;
            default:
                return 30000;
        }
    }

    private Object executeCommand(String name, JSONObject payload) throws Exception {
        addBridgeLog("debug", "command:start", name);
        switch (name) {
            case "navigate":
                return navigate(payload);
            case "evaluate":
            case "evaluatePage":
                return evaluatePage(
                        payload.optString("expression", ""),
                        payload.optLong("timeoutMs", 15000));
            case "evaluateInternal":
                return evaluateInternal(
                        payload.optString("expression", ""),
                        payload.optLong("timeoutMs", 8000));
            case "getNativeState":
                return getNativeState();
            case "waitForNativeReady":
                return waitForNativeReady(payload.optLong("timeoutMs", 15000));
            case "resetAutomationTab":
                return resetAutomationTab(payload.optString("reason", "command"));
            case "getPageSnapshot":
                return getPageSnapshot();
            case "clickSelector":
                return clickSelector(payload.optString("selector", ""));
            case "fillSelector":
                return fillSelector(
                        payload.optString("selector", ""),
                        payload.optString("value", ""));
            case "cleanup":
                return cleanup();
            case "getLogs":
                return getLogs();
            case "reload":
                return runWithTab(
                        "about:blank",
                        tab -> {
                            tab.reload();
                            return new JSONObject().put("ok", true);
                        });
            case "goForward":
                return runWithTab(
                        "about:blank",
                        tab -> {
                            tab.goForward();
                            return new JSONObject().put("ok", true);
                        });
            case "handleDialog":
                return false;
            case "getBrowserInfo":
                return getBrowserInfo();
            default:
                throw new IllegalArgumentException("native_command_not_implemented:" + name);
        }
    }

    private Object navigate(JSONObject payload) throws Exception {
        String url = payload.optString("url", "");
        if (isBlank(url)) throw new IllegalArgumentException("navigate url is required");
        String waitUntil =
                payload.optString("waitUntil", "load")
                        .trim()
                        .toLowerCase(Locale.US);
        long timeoutMs = clamp(payload.optLong("timeoutMs", 30000), 1000, 60000);
        long startedAt = System.currentTimeMillis();
        waitForNativeReady(Math.min(15000, timeoutMs));

        CountDownLatch latch = new CountDownLatch(1);
        AtomicReference<JSONObject> result = new AtomicReference<>();
        AtomicReference<String> error = new AtomicReference<>();
        AtomicReference<Tab> observedTab = new AtomicReference<>();
        AtomicBoolean done = new AtomicBoolean(false);

        EmptyTabObserver observer =
                new EmptyTabObserver() {
                    private void finish(Tab tab, String event, GURL eventUrl) {
                        if (!done.compareAndSet(false, true)) return;
                        try {
                            tab.removeObserver(this);
                        } catch (Throwable ignored) {
                        }
                        try {
                            String finalUrl =
                                    eventUrl == null ? safeTabUrl(tab) : String.valueOf(eventUrl);
                            result.set(
                                    new JSONObject()
                                            .put("ok", true)
                                            .put("url", url)
                                            .put("finalUrl", finalUrl)
                                            .put("event", event)
                                            .put("waitUntil", waitUntil)
                                            .put("durationMs", System.currentTimeMillis() - startedAt)
                                            .put("nativeState", collectNativeStateOnUi()));
                        } catch (Exception jsonError) {
                            error.set(jsonError.toString());
                        }
                        latch.countDown();
                    }

                    private void fail(Tab tab, String reason) {
                        if (!done.compareAndSet(false, true)) return;
                        try {
                            tab.removeObserver(this);
                        } catch (Throwable ignored) {
                        }
                        error.set(reason + " " + describeTabState(tab));
                        latch.countDown();
                    }

                    @Override
                    public void onDidFinishNavigationInPrimaryMainFrame(
                            Tab tab, NavigationHandle navigation) {
                        if (navigation != null
                                && (navigation.isErrorPage() || navigation.errorCode() != 0)) {
                            fail(
                                    tab,
                                    "navigation_error:"
                                            + navigation.errorCode()
                                            + ":"
                                            + navigation.errorDescription());
                            return;
                        }
                        if ("commit".equals(waitUntil) || "domcontentloaded".equals(waitUntil)) {
                            finish(tab, "primary_main_frame_finished", navigation == null ? null : navigation.getUrl());
                        }
                    }

                    @Override
                    public void onLoadStopped(Tab tab, boolean toDifferentDocument) {
                        if ("loadstopped".equals(waitUntil) || "load".equals(waitUntil)) {
                            finish(tab, "load_stopped", null);
                        }
                    }

                    @Override
                    public void onPageLoadFinished(Tab tab, GURL eventUrl) {
                        finish(tab, "page_load_finished", eventUrl);
                    }

                    @Override
                    public void onPageLoadFailed(Tab tab, int errorCode) {
                        fail(tab, "page_load_failed:" + errorCode);
                    }

                    @Override
                    public void onCrash(Tab tab) {
                        fail(tab, "tab_crash");
                    }
                };

        Runnable startNavigation =
                () -> {
                    try {
                        ChromeTabbedActivity activity = mActivity.get();
                        Tab tab = getOrCreateActivityTab(activity, url);
                        if (tab == null) {
                            error.set("No current tab " + describeActivityState(activity));
                            latch.countDown();
                            return;
                        }
                        observedTab.set(tab);
                        tab.addObserver(observer);
                        tab.loadUrl(new LoadUrlParams(url));
                    } catch (Throwable t) {
                        error.set(t.toString());
                        latch.countDown();
                    }
                };
        ThreadUtils.runOnUiThreadBlocking(startNavigation);

        if (!latch.await(timeoutMs, TimeUnit.MILLISECONDS)) {
            Tab tab = observedTab.get();
            if (tab != null) {
                ThreadUtils.postOnUiThread(() -> {
                    try {
                        tab.removeObserver(observer);
                    } catch (Throwable ignored) {
                    }
                });
            }
            JSONObject syntheticResult =
                    synthesizeNavigationResultIfUrlCommitted(tab, url, waitUntil, startedAt);
            if (syntheticResult != null) return syntheticResult;
            throw new IllegalStateException(
                    "native_navigation_timeout:"
                            + url
                            + " waitUntil="
                            + waitUntil
                            + " "
                            + readActivityState());
        }
        if (!isBlank(error.get())) throw new IllegalStateException(error.get());
        return result.get();
    }

    private JSONObject synthesizeNavigationResultIfUrlCommitted(
            Tab tab, String expectedUrl, String waitUntil, long startedAt) {
        if (tab == null) return null;
        try {
            Callable<JSONObject> fallbackCheck =
                    () -> {
                        ChromeTabbedActivity activity = mActivity.get();
                        activateAutomationTab(activity, tab);
                        if (!isUsableTab(tab) || !isTabReadyForJs(tab)) return null;
                        String finalUrl = safeTabUrl(tab);
                        if (!urlMatches(finalUrl, expectedUrl)
                                && !urlMatches(mLastKnownUrl, expectedUrl)) {
                            return null;
                        }
                        boolean stillLoading = false;
                        try {
                            stillLoading = tab.isLoading();
                        } catch (Throwable ignored) {
                        }
                        return new JSONObject()
                                .put("ok", true)
                                .put("url", expectedUrl)
                                .put("finalUrl", finalUrl)
                                .put("event", "url_committed_fallback")
                                .put("stillLoading", stillLoading)
                                .put("waitUntil", waitUntil)
                                .put("durationMs", System.currentTimeMillis() - startedAt)
                                .put("nativeState", collectNativeStateOnUi());
                    };
            return ThreadUtils.runOnUiThreadBlocking(fallbackCheck);
        } catch (Throwable t) {
            addBridgeLog("warn", "navigate:fallback_failed", t.toString());
            return null;
        }
    }

    private Object cleanup() throws Exception {
        long startedAt = System.currentTimeMillis();
        JSONObject profileResult = clearNativeProfileData();
        JSONObject pageResult = runPageLevelCleanupBestEffort();
        boolean nativeOk = profileResult.optBoolean("ok", false);
        boolean pageOk = pageResult.optBoolean("ok", false);
        boolean pageBlocking = pageResult.optBoolean("blocking", false);
        JSONObject resetResult = resetAutomationTabBestEffort("cleanup");
        JSONObject result =
                new JSONObject()
                        .put("ok", nativeOk)
                        .put("mode", "native_profile_plus_page")
                        .put("nativeProfileCleared", nativeOk)
                        .put("pageLevelCleared", pageOk)
                        .put("pageLevelBlocking", pageBlocking)
                        .put("profile", profileResult)
                        .put("page", pageResult)
                        .put("reset", resetResult)
                        .put("durationMs", System.currentTimeMillis() - startedAt);
        addBridgeLog(result.optBoolean("ok", false) ? "debug" : "warn", "cleanup", result.toString());
        return result;
    }

    private JSONObject clearNativeProfileData() throws Exception {
        CountDownLatch latch = new CountDownLatch(1);
        AtomicReference<String> error = new AtomicReference<>();
        ThreadUtils.postOnUiThread(
                () -> {
                    try {
                        ChromeTabbedActivity activity = mActivity.get();
                        Tab tab = getOrCreateActivityTab(activity, "about:blank");
                        if (tab == null) {
                            error.set("No current tab/profile " + describeActivityState(activity));
                            latch.countDown();
                            return;
                        }
                        Profile profile = tab.getProfile().getOriginalProfile();
                        BrowsingDataBridge.getForProfile(profile)
                                .clearBrowsingData(
                                        () -> latch.countDown(),
                                        new int[] {
                                            BrowsingDataType.HISTORY,
                                            BrowsingDataType.SITE_DATA,
                                            BrowsingDataType.CACHE,
                                            BrowsingDataType.FORM_DATA,
                                            BrowsingDataType.SITE_SETTINGS
                                        },
                                        TimePeriod.ALL_TIME);
                    } catch (Throwable t) {
                        error.set(t.toString());
                        latch.countDown();
                    }
                });
        boolean completed = latch.await(25000, TimeUnit.MILLISECONDS);
        if (!completed) {
            return new JSONObject().put("ok", false).put("reason", "native_profile_cleanup_timeout");
        }
        if (!isBlank(error.get())) {
            return new JSONObject().put("ok", false).put("reason", error.get());
        }
        return new JSONObject().put("ok", true).put("dataTypes", "history,site_data,cache,form_data,site_settings");
    }

    private JSONObject runPageLevelCleanupBestEffort() {
        try {
            return new JSONObject()
                    .put("ok", false)
                    .put("blocking", false)
                    .put("mode", "page_level_best_effort")
                    .put("skipped", true)
                    .put("reason", "native_profile_cleanup_is_blocking_gate");
        } catch (Exception e) {
            addBridgeLog("warn", "cleanup:page_level_skipped", e.toString());
            try {
                return new JSONObject()
                        .put("ok", false)
                        .put("blocking", false)
                        .put("mode", "page_level_best_effort")
                        .put("skipped", true)
                        .put("reason", e.toString());
            } catch (Exception ignored) {
                return new JSONObject();
            }
        }
    }

    private void resetActiveTabToBlank() {
        try {
            ThreadUtils.runOnUiThreadBlocking(
                    () -> {
                        try {
                            ChromeTabbedActivity activity = mActivity.get();
                            Tab tab = getOrCreateActivityTab(activity, "about:blank");
                            if (tab != null) {
                                tab.loadUrl(new LoadUrlParams("about:blank"));
                            }
                        } catch (Throwable t) {
                            addBridgeLog("warn", "tab:reset_blank_failed", t.toString());
                        }
                    });
            sleep(750);
        } catch (Throwable t) {
            addBridgeLog("warn", "tab:reset_blank_failed", t.toString());
        }
    }

    private Object getPageSnapshot() throws Exception {
        JSONObject snapshot = new JSONObject().put("nativeState", getNativeState());
        try {
            Object page =
                    evaluateInternal(
                "(function(){return {url:location.href,title:document.title,readyState:document.readyState,webdriver:navigator.webdriver,userAgent:navigator.userAgent,cookie:document.cookie,localStorageKeys:Object.keys(localStorage||{}),sessionStorageKeys:Object.keys(sessionStorage||{}),viewport:{width:innerWidth,height:innerHeight,dpr:devicePixelRatio||1},bodyTextLength:document.body&&document.body.innerText?document.body.innerText.trim().length:0};})()",
                            5000);
            snapshot.put("page", page == null ? JSONObject.NULL : page);
        } catch (Exception e) {
            snapshot.put("pageError", e.toString());
        }
        return snapshot;
    }

    private Object clickSelector(String selector) throws Exception {
        if (isBlank(selector)) throw new IllegalArgumentException("selector is required");
        return evaluateInternal(
                "(function(){var el=document.querySelector(" + JSONObject.quote(selector) + ");"
                        + "if(!el)return {found:false};"
                        + "el.scrollIntoView({block:'center',inline:'center'});"
                        + "el.click();"
                        + "return {found:true};})()",
                8000);
    }

    private Object fillSelector(String selector, String value) throws Exception {
        if (isBlank(selector)) throw new IllegalArgumentException("selector is required");
        return evaluateInternal(
                "(function(){var el=document.querySelector(" + JSONObject.quote(selector) + ");"
                        + "if(!el)return {found:false};"
                        + "el.focus();"
                        + "if('value' in el){el.value=" + JSONObject.quote(value) + ";}else{el.textContent=" + JSONObject.quote(value) + ";}"
                        + "el.dispatchEvent(new Event('input',{bubbles:true}));"
                        + "el.dispatchEvent(new Event('change',{bubbles:true}));"
                        + "return {found:true};})()",
                8000);
    }

    private Object getLogs() {
        JSONArray logs = new JSONArray();
        synchronized (mBridgeLogs) {
            for (JSONObject entry : mBridgeLogs) {
                logs.put(entry);
            }
        }
        return logs;
    }

    private Object getBrowserInfo() throws Exception {
        JSONObject page = new JSONObject();
        try {
            Object snapshot = getPageSnapshot();
            if (snapshot instanceof JSONObject) page = (JSONObject) snapshot;
        } catch (Exception e) {
            page.put("error", e.toString());
        }
        return new JSONObject()
                .put("packageName", mPackageName)
                .put("bridgeVersion", BRIDGE_VERSION)
                .put("userAgent", System.getProperty("http.agent", ""))
                .put("nativeState", getNativeState())
                .put("page", page);
    }

    private JSONObject getNativeState() throws Exception {
        if (ThreadUtils.runningOnUiThread()) {
            return collectNativeStateOnUi();
        }
        return ThreadUtils.runOnUiThreadBlocking(this::collectNativeStateOnUi);
    }

    private JSONObject waitForNativeReady(long timeoutMs) throws Exception {
        long deadline = System.currentTimeMillis() + Math.max(1000, timeoutMs);
        JSONObject lastState = new JSONObject();
        boolean triedReset = false;
        while (System.currentTimeMillis() < deadline) {
            lastState = getNativeState();
            boolean nativeReady = lastState.optBoolean("nativeReady", false);
            boolean tabModelsReady = lastState.optBoolean("tabModelsReady", false);
            boolean readyForCommands = lastState.optBoolean("readyForCommands", false);
            if (readyForCommands) {
                lastState.put("ok", true);
                return lastState;
            }
            if (!triedReset && nativeReady && tabModelsReady) {
                triedReset = true;
                resetAutomationTabBestEffort("wait_for_native_ready");
            }
            sleep(250);
        }
        throw new IllegalStateException("native_ready_timeout " + lastState);
    }

    private JSONObject resetAutomationTab(String reason) throws Exception {
        JSONObject result =
                ThreadUtils.runOnUiThreadBlocking(
                        () -> {
                            ChromeTabbedActivity activity = mActivity.get();
                            JSONObject output = new JSONObject();
                            try {
                                Tab tab = getOrCreateActivityTab(activity, "about:blank", true);
                                if (tab == null) {
                                    return output
                                            .put("ok", false)
                                            .put("reason", "no_tab")
                                            .put("nativeState", collectNativeStateOnUi());
                                }
                                tab.loadUrl(new LoadUrlParams("about:blank"));
                                return output
                                        .put("ok", true)
                                        .put("reason", reason)
                                        .put("automationTabId", mAutomationTabId)
                                        .put("nativeState", collectNativeStateOnUi());
                            } catch (Exception e) {
                                return output.put("ok", false).put("reason", e.toString());
                            }
                        });
        sleep(500);
        return result;
    }

    private JSONObject resetAutomationTabBestEffort(String reason) {
        try {
            return resetAutomationTab(reason);
        } catch (Throwable t) {
            addBridgeLog("warn", "tab:reset_automation_failed", t.toString());
            try {
                return new JSONObject().put("ok", false).put("reason", t.toString());
            } catch (Exception ignored) {
                return new JSONObject();
            }
        }
    }

    private Object evaluatePage(String expression, long timeoutMs) throws Exception {
        if (isBlank(expression)) throw new IllegalArgumentException("evaluate expression is required");
        waitForWebContents("about:blank", Math.min(Math.max(5000, timeoutMs), 15000));
        long primaryTimeoutMs = Math.min(Math.max(2500, timeoutMs / 3), 5000);
        if (mPreferIsolatedWorldEval) {
            try {
                return evaluateWithMainFrame(expression, timeoutMs);
            } catch (Exception isolatedError) {
                mPreferIsolatedWorldEval = false;
                addBridgeLog("warn", "evaluate:fallback_webcontents", isolatedError.toString());
                return evaluateWithWebContents(expression, primaryTimeoutMs);
            }
        }
        try {
            Object result = evaluateWithWebContents(expression, primaryTimeoutMs);
            mPreferIsolatedWorldEval = false;
            return result;
        } catch (Exception primaryError) {
            addBridgeLog("warn", "evaluate:fallback_isolated_world", primaryError.toString());
            try {
                Object result =
                        evaluateWithMainFrame(expression, Math.max(1000, timeoutMs - primaryTimeoutMs));
                mPreferIsolatedWorldEval = true;
                return result;
            } catch (Exception fallbackError) {
                throw new IllegalStateException(
                        "evaluate failed; webContents="
                                + primaryError
                                + "; mainFrame="
                                + fallbackError,
                        fallbackError);
            }
        }
    }

    private Object evaluateInternal(String expression, long timeoutMs) throws Exception {
        if (isBlank(expression)) throw new IllegalArgumentException("evaluate expression is required");
        waitForWebContents("about:blank", Math.min(Math.max(2500, timeoutMs), 10000));
        try {
            Object result = evaluateWithMainFrame(expression, timeoutMs);
            mPreferIsolatedWorldEval = true;
            return result;
        } catch (Exception isolatedError) {
            addBridgeLog("warn", "evaluate_internal:fallback_webcontents", isolatedError.toString());
            return evaluateWithWebContents(expression, Math.min(Math.max(1000, timeoutMs / 2), 5000));
        }
    }

    private Object evaluateWithWebContents(String expression, long timeoutMs) throws Exception {
        CountDownLatch latch = new CountDownLatch(1);
        AtomicReference<String> rawResult = new AtomicReference<>();
        AtomicReference<String> error = new AtomicReference<>();

        ThreadUtils.postOnUiThread(
                () -> {
                    try {
                        ChromeTabbedActivity activity = mActivity.get();
                        Tab tab = getOrCreateActivityTab(activity, "about:blank");
                        WebContents webContents = tab == null ? null : tab.getWebContents();
                        if (webContents == null) {
                            error.set("No current WebContents " + describeActivityState(activity));
                            latch.countDown();
                            return;
                        }
                        webContents.evaluateJavaScript(
                                expression,
                                jsonResult -> {
                                    rawResult.set(jsonResult);
                                    latch.countDown();
                                });
                    } catch (Throwable t) {
                        error.set(t.toString());
                        latch.countDown();
                    }
                });

        if (!latch.await(Math.max(1000, timeoutMs), TimeUnit.MILLISECONDS)) {
            throw new IllegalStateException("evaluate timeout " + readActivityState());
        }
        if (!isBlank(error.get())) throw new IllegalStateException(error.get());
        return parseJsonResult(rawResult.get());
    }

    private Object evaluateWithMainFrame(String expression, long timeoutMs) throws Exception {
        CountDownLatch latch = new CountDownLatch(1);
        AtomicReference<String> rawResult = new AtomicReference<>();
        AtomicReference<String> error = new AtomicReference<>();

        ThreadUtils.postOnUiThread(
                () -> {
                    try {
                        ChromeTabbedActivity activity = mActivity.get();
                        Tab tab = getOrCreateActivityTab(activity, "about:blank");
                        WebContents webContents = tab == null ? null : tab.getWebContents();
                        RenderFrameHost mainFrame =
                                webContents == null ? null : webContents.getMainFrame();
                        if (mainFrame == null || !mainFrame.isRenderFrameLive()) {
                            error.set("No live main frame " + describeActivityState(activity));
                            latch.countDown();
                            return;
                        }
                        mainFrame.executeJavaScriptInIsolatedWorld(
                                expression,
                                1,
                                jsonResult -> {
                                    rawResult.set(jsonResult);
                                    latch.countDown();
                                });
                    } catch (Throwable t) {
                        error.set(t.toString());
                        latch.countDown();
                    }
                });

        if (!latch.await(Math.max(1000, timeoutMs), TimeUnit.MILLISECONDS)) {
            throw new IllegalStateException("main frame evaluate timeout " + readActivityState());
        }
        if (!isBlank(error.get())) throw new IllegalStateException(error.get());
        return parseJsonResult(rawResult.get());
    }

    private void waitForWebContents(String fallbackUrl, long timeoutMs) throws Exception {
        long deadline = System.currentTimeMillis() + Math.max(1000, timeoutMs);
        String lastState = "";
        while (System.currentTimeMillis() < deadline) {
            AtomicReference<String> state = new AtomicReference<>("");
            Boolean ready =
                    ThreadUtils.runOnUiThreadBlocking(
                            () -> {
                                ChromeTabbedActivity activity = mActivity.get();
                                state.set(describeActivityState(activity));
                                Tab tab = getOrCreateActivityTab(activity, fallbackUrl);
                                return isTabReadyForJs(tab);
                            });
            lastState = state.get();
            if (Boolean.TRUE.equals(ready)) return;
            sleep(250);
        }
        throw new IllegalStateException("No JS-ready WebContents after wait " + lastState);
    }

    private Tab getOrCreateActivityTab(ChromeTabbedActivity activity, String fallbackUrl) {
        return getOrCreateActivityTab(activity, fallbackUrl, false);
    }

    private Tab getOrCreateActivityTab(
            ChromeTabbedActivity activity, String fallbackUrl, boolean forceNew) {
        if (activity == null) return null;
        if (!activity.didFinishNativeInitialization() || !activity.areTabModelsInitialized()) {
            return null;
        }
        Tab tab = forceNew ? null : getAutomationTab(activity);
        if (isUsableTab(tab)) {
            attachAutomationObserver(tab);
            activateAutomationTab(activity, tab);
            return tab;
        }
        tab = forceNew ? null : activity.getActivityTab();
        if (isUsableTab(tab)) {
            attachAutomationObserver(tab);
            activateAutomationTab(activity, tab);
            return tab;
        }
        try {
            String url = isBlank(fallbackUrl) ? "about:blank" : fallbackUrl;
            activity.getTabModelSelector().selectModel(false);
            tab =
                    activity.getTabCreator(false)
                            .createNewTab(
                                    new LoadUrlParams(url),
                                    TabLaunchType.FROM_CHROME_UI,
                                    /* parent= */ null);
            if (tab != null) {
                attachAutomationObserver(tab);
                activateAutomationTab(activity, tab);
                addBridgeLog("debug", "tab:create", url);
                return tab;
            }
        } catch (Throwable t) {
            addBridgeLog("warn", "tab:create_failed", t.toString());
        }
        tab = activity.getActivityTab();
        if (isUsableTab(tab)) attachAutomationObserver(tab);
        return tab;
    }

    private Tab getAutomationTab(ChromeTabbedActivity activity) {
        if (activity == null || mAutomationTabId < 0) return null;
        try {
            TabModel model = activity.getTabModelSelector().getModel(false);
            int index = TabModelUtils.getTabIndexById(model, mAutomationTabId);
            return index >= 0 ? model.getTabAt(index) : null;
        } catch (Throwable ignored) {
            return null;
        }
    }

    private boolean activateAutomationTab(ChromeTabbedActivity activity, Tab tab) {
        if (activity == null || tab == null) return false;
        try {
            activity.getTabModelSelector().selectModel(false);
            TabModel model = activity.getTabModelSelector().getModel(false);
            int index = TabModelUtils.getTabIndexById(model, tab.getId());
            if (index < 0) return false;
            if (model.index() != index) {
                model.setIndex(index, TabSelectionType.FROM_USER);
            }
            return activity.getActivityTab() != null && activity.getActivityTab().getId() == tab.getId();
        } catch (Throwable t) {
            addBridgeLog("warn", "tab:activate_failed", t.toString());
            return false;
        }
    }

    private void attachAutomationObserver(Tab tab) {
        if (tab == null) return;
        try {
            if (mObservedTab == tab) {
                mAutomationTabId = tab.getId();
                recordTabSnapshot(tab, "tab_observed");
                return;
            }
            if (mObservedTab != null) {
                try {
                    mObservedTab.removeObserver(mAutomationTabObserver);
                } catch (Throwable ignored) {
                }
            }
            mObservedTab = tab;
            mAutomationTabId = tab.getId();
            tab.addObserver(mAutomationTabObserver);
            recordTabSnapshot(tab, "tab_observed");
        } catch (Throwable t) {
            addBridgeLog("warn", "tab:observe_failed", t.toString());
        }
    }

    private void recordTabSnapshot(Tab tab, String event) {
        if (tab == null) return;
        try {
            mLastKnownUrl = safeTabUrl(tab);
            mLastNavigationEvent = event;
        } catch (Throwable ignored) {
        }
    }

    private JSONObject collectNativeStateOnUi() throws Exception {
        ChromeTabbedActivity activity = mActivity.get();
        boolean nativeReady = false;
        boolean tabModelsReady = false;
        int tabCount = -1;
        int activityTabId = -1;
        Tab tab = null;
        if (activity != null) {
            try {
                nativeReady = activity.didFinishNativeInitialization();
            } catch (Throwable ignored) {
            }
            try {
                tabModelsReady = activity.areTabModelsInitialized();
            } catch (Throwable ignored) {
            }
            try {
                if (tabModelsReady) {
                    TabModel model = activity.getTabModelSelector().getModel(false);
                    tabCount = model.getCount();
                    Tab activityTab = activity.getActivityTab();
                    activityTabId = activityTab == null ? -1 : activityTab.getId();
                }
            } catch (Throwable ignored) {
            }
            tab = getAutomationTab(activity);
            if (tab == null) tab = activity.getActivityTab();
        }
        boolean tabInitialized = false;
        boolean tabDestroyed = false;
        boolean tabClosing = false;
        boolean hasWebContents = false;
        boolean hasMainFrame = false;
        boolean mainFrameLive = false;
        String url = "";
        int tabId = -1;
        if (tab != null) {
            tabId = safeTabId(tab);
            url = safeTabUrl(tab);
            try {
                tabInitialized = tab.isInitialized();
            } catch (Throwable ignored) {
            }
            try {
                tabDestroyed = tab.isDestroyed();
            } catch (Throwable ignored) {
            }
            try {
                tabClosing = tab.isClosing();
            } catch (Throwable ignored) {
            }
            try {
                WebContents webContents = tab.getWebContents();
                hasWebContents = webContents != null;
                RenderFrameHost mainFrame = webContents == null ? null : webContents.getMainFrame();
                hasMainFrame = mainFrame != null;
                mainFrameLive = mainFrame != null && mainFrame.isRenderFrameLive();
            } catch (Throwable ignored) {
            }
        }
        boolean readyForCommands =
                nativeReady
                        && tabModelsReady
                        && tab != null
                        && tabInitialized
                        && !tabDestroyed
                        && !tabClosing
                        && activityTabId == tabId
                        && hasWebContents
                        && hasMainFrame
                        && mainFrameLive;
        return new JSONObject()
                .put("nativeReady", nativeReady)
                .put("tabModelsReady", tabModelsReady)
                .put("tabCount", tabCount)
                .put("activityTabId", activityTabId)
                .put("automationTabId", mAutomationTabId)
                .put("tabId", tabId)
                .put("url", url)
                .put("lastKnownUrl", mLastKnownUrl)
                .put("tabInitialized", tabInitialized)
                .put("tabDestroyed", tabDestroyed)
                .put("tabClosing", tabClosing)
                .put("hasWebContents", hasWebContents)
                .put("hasMainFrame", hasMainFrame)
                .put("mainFrameLive", mainFrameLive)
                .put("rendererResponsive", mRendererResponsive)
                .put("lastLoadStopped", mLastLoadStoppedAt)
                .put("lastPageLoadFinished", mLastPageLoadFinishedAt)
                .put("lastNavigationFinished", mLastNavigationFinishedAt)
                .put("lastNavigationEvent", mLastNavigationEvent)
                .put("lastNavigationError", mLastNavigationError)
                .put("lastCrash", mLastCrash)
                .put("readyForCommands", readyForCommands);
    }

    private String describeActivityState(ChromeTabbedActivity activity) {
        if (activity == null) return "(activity=null)";
        boolean nativeReady = false;
        boolean tabModelsReady = false;
        int tabCount = -1;
        String tabState = "(tab=unknown)";
        try {
            nativeReady = activity.didFinishNativeInitialization();
        } catch (Throwable ignored) {
        }
        try {
            tabModelsReady = activity.areTabModelsInitialized();
        } catch (Throwable ignored) {
        }
        try {
            if (tabModelsReady) tabCount = activity.getCurrentTabModel().getCount();
        } catch (Throwable ignored) {
        }
        try {
            tabState = describeTabState(activity.getActivityTab());
        } catch (Throwable ignored) {
        }
        return "(nativeReady="
                + nativeReady
                + ", tabModelsReady="
                + tabModelsReady
                + ", tabCount="
                + tabCount
                + ", "
                + tabState
                + ")";
    }

    private String readActivityState() {
        try {
            if (ThreadUtils.runningOnUiThread()) {
                return describeActivityState(mActivity.get());
            }
            return ThreadUtils.runOnUiThreadBlocking(() -> describeActivityState(mActivity.get()));
        } catch (Throwable t) {
            return "(state_error=" + t + ")";
        }
    }

    private boolean isTabReadyForJs(Tab tab) {
        if (tab == null || !tab.isInitialized() || tab.isDestroyed() || tab.isClosing()) {
            return false;
        }
        WebContents webContents = tab.getWebContents();
        RenderFrameHost mainFrame = webContents == null ? null : webContents.getMainFrame();
        return webContents != null && mainFrame != null && mainFrame.isRenderFrameLive();
    }

    private boolean isUsableTab(Tab tab) {
        try {
            return tab != null && tab.isInitialized() && !tab.isDestroyed() && !tab.isClosing();
        } catch (Throwable ignored) {
            return false;
        }
    }

    private int safeTabId(Tab tab) {
        try {
            return tab == null ? -1 : tab.getId();
        } catch (Throwable ignored) {
            return -1;
        }
    }

    private String safeTabUrl(Tab tab) {
        try {
            return tab == null ? "" : String.valueOf(tab.getUrl());
        } catch (Throwable ignored) {
            return "";
        }
    }

    private boolean urlMatches(String observed, String expected) {
        if (isBlank(observed) || isBlank(expected)) return false;
        return observed.equals(expected)
                || observed.contains(expected)
                || observed.equals("GURL(" + expected + ")");
    }

    private String describeTabState(Tab tab) {
        if (tab == null) return "tab=null";
        boolean initialized = false;
        boolean destroyed = false;
        boolean closing = false;
        String url = "";
        boolean hasWebContents = false;
        boolean hasMainFrame = false;
        boolean mainFrameLive = false;
        try {
            initialized = tab.isInitialized();
        } catch (Throwable ignored) {
        }
        try {
            destroyed = tab.isDestroyed();
        } catch (Throwable ignored) {
        }
        try {
            closing = tab.isClosing();
        } catch (Throwable ignored) {
        }
        try {
            url = String.valueOf(tab.getUrl());
        } catch (Throwable ignored) {
        }
        try {
            WebContents webContents = tab.getWebContents();
            hasWebContents = webContents != null;
            RenderFrameHost mainFrame = webContents == null ? null : webContents.getMainFrame();
            hasMainFrame = mainFrame != null;
            mainFrameLive = mainFrame != null && mainFrame.isRenderFrameLive();
        } catch (Throwable ignored) {
        }
        return "tabInitialized="
                + initialized
                + ", tabDestroyed="
                + destroyed
                + ", tabClosing="
                + closing
                + ", hasWebContents="
                + hasWebContents
                + ", hasMainFrame="
                + hasMainFrame
                + ", mainFrameLive="
                + mainFrameLive
                + ", url="
                + url;
    }

    private <T> T runWithTab(String fallbackUrl, TabCallable<T> callable) throws Exception {
        waitForNativeReady(15000);
        AtomicReference<Exception> error = new AtomicReference<>();
        T result =
                ThreadUtils.runOnUiThreadBlocking(
                        () -> {
                            try {
                                ChromeTabbedActivity activity = mActivity.get();
                                Tab tab = getOrCreateActivityTab(activity, fallbackUrl);
                                if (tab == null) {
                                    throw new IllegalStateException(
                                            "No current tab " + describeActivityState(activity));
                                }
                                return callable.call(tab);
                            } catch (Exception e) {
                                error.set(e);
                                return null;
                            }
                        });
        if (error.get() != null) throw error.get();
        return result;
    }

    private void submitResult(String id, boolean ok, Object result, String error) {
        if (isBlank(id)) return;
        try {
            JSONObject body = new JSONObject().put("id", id).put("token", mToken).put("ok", ok);
            if (ok) {
                body.put("result", result == null ? JSONObject.NULL : result);
            } else {
                body.put("error", error == null ? "unknown error" : error);
            }
            postJson("/api/iptest-browser/" + encode(mSerial) + "/result", body, 10000);
        } catch (Exception e) {
            Log.w(TAG, "Failed to submit command result: %s", e.toString());
        }
    }

    private void addBridgeLog(String level, String message, String details) {
        try {
            JSONObject entry =
                    new JSONObject()
                            .put("level", level)
                            .put("message", message)
                            .put("details", details == null ? JSONObject.NULL : details)
                            .put("timestamp", System.currentTimeMillis())
                            .put("source", "iptest-native");
            synchronized (mBridgeLogs) {
                mBridgeLogs.add(entry);
                if (mBridgeLogs.size() > 300) {
                    mBridgeLogs.remove(0);
                }
            }
        } catch (Exception ignored) {
        }
    }

    private JSONObject postJson(String path, JSONObject body, int readTimeoutMs) throws Exception {
        URL url = new URL(mHubUrl + path);
        HttpURLConnection connection = (HttpURLConnection) url.openConnection();
        connection.setRequestMethod("POST");
        connection.setConnectTimeout(5000);
        connection.setReadTimeout(readTimeoutMs);
        connection.setDoOutput(true);
        connection.setRequestProperty("Content-Type", "application/json; charset=utf-8");
        connection.setRequestProperty("Accept", "application/json");
        connection.setRequestProperty("X-IPTEST-Browser-Token", mToken);
        byte[] bytes = body.toString().getBytes(StandardCharsets.UTF_8);
        connection.setFixedLengthStreamingMode(bytes.length);
        try (OutputStream output = connection.getOutputStream()) {
            output.write(bytes);
        }
        int code = connection.getResponseCode();
        InputStream stream = code >= 400 ? connection.getErrorStream() : connection.getInputStream();
        String response = readAll(stream);
        if (code >= 400) {
            throw new IllegalStateException("HTTP " + code + " " + response);
        }
        return isBlank(response) ? new JSONObject() : new JSONObject(response);
    }

    private static Object parseJsonResult(String raw) throws Exception {
        if (raw == null || "undefined".equals(raw)) return JSONObject.NULL;
        return new JSONTokener(raw).nextValue();
    }

    private static String readAll(InputStream stream) throws Exception {
        if (stream == null) return "";
        StringBuilder builder = new StringBuilder();
        try (BufferedReader reader =
                new BufferedReader(new InputStreamReader(stream, StandardCharsets.UTF_8))) {
            String line;
            while ((line = reader.readLine()) != null) {
                builder.append(line);
            }
        }
        return builder.toString();
    }

    private static String encode(String value) throws Exception {
        return URLEncoder.encode(value, "UTF-8");
    }

    private static String trimTrailingSlash(String value) {
        String trimmed = value == null ? "" : value.trim();
        while (trimmed.endsWith("/")) {
            trimmed = trimmed.substring(0, trimmed.length() - 1);
        }
        return trimmed;
    }

    private static boolean isBlank(String value) {
        return value == null || value.trim().isEmpty();
    }

    private static long clamp(long value, long min, long max) {
        return Math.max(min, Math.min(max, value));
    }

    private static void sleep(long ms) {
        try {
            Thread.sleep(ms);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    private interface TabCallable<T> {
        T call(Tab tab) throws Exception;
    }
}
