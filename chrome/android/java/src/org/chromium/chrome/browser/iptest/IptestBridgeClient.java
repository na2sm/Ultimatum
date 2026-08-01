// Copyright 2026 The IP-TEST Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

package org.chromium.chrome.browser.iptest;

import android.app.ActivityManager;
import android.content.Context;
import android.content.Intent;
import android.graphics.Point;
import android.os.SystemClock;
import android.view.MotionEvent;
import android.view.View;

import org.chromium.base.CommandLine;
import org.chromium.base.Log;
import org.chromium.base.TerminationStatus;
import org.chromium.base.ThreadUtils;
import org.chromium.chrome.browser.browsing_data.BrowsingDataBridge;
import org.chromium.chrome.browser.browsing_data.BrowsingDataType;
import org.chromium.chrome.browser.ChromeTabbedActivity;
import org.chromium.chrome.browser.profiles.Profile;
import org.chromium.chrome.browser.tab.EmptyTabObserver;
import org.chromium.chrome.browser.tab.Tab;
import org.chromium.chrome.browser.tab.TabLaunchType;
import org.chromium.chrome.browser.tab.TabSelectionType;
import org.chromium.chrome.browser.tabmodel.TabClosureParams;
import org.chromium.chrome.browser.tabmodel.TabModel;
import org.chromium.chrome.browser.tabmodel.TabModelUtils;
import org.chromium.chrome.browser.browsing_data.TimePeriod;
import org.chromium.components.browsing_data.content.BrowsingDataInfo;
import org.chromium.components.browsing_data.content.BrowsingDataModel;
import org.chromium.content.browser.MotionEventAction;
import org.chromium.content_public.browser.LoadUrlParams;
import org.chromium.content_public.browser.MotionEventSynthesizer;
import org.chromium.content_public.browser.NavigationHandle;
import org.chromium.content_public.browser.RenderFrameHost;
import org.chromium.content_public.browser.WebContents;
import org.chromium.content_public.browser.WebContentsObserver;
import org.chromium.url.GURL;
import org.chromium.url.Origin;

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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
    public static final String EXTRA_SESSION_GENERATION = "iptest_session_generation";

    private static final String TAG = "IptestBridgeClient";
    private static final String BRIDGE_VERSION = "native-v4";
    private static final String SWITCH_IN_PROCESS_GPU = "in-process-gpu";
    private static final Object LOCK = new Object();
    private static final long START_RETRY_DELAY_MS = 300;
    private static final long START_RETRY_DEADLINE_MS = 60000;
    private static final long NAVIGATION_COMMITTED_SETTLE_MS = 2500;
    private static final long NATIVE_CONSENT_TOUCH_DURATION_MS = 70;
    private static final Pattern FINGERPRINT_CONSOLE_IDS =
            Pattern.compile("([A-Za-z0-9_.:-]{12,160})\\s+([A-Za-z0-9_-]{12,128})");

    private static IptestBridgeClient sClient;
    private static PendingLaunch sPendingLaunch;
    private static boolean sPendingRetryScheduled;
    private static volatile boolean sIptestLaunchRequested;

    private WeakReference<ChromeTabbedActivity> mActivity;
    private final Context mAppContext;
    private final String mSerial;
    private final String mHubUrl;
    private final String mToken;
    private final String mSessionGeneration;
    private final String mPackageName;
    private final List<JSONObject> mBridgeLogs = new ArrayList<>();
    private volatile boolean mStopped;
    private volatile boolean mPreferIsolatedWorldEval;
    private volatile int mAutomationTabId = -1;
    private volatile boolean mRendererResponsive = true;
    private volatile boolean mRenderProcessGone;
    private volatile int mLastRenderProcessTerminationStatus = -1;
    private volatile long mLastLoadStoppedAt;
    private volatile long mLastPageLoadFinishedAt;
    private volatile long mLastNavigationFinishedAt;
    private volatile String mLastKnownUrl = "";
    private volatile String mLastNavigationEvent = "";
    private volatile String mLastNavigationError = "";
    private volatile long mLastConsentEvidenceEpoch = -1;
    private volatile String mLastConsentEvidenceHash = "";
    private volatile String mLastCrash = "";
    private volatile JSONObject mLastFingerprintVisitorEvidence;
    private Tab mObservedTab;
    private WebContents mObservedWebContents;
    private final EmptyTabObserver mAutomationTabObserver =
            new EmptyTabObserver() {
                @Override
                public void onContentChanged(Tab tab) {
                    attachAutomationWebContentsObserver(tab);
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
    private final WebContentsObserver mAutomationWebContentsObserver =
            new WebContentsObserver() {
                @Override
                public void primaryMainFrameRenderProcessGone(
                        @TerminationStatus int terminationStatus) {
                    mRenderProcessGone = true;
                    mLastRenderProcessTerminationStatus = terminationStatus;
                    mRendererResponsive = false;
                    mLastCrash =
                            "primary_main_frame_render_process_gone:"
                                    + terminationStatus
                                    + ":"
                                    + System.currentTimeMillis();
                    addBridgeLog("warn", "renderer:primary_main_frame_gone", mLastCrash);
                }

                @Override
                public void webContentsDestroyed() {
                    mRenderProcessGone = true;
                    mRendererResponsive = false;
                    mLastCrash = "web_contents_destroyed:" + System.currentTimeMillis();
                    addBridgeLog("warn", "renderer:web_contents_destroyed", mLastCrash);
                }
            };

    private static final class PendingLaunch {
        final WeakReference<ChromeTabbedActivity> activity;
        final String serial;
        final String hubUrl;
        final String token;
        final String sessionGeneration;
        final long createdAt;
        int attempts;

        PendingLaunch(
                ChromeTabbedActivity activity,
                String serial,
                String hubUrl,
                String token,
                String sessionGeneration) {
            this.activity = new WeakReference<>(activity);
            this.serial = serial;
            this.hubUrl = hubUrl;
            this.token = token;
            this.sessionGeneration = sessionGeneration;
            this.createdAt = System.currentTimeMillis();
        }
    }

    private IptestBridgeClient(
            ChromeTabbedActivity activity,
            String serial,
            String hubUrl,
            String token,
            String sessionGeneration) {
        mActivity = new WeakReference<>(activity);
        mAppContext = activity.getApplicationContext();
        mSerial = serial;
        mHubUrl = trimTrailingSlash(hubUrl);
        mToken = token;
        mSessionGeneration = sessionGeneration;
        mPackageName = mAppContext.getPackageName();
    }

    /** Records the exact Fingerprint result already emitted by the controlled KH test page. */
    public static void onPageConsoleMessage(
            Tab tab, int level, String message, int lineNumber, String sourceId) {
        IptestBridgeClient client;
        synchronized (LOCK) {
            client = sClient;
        }
        if (client == null || client.mStopped) return;
        client.recordFingerprintVisitorEvidence(tab, level, message, lineNumber, sourceId);
    }

    private void recordFingerprintVisitorEvidence(
            Tab tab, int level, String message, int lineNumber, String sourceId) {
        try {
            if (tab == null) return;
            String pageUrl = safeTabUrl(tab);
            String source = sourceId == null ? "" : sourceId;
            if (!pageUrl.contains("khdevelopment.pl") && !source.contains("khdevelopment.pl")) return;
            Matcher matcher = FINGERPRINT_CONSOLE_IDS.matcher(message == null ? "" : message);
            if (!matcher.find()) {
                addBridgeLog(
                        "debug",
                        "fingerprint:console_unmatched",
                        "messageLength=" + (message == null ? 0 : message.length()));
                return;
            }
            JSONObject evidence =
                    new JSONObject()
                            .put("eventId", matcher.group(1))
                            .put("visitorId", matcher.group(2))
                            .put("pageUrl", pageUrl)
                            .put("sourceId", source)
                            .put("lineNumber", lineNumber)
                            .put("consoleLevel", level)
                            .put("capturedAt", System.currentTimeMillis())
                            .put("source", "kh_page_console");
            mLastFingerprintVisitorEvidence = evidence;
            addBridgeLog("info", "fingerprint:visitor_result", evidence.toString());
        } catch (Throwable ignored) {
        }
    }

    /** Marks an incoming launcher intent before Chromium's process mode is selected. */
    public static boolean markLaunchIntentForStartup(Intent intent) {
        if (!hasBridgeLaunchExtras(intent)) return false;
        sIptestLaunchRequested = true;
        return true;
    }

    /** Returns whether the current browser process was launched for IP-TEST automation. */
    public static boolean shouldUseSingleProcessStartup() {
        return sIptestLaunchRequested;
    }

    /** Starts or refreshes the singleton bridge when an IP-TEST launcher intent is present. */
    public static boolean maybeStartFromIntent(ChromeTabbedActivity activity, Intent intent) {
        if (activity == null || intent == null) return false;
        if (!markLaunchIntentForStartup(intent)) return false;
        String serial = intent.getStringExtra(EXTRA_SERIAL);
        String hubUrl = intent.getStringExtra(EXTRA_HUB_URL);
        String token = intent.getStringExtra(EXTRA_TOKEN);
        String sessionGeneration = intent.getStringExtra(EXTRA_SESSION_GENERATION);
        ensureIptestCommandLineSwitches();

        synchronized (LOCK) {
            String trimmedSerial = serial.trim();
            String trimmedHubUrl = hubUrl.trim();
            String trimmedToken = token.trim();
            String trimmedSessionGeneration =
                    isBlank(sessionGeneration) ? "" : sessionGeneration.trim();
            if (!isActivityReadyForBridge(activity)) {
                sPendingLaunch =
                        new PendingLaunch(
                                activity,
                                trimmedSerial,
                                trimmedHubUrl,
                                trimmedToken,
                                trimmedSessionGeneration);
                schedulePendingStartLocked();
                return true;
            }
            startOrRefreshLocked(
                    activity,
                    trimmedSerial,
                    trimmedHubUrl,
                    trimmedToken,
                    trimmedSessionGeneration);
        }
        return true;
    }

    private static boolean hasBridgeLaunchExtras(Intent intent) {
        if (intent == null) return false;
        String serial = intent.getStringExtra(EXTRA_SERIAL);
        String hubUrl = intent.getStringExtra(EXTRA_HUB_URL);
        String token = intent.getStringExtra(EXTRA_TOKEN);
        return !isBlank(serial) && !isBlank(hubUrl) && !isBlank(token);
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
            ChromeTabbedActivity activity,
            String serial,
            String hubUrl,
            String token,
            String sessionGeneration) {
        sPendingLaunch = null;
        if (sClient != null && sClient.matches(serial, hubUrl, token, sessionGeneration)) {
            sClient.updateActivity(activity);
            sClient.resetAutomationTabBestEffort("activity_refreshed");
            return;
        }
        if (sClient != null) sClient.stop();
        sClient =
                new IptestBridgeClient(
                        activity, serial, hubUrl, token, sessionGeneration);
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
                                    activity,
                                    pending.serial,
                                    pending.hubUrl,
                                    pending.token,
                                    pending.sessionGeneration);
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

    private boolean matches(
            String serial, String hubUrl, String token, String sessionGeneration) {
        return mSerial.equals(serial)
                && mHubUrl.equals(trimTrailingSlash(hubUrl))
                && mToken.equals(token)
                && mSessionGeneration.equals(sessionGeneration);
    }

    private void start() {
        logStartupDiagnostics("bridge_start");
        Thread thread = new Thread(this::runLoop, "IPTEST-BrowserBridge");
        thread.setDaemon(true);
        thread.start();
    }

    private void logStartupDiagnostics(String event) {
        try {
            CommandLine commandLine = CommandLine.getInstance();
            JSONObject switches =
                    new JSONObject()
                            .put("inProcessGpu", commandLine.hasSwitch(SWITCH_IN_PROCESS_GPU))
                            .put("singleProcess", commandLine.hasSwitch("single-process"))
                            .put(
                                    "rendererProcessLimit",
                                    commandLine.hasSwitch("renderer-process-limit"))
                            .put(
                                    "rendererProcessLimitValue",
                                    commandLine.getSwitchValue("renderer-process-limit"));
            JSONObject diagnostics =
                    new JSONObject()
                            .put("event", event)
                            .put("bridgeVersion", BRIDGE_VERSION)
                            .put("serial", mSerial)
                            .put("packageName", mPackageName)
                            .put("hubHost", safeHubHost(mHubUrl))
                            .put("tokenPresent", !isBlank(mToken))
                            .put("sessionGeneration", mSessionGeneration)
                            .put("commandLineSwitches", switches);
            Log.i(TAG, "IP-TEST bridge startup diagnostics: %s", diagnostics.toString());
            addBridgeLog("debug", event, diagnostics.toString());
        } catch (Throwable t) {
            Log.w(TAG, "Failed to log IP-TEST bridge startup diagnostics", t);
        }
    }

    private static String safeHubHost(String hubUrl) {
        try {
            return new URL(hubUrl).getHost();
        } catch (Throwable ignored) {
            return "";
        }
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
                                                .put("sessionGeneration", mSessionGeneration)
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
                        .put("sessionGeneration", mSessionGeneration)
                        .put("packageName", mPackageName)
                        .put("browserVersion", "ultimatum-native")
                        .put("userAgent", System.getProperty("http.agent", ""))
                        .put("bridgeVersion", BRIDGE_VERSION)
                        .put(
                                "capabilities",
                                new JSONArray()
                                        .put("nativeConsentStateV1")
                                        .put("nativeAtomicConsentV1")
                                        .put("nativeAtomicConsentRectV2")),
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
                return 60000;
            case "navigate":
                return 45000;
            case "evaluate":
            case "evaluatePage":
            case "evaluateInternal":
                return 20000;
            case "getNativeState":
            case "getConsentState":
            case "dismissConsent":
            case "dismissConsentRect":
            case "waitForNativeReady":
            case "resetAutomationTab":
            case "bringTaskToFront":
            case "goBack":
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
            case "getConsentState":
                return getConsentState(payload.optLong("timeoutMs", 5000));
            case "dismissConsent":
                return dismissConsent(payload);
            case "dismissConsentRect":
                return dismissConsentRect(payload);
            case "waitForNativeReady":
                return waitForNativeReady(payload.optLong("timeoutMs", 15000));
            case "resetAutomationTab":
                return resetAutomationTab(payload.optString("reason", "command"));
            case "bringTaskToFront":
                return bringTaskToFront(payload.optString("reason", "command"));
            case "getPageSnapshot":
                return getPageSnapshot();
            case "clickSelector":
                return clickSelector(payload.optString("selector", ""));
            case "fillSelector":
                return fillSelector(
                        payload.optString("selector", ""),
                        payload.optString("value", ""));
            case "cleanup":
                return cleanup(payload);
            case "getLogs":
                return getLogs();
            case "getVisitorIsolationEvidence":
                return getVisitorIsolationEvidence();
            case "reload":
                return runWithTab(
                        "about:blank",
                        tab -> {
                            tab.reload();
                            return new JSONObject().put("ok", true);
                        });
            case "goBack":
                return runWithTab(
                        "about:blank",
                        tab -> {
                            boolean canGoBack = tab.canGoBack();
                            if (canGoBack) tab.goBack();
                            return new JSONObject()
                                    .put("ok", true)
                                    .put("navigated", canGoBack)
                                    .put("url", safeTabUrl(tab))
                                    .put("nativeState", collectNativeStateOnUi());
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
                        if (isBenignNavigationAbortAfterCommit(reason, tab, url)) {
                            finish(tab, "aborted_after_commit", null);
                            return;
                        }
                        if (!done.compareAndSet(false, true)) return;
                        try {
                            tab.removeObserver(this);
                        } catch (Throwable ignored) {
                        }
                        error.set(reason + " " + describeTabState(tab));
                        latch.countDown();
                    }

                    private void finishIfUrlMatches(Tab tab, String event, GURL eventUrl) {
                        String eventUrlString = eventUrl == null ? "" : String.valueOf(eventUrl);
                        String tabUrl = safeTabUrl(tab);
                        if (!urlMatches(eventUrlString, url)
                                && !urlMatches(tabUrl, url)
                                && !urlMatches(mLastKnownUrl, url)) {
                            return;
                        }
                        finish(tab, event, eventUrl);
                    }

                    private void finishAfterSettledCommit(Tab tab, String event, GURL eventUrl) {
                        String eventUrlString = eventUrl == null ? "" : String.valueOf(eventUrl);
                        String tabUrl = safeTabUrl(tab);
                        if (!urlMatches(eventUrlString, url)
                                && !urlMatches(tabUrl, url)
                                && !urlMatches(mLastKnownUrl, url)) {
                            return;
                        }
                        ThreadUtils.postOnUiThreadDelayed(
                                () -> finishIfUrlMatches(tab, event, eventUrl),
                                NAVIGATION_COMMITTED_SETTLE_MS);
                    }

                    @Override
                    public void onPageLoadStarted(Tab tab, GURL eventUrl) {
                        if ("commit".equals(waitUntil)) {
                            finishIfUrlMatches(tab, "page_load_started_committed", eventUrl);
                        } else if ("domcontentloaded".equals(waitUntil)) {
                            finishAfterSettledCommit(
                                    tab, "page_load_started_committed_settled", eventUrl);
                        }
                    }

                    @Override
                    public void onUrlUpdated(Tab tab) {
                        if ("commit".equals(waitUntil)) {
                            finishIfUrlMatches(tab, "url_updated_committed", null);
                        } else if ("domcontentloaded".equals(waitUntil)) {
                            finishAfterSettledCommit(tab, "url_updated_committed_settled", null);
                        }
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
                            finishIfUrlMatches(
                                    tab,
                                    "primary_main_frame_finished",
                                    navigation == null ? null : navigation.getUrl());
                        }
                    }

                    @Override
                    public void onLoadStopped(Tab tab, boolean toDifferentDocument) {
                        if ("loadstopped".equals(waitUntil) || "load".equals(waitUntil)) {
                            finishIfUrlMatches(tab, "load_stopped", null);
                        }
                    }

                    @Override
                    public void onPageLoadFinished(Tab tab, GURL eventUrl) {
                        finishIfUrlMatches(tab, "page_load_finished", eventUrl);
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
        JSONObject output = result.get();
        if (output != null && "aborted_after_commit".equals(output.optString("event", ""))) {
            sleep(750);
        } else if (output != null && "domcontentloaded".equals(output.optString("waitUntil", ""))) {
            sleep(500);
        }
        return output;
    }

    private boolean isBenignNavigationAbortAfterCommit(String reason, Tab tab, String expectedUrl) {
        if (isBlank(reason) || isBlank(expectedUrl)) return false;
        boolean aborted =
                reason.startsWith("navigation_error:-3:")
                        || reason.startsWith("page_load_failed:-3")
                        || reason.startsWith("navigation_error:-15:")
                        || reason.startsWith("page_load_failed:-15");
        if (!aborted) return false;
        String tabUrl = safeTabUrl(tab);
        boolean committed =
                urlMatches(tabUrl, expectedUrl) || urlMatches(mLastKnownUrl, expectedUrl);
        if (committed) {
            mLastNavigationError = "";
            addBridgeLog("debug", "navigate:aborted_after_commit", reason);
        }
        return committed;
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

    private Object cleanup(JSONObject payload) throws Exception {
        long startedAt = System.currentTimeMillis();
        mLastFingerprintVisitorEvidence = null;
        List<String> verificationDomains = parseVerificationDomains(payload);
        boolean verifyStorage = payload.optBoolean("verifyStorage", !verificationDomains.isEmpty());
        JSONObject preResetResult = resetAutomationTabBestEffort("cleanup:pre");
        sleep(1000);
        JSONObject profileResult = clearNativeProfileData();
        JSONObject pageResult = runPageLevelCleanupBestEffort();
        JSONObject verificationResult = verifyStorage
                ? verifyNativeProfileDataCleared(verificationDomains)
                : new JSONObject()
                        .put("ok", true)
                        .put("supported", true)
                        .put("skipped", true)
                        .put("reason", "verifyStorage=false")
                        .put("checkedDomains", new JSONArray())
                        .put("remainingDomains", new JSONArray())
                        .put("remainingCount", 0);
        boolean nativeOk = profileResult.optBoolean("ok", false);
        boolean pageOk = pageResult.optBoolean("ok", false);
        boolean pageBlocking = pageResult.optBoolean("blocking", false);
        boolean verificationOk = verificationResult.optBoolean("ok", false);
        JSONObject resetResult = resetAutomationTabBestEffort("cleanup:post");
        JSONObject result =
                new JSONObject()
                        .put("ok", nativeOk && verificationOk)
                        .put("mode", "native_profile_plus_page")
                        .put("nativeProfileCleared", nativeOk)
                        .put("pageLevelCleared", pageOk)
                        .put("pageLevelBlocking", pageBlocking)
                        .put("cleanupDataTypes", new JSONArray()
                                .put("history")
                                .put("site_data")
                                .put("cache")
                                .put("form_data")
                                .put("site_settings"))
                        .put("cleanupVerification", verificationResult)
                        .put("preReset", preResetResult)
                        .put("profile", profileResult)
                        .put("page", pageResult)
                        .put("reset", resetResult)
                        .put("durationMs", System.currentTimeMillis() - startedAt);
        addBridgeLog(result.optBoolean("ok", false) ? "debug" : "warn", "cleanup", result.toString());
        return result;
    }

    private List<String> parseVerificationDomains(JSONObject payload) {
        Set<String> domains = new LinkedHashSet<>();
        JSONArray rawDomains = payload.optJSONArray("verificationDomains");
        if (rawDomains != null) {
            for (int i = 0; i < rawDomains.length(); i++) {
                String domain = normalizeDomain(rawDomains.optString(i, ""));
                if (!isBlank(domain)) domains.add(domain);
            }
        }
        String singleDomain = normalizeDomain(payload.optString("verificationDomain", ""));
        if (!isBlank(singleDomain)) domains.add(singleDomain);
        return new ArrayList<>(domains);
    }

    private static String normalizeDomain(String value) {
        if (value == null) return "";
        String candidate = value.trim().toLowerCase(Locale.ROOT);
        if (candidate.isEmpty()) return "";
        try {
            if (candidate.startsWith("http://") || candidate.startsWith("https://")) {
                GURL gurl = new GURL(candidate);
                candidate = gurl.getHost();
            } else {
                int schemeIndex = candidate.indexOf("://");
                if (schemeIndex >= 0) candidate = candidate.substring(schemeIndex + 3);
                int slashIndex = candidate.indexOf('/');
                if (slashIndex >= 0) candidate = candidate.substring(0, slashIndex);
                int questionIndex = candidate.indexOf('?');
                if (questionIndex >= 0) candidate = candidate.substring(0, questionIndex);
                int hashIndex = candidate.indexOf('#');
                if (hashIndex >= 0) candidate = candidate.substring(0, hashIndex);
                if (candidate.startsWith("[")) {
                    int closeBracket = candidate.indexOf(']');
                    if (closeBracket > 0) candidate = candidate.substring(1, closeBracket);
                } else {
                    int colonIndex = candidate.indexOf(':');
                    if (colonIndex > 0) candidate = candidate.substring(0, colonIndex);
                }
            }
        } catch (Throwable ignored) {
        }
        while (candidate.startsWith(".")) candidate = candidate.substring(1);
        while (candidate.endsWith(".")) candidate = candidate.substring(0, candidate.length() - 1);
        if (candidate.equals("localhost") || candidate.matches("\\d+\\.\\d+\\.\\d+\\.\\d+")) return candidate;
        if (!candidate.matches("[a-z0-9.-]+")) return "";
        return candidate;
    }

    private static boolean hostMatchesDomain(String host, String domain) {
        String normalizedHost = normalizeDomain(host);
        String normalizedDomain = normalizeDomain(domain);
        if (isBlank(normalizedHost) || isBlank(normalizedDomain)) return false;
        return normalizedHost.equals(normalizedDomain)
                || normalizedHost.endsWith("." + normalizedDomain);
    }

    private JSONObject verifyNativeProfileDataCleared(List<String> domains) throws Exception {
        long startedAt = System.currentTimeMillis();
        JSONArray checkedDomains = new JSONArray();
        for (String domain : domains) checkedDomains.put(domain);
        if (domains.isEmpty()) {
            return new JSONObject()
                    .put("ok", true)
                    .put("supported", true)
                    .put("checkedDomains", checkedDomains)
                    .put("remainingDomains", new JSONArray())
                    .put("remainingCount", 0)
                    .put("durationMs", System.currentTimeMillis() - startedAt);
        }

        CountDownLatch latch = new CountDownLatch(1);
        AtomicReference<JSONObject> result = new AtomicReference<>();
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
                        BrowsingDataBridge.buildBrowsingDataModelFromDisk(
                                profile,
                                model -> {
                                    try {
                                        JSONArray remaining = new JSONArray();
                                        Map<Origin, BrowsingDataInfo> data =
                                                model.getBrowsingDataInfo(profile, false);
                                        for (Map.Entry<Origin, BrowsingDataInfo> entry : data.entrySet()) {
                                            Origin origin = entry.getKey();
                                            BrowsingDataInfo info = entry.getValue();
                                            String host = normalizeDomain(origin.getHost());
                                            if (isBlank(host)) continue;
                                            String matchedDomain = "";
                                            for (String domain : domains) {
                                                if (hostMatchesDomain(host, domain)) {
                                                    matchedDomain = domain;
                                                    break;
                                                }
                                            }
                                            if (isBlank(matchedDomain)) continue;
                                            remaining.put(
                                                    new JSONObject()
                                                            .put("origin", origin.toString())
                                                            .put("host", host)
                                                            .put("matchedDomain", matchedDomain)
                                                            .put("cookieCount", info.getCookieCount())
                                                            .put("storageSize", info.getStorageSize())
                                                            .put("importantDomain", info.isDomainImportant()));
                                        }
                                        result.set(
                                                new JSONObject()
                                                        .put("ok", remaining.length() == 0)
                                                        .put("supported", true)
                                                        .put("checkedDomains", checkedDomains)
                                                        .put("remainingDomains", remaining)
                                                        .put("remainingCount", remaining.length())
                                                        .put("durationMs", System.currentTimeMillis() - startedAt));
                                    } catch (Throwable t) {
                                        error.set(t.toString());
                                    } finally {
                                        try {
                                            model.destroy();
                                        } catch (Throwable ignored) {
                                        }
                                        latch.countDown();
                                    }
                                });
                    } catch (Throwable t) {
                        error.set(t.toString());
                        latch.countDown();
                    }
                });
        boolean completed = latch.await(25000, TimeUnit.MILLISECONDS);
        if (!completed) {
            return new JSONObject()
                    .put("ok", false)
                    .put("supported", true)
                    .put("checkedDomains", checkedDomains)
                    .put("remainingDomains", new JSONArray())
                    .put("remainingCount", -1)
                    .put("reason", "cleanup_verification_timeout")
                    .put("durationMs", System.currentTimeMillis() - startedAt);
        }
        if (!isBlank(error.get())) {
            return new JSONObject()
                    .put("ok", false)
                    .put("supported", true)
                    .put("checkedDomains", checkedDomains)
                    .put("remainingDomains", new JSONArray())
                    .put("remainingCount", -1)
                    .put("reason", error.get())
                    .put("durationMs", System.currentTimeMillis() - startedAt);
        }
        return result.get() != null
                ? result.get()
                : new JSONObject()
                        .put("ok", false)
                        .put("supported", true)
                        .put("checkedDomains", checkedDomains)
                        .put("remainingDomains", new JSONArray())
                        .put("remainingCount", -1)
                        .put("reason", "cleanup_verification_missing_result")
                        .put("durationMs", System.currentTimeMillis() - startedAt);
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

    private Object getVisitorIsolationEvidence() {
        JSONObject evidence = mLastFingerprintVisitorEvidence;
        return evidence == null ? JSONObject.NULL : evidence;
    }

    private Object getBrowserInfo() throws Exception {
        return new JSONObject()
                .put("packageName", mPackageName)
                .put("bridgeVersion", BRIDGE_VERSION)
                .put("userAgent", System.getProperty("http.agent", ""))
                .put("nativeState", getNativeState())
                .put("page", new JSONObject().put("nativeState", getNativeState()));
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
            boolean rendererHealthy = lastState.optBoolean("rendererHealthy", true);
            if (readyForCommands) {
                lastState.put("ok", true);
                return lastState;
            }
            if (!triedReset && nativeReady && tabModelsReady && !rendererHealthy) {
                triedReset = true;
                resetAutomationTabBestEffort("renderer_unhealthy");
                sleep(500);
                continue;
            }
            if (!triedReset && nativeReady && tabModelsReady) {
                triedReset = true;
                resetAutomationTabBestEffort("wait_for_native_ready");
            }
            sleep(250);
        }
        if (!lastState.optBoolean("rendererHealthy", true)) {
            throw new IllegalStateException("native_renderer_unhealthy " + lastState);
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
                                int closedTabs = closeOtherRegularTabs(activity, tab.getId());
                                activateAutomationTab(activity, tab);
                                tab.loadUrl(new LoadUrlParams("about:blank"));
                                return output
                                        .put("ok", true)
                                        .put("reason", reason)
                                        .put("closedTabs", closedTabs)
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

    private JSONObject bringTaskToFront(String reason) throws Exception {
        JSONObject result =
                ThreadUtils.runOnUiThreadBlocking(
                        () -> {
                            ChromeTabbedActivity activity = mActivity.get();
                            JSONObject output = new JSONObject();
                            try {
                                if (activity == null) {
                                    return output.put("ok", false).put("reason", "no_activity");
                                }
                                ActivityManager activityManager =
                                        (ActivityManager)
                                                mAppContext.getSystemService(Context.ACTIVITY_SERVICE);
                                if (activityManager == null) {
                                    return output.put("ok", false).put("reason", "no_activity_manager");
                                }
                                int activityTaskId = activity.getTaskId();
                                int examinedTasks = 0;
                                for (ActivityManager.AppTask task : activityManager.getAppTasks()) {
                                    examinedTasks++;
                                    ActivityManager.RecentTaskInfo taskInfo = task.getTaskInfo();
                                    int taskId = taskInfo == null ? -1 : taskInfo.id;
                                    if (taskId != activityTaskId) continue;
                                    task.moveToFront();
                                    addBridgeLog(
                                            "info",
                                            "task:move_to_front",
                                            "reason=" + reason + " taskId=" + taskId);
                                    return output
                                            .put("ok", true)
                                            .put("reason", reason)
                                            .put("taskId", taskId)
                                            .put("examinedTasks", examinedTasks)
                                            .put("nativeState", collectNativeStateOnUi());
                                }
                                return output
                                        .put("ok", false)
                                        .put("reason", "task_not_found")
                                        .put("activityTaskId", activityTaskId)
                                        .put("examinedTasks", examinedTasks)
                                        .put("nativeState", collectNativeStateOnUi());
                            } catch (Exception e) {
                                return output.put("ok", false).put("reason", e.toString());
                            }
                        });
        sleep(250);
        return result;
    }

    private Object evaluatePage(String expression, long timeoutMs) throws Exception {
        if (isBlank(expression)) throw new IllegalArgumentException("evaluate expression is required");
        waitForWebContents("about:blank", Math.min(Math.max(5000, timeoutMs), 15000));
        try {
            Object result = evaluateWithMainFrame(expression, timeoutMs);
            mPreferIsolatedWorldEval = true;
            return result;
        } catch (Exception isolatedError) {
            addBridgeLog("warn", "evaluate:isolated_world_failed", isolatedError.toString());
            throw new IllegalStateException(
                    "evaluate failed; isolatedWorld=" + isolatedError
                            + "; webContentsFallback=disabled",
                    isolatedError);
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
            addBridgeLog("warn", "evaluate_internal:isolated_world_failed", isolatedError.toString());
            throw new IllegalStateException(
                    "evaluate internal failed; isolatedWorld=" + isolatedError
                            + "; webContentsFallback=disabled",
                    isolatedError);
        }
    }

    private boolean isSafePrimaryConsentLabel(String normalizedLabel) {
        if (isBlank(normalizedLabel)) return false;
        String normalized = normalizedLabel.trim().toLowerCase(Locale.US);
        if (normalized.matches(
                ".*(ustaw|preferenc|manage|settings|reject|odrzuc|odmow|decline|konfigur|dostosuj|anulowanie|zmien.*zgod).*")) {
            return false;
        }
        return normalized.matches(
                ".*(akcept|zaakcept|zgadzam|zgoda na wszystko|zezwol|accept|allow all|i agree|przejdz do serwisu|wlacz wszystko).*" );
    }

    private JSONObject dismissConsentRect(JSONObject payload) throws Exception {
        String expectedGeneration = payload.optString("sessionGeneration", "").trim();
        if (isBlank(expectedGeneration) || !mSessionGeneration.equals(expectedGeneration)) {
            return new JSONObject()
                    .put("ok", false)
                    .put("dispatched", false)
                    .put("reason", "session_generation_mismatch")
                    .put("expectedSessionGeneration", mSessionGeneration)
                    .put("actualSessionGeneration", expectedGeneration);
        }

        String targetLabel = payload.optString("targetLabel", "").trim();
        String normalizedLabel = payload.optString("targetLabelNormalized", "").trim();
        if (!isSafePrimaryConsentLabel(normalizedLabel)) {
            return new JSONObject()
                    .put("ok", false)
                    .put("dispatched", false)
                    .put("reason", "unsafe_target_label")
                    .put("label", targetLabel)
                    .put("sessionGeneration", mSessionGeneration);
        }

        long evidenceEpoch = payload.optLong("evidenceEpoch", -1);
        String screenshotHash = payload.optString("screenshotHash", "").trim();
        synchronized (LOCK) {
            if (evidenceEpoch < 0 || evidenceEpoch < mLastConsentEvidenceEpoch) {
                return new JSONObject()
                        .put("ok", false)
                        .put("dispatched", false)
                        .put("reason", "stale_evidence_epoch")
                        .put("evidenceEpoch", evidenceEpoch)
                        .put("lastEvidenceEpoch", mLastConsentEvidenceEpoch);
            }
            if (evidenceEpoch == mLastConsentEvidenceEpoch
                    && !isBlank(screenshotHash)
                    && screenshotHash.equals(mLastConsentEvidenceHash)) {
                return new JSONObject()
                        .put("ok", false)
                        .put("dispatched", false)
                        .put("reason", "evidence_epoch_replayed")
                        .put("evidenceEpoch", evidenceEpoch);
            }
        }

        JSONObject rect = payload.optJSONObject("rect");
        int screenshotWidth = payload.optInt("screenshotWidth", 0);
        int screenshotHeight = payload.optInt("screenshotHeight", 0);
        double left = rect == null ? Double.NaN : rect.optDouble("left", Double.NaN);
        double top = rect == null ? Double.NaN : rect.optDouble("top", Double.NaN);
        double right = rect == null ? Double.NaN : rect.optDouble("right", Double.NaN);
        double bottom = rect == null ? Double.NaN : rect.optDouble("bottom", Double.NaN);
        if (screenshotWidth <= 0
                || screenshotHeight <= 0
                || !Double.isFinite(left)
                || !Double.isFinite(top)
                || !Double.isFinite(right)
                || !Double.isFinite(bottom)
                || left < 0
                || top < 0
                || right > 1
                || bottom > 1
                || right <= left
                || bottom <= top) {
            return new JSONObject()
                    .put("ok", false)
                    .put("dispatched", false)
                    .put("reason", "invalid_screen_rect")
                    .put("sessionGeneration", mSessionGeneration);
        }

        long startedAt = System.currentTimeMillis();
        AtomicReference<JSONObject> dispatchResult = new AtomicReference<>();
        CountDownLatch touchLatch = new CountDownLatch(1);
        AtomicBoolean delayedUpScheduled = new AtomicBoolean(false);
        ThreadUtils.postOnUiThread(
                () -> {
                    try {
                        ChromeTabbedActivity activity = mActivity.get();
                        Tab tab = activity == null ? null : activity.getActivityTab();
                        View contentView = tab == null ? null : tab.getContentView();
                        WebContents webContents = tab == null ? null : tab.getWebContents();
                        if (activity == null
                                || tab == null
                                || contentView == null
                                || webContents == null
                                || !contentView.isShown()
                                || !activity.hasWindowFocus()) {
                            dispatchResult.set(
                                    new JSONObject()
                                            .put("ok", false)
                                            .put("dispatched", false)
                                            .put("reason", "foreground_mismatch"));
                            return;
                        }
                        int orientation =
                                activity.getResources().getConfiguration().orientation;
                        String requestedOrientation = payload.optString("orientation", "");
                        String currentOrientation = orientation == 2 ? "landscape" : "portrait";
                        if (!requestedOrientation.equals(currentOrientation)) {
                            dispatchResult.set(
                                    new JSONObject()
                                            .put("ok", false)
                                            .put("dispatched", false)
                                            .put("reason", "orientation_mismatch")
                                            .put("expectedOrientation", currentOrientation)
                                            .put("actualOrientation", requestedOrientation));
                            return;
                        }

                        Point realSize = new Point();
                        activity.getWindowManager().getDefaultDisplay().getRealSize(realSize);
                        if (Math.abs(realSize.x - screenshotWidth) > 4
                                || Math.abs(realSize.y - screenshotHeight) > 4) {
                            dispatchResult.set(
                                    new JSONObject()
                                            .put("ok", false)
                                            .put("dispatched", false)
                                            .put("reason", "screen_geometry_mismatch")
                                            .put("screenWidth", realSize.x)
                                            .put("screenHeight", realSize.y));
                            return;
                        }

                        int[] screenLocation = new int[2];
                        contentView.getLocationOnScreen(screenLocation);
                        double targetScreenXBase = ((left + right) / 2.0) * realSize.x;
                        double targetScreenYBase = ((top + bottom) / 2.0) * realSize.y;
                        double rectWidth = (right - left) * realSize.x;
                        double rectHeight = (bottom - top) * realSize.y;
                        final double targetScreenX =
                                targetScreenXBase
                                        + (Math.random() - 0.5)
                                                * Math.min(12, rectWidth * 0.12);
                        final double targetScreenY =
                                targetScreenYBase
                                        + (Math.random() - 0.5)
                                                * Math.min(10, rectHeight * 0.12);
                        float viewX = (float) (targetScreenX - screenLocation[0]);
                        float viewY = (float) (targetScreenY - screenLocation[1]);
                        if (viewX < 2
                                || viewY < 2
                                || viewX > contentView.getWidth() - 3
                                || viewY > contentView.getHeight() - 3) {
                            dispatchResult.set(
                                    new JSONObject()
                                            .put("ok", false)
                                            .put("dispatched", false)
                                            .put("reason", "screen_rect_outside_content_view")
                                            .put("screenX", targetScreenX)
                                            .put("screenY", targetScreenY));
                            return;
                        }

                        long downTime = SystemClock.uptimeMillis();
                        MotionEventSynthesizer synthesizer =
                                MotionEventSynthesizer.create(contentView);
                        synthesizer.setPointer(
                                0, viewX, viewY, 0, MotionEvent.TOOL_TYPE_FINGER);
                        synthesizer.inject(MotionEventAction.START, 1, 0, downTime);
                        ThreadUtils.postOnUiThreadDelayed(
                                () -> {
                                    try {
                                        synthesizer.inject(
                                                MotionEventAction.END,
                                                1,
                                                0,
                                                SystemClock.uptimeMillis());
                                        dispatchResult.set(
                                                new JSONObject()
                                                        .put("ok", true)
                                                        .put("dispatched", true)
                                                        .put("reason", "motion_event_synthesized_from_screen_rect")
                                                        .put("label", targetLabel)
                                                        .put("evidenceEpoch", evidenceEpoch)
                                                        .put(
                                                                "touchPoint",
                                                                new JSONObject()
                                                                        .put("viewX", viewX)
                                                                        .put("viewY", viewY)
                                                                        .put("screenX", targetScreenX)
                                                                        .put("screenY", targetScreenY))
                                                        .put(
                                                                "mapping",
                                                                new JSONObject()
                                                                        .put("source", "ocr_screen_rect")
                                                                        .put("screenWidth", realSize.x)
                                                                        .put("screenHeight", realSize.y)
                                                                        .put("contentViewScreenX", screenLocation[0])
                                                                        .put("contentViewScreenY", screenLocation[1])
                                                                        .put("viewWidth", contentView.getWidth())
                                                                        .put("viewHeight", contentView.getHeight())
                                                                        .put("orientation", currentOrientation)));
                                    } catch (Throwable t) {
                                        try {
                                            dispatchResult.set(
                                                    new JSONObject()
                                                            .put("ok", false)
                                                            .put("dispatched", false)
                                                            .put("reason", "motion_event_up_exception")
                                                            .put("error", t.toString()));
                                        } catch (Exception ignored) {
                                        }
                                    } finally {
                                        touchLatch.countDown();
                                    }
                                },
                                NATIVE_CONSENT_TOUCH_DURATION_MS);
                        delayedUpScheduled.set(true);
                    } catch (Throwable t) {
                        try {
                            dispatchResult.set(
                                    new JSONObject()
                                            .put("ok", false)
                                            .put("dispatched", false)
                                            .put("reason", "motion_event_exception")
                                            .put("error", t.toString()));
                        } catch (Exception ignored) {
                        }
                    } finally {
                        if (!delayedUpScheduled.get()) touchLatch.countDown();
                    }
                });

        if (!touchLatch.await(2500, TimeUnit.MILLISECONDS)) {
            return new JSONObject()
                    .put("ok", false)
                    .put("dispatched", false)
                    .put("reason", "motion_event_timeout")
                    .put("sessionGeneration", mSessionGeneration);
        }
        JSONObject result = dispatchResult.get();
        if (result == null) {
            result = new JSONObject()
                    .put("ok", false)
                    .put("dispatched", false)
                    .put("reason", "motion_event_missing_result");
        }
        if (result.optBoolean("dispatched", false)) {
            synchronized (LOCK) {
                mLastConsentEvidenceEpoch = evidenceEpoch;
                mLastConsentEvidenceHash = screenshotHash;
            }
        }
        result.put("sessionGeneration", mSessionGeneration);
        result.put("durationMs", System.currentTimeMillis() - startedAt);
        return result;
    }

    private JSONObject dismissConsent(JSONObject payload) throws Exception {
        String expectedGeneration = payload.optString("sessionGeneration", "").trim();
        if (isBlank(expectedGeneration) || !mSessionGeneration.equals(expectedGeneration)) {
            return new JSONObject()
                    .put("ok", false)
                    .put("dispatched", false)
                    .put("reason", "session_generation_mismatch")
                    .put("expectedSessionGeneration", mSessionGeneration)
                    .put("actualSessionGeneration", expectedGeneration);
        }

        long timeoutMs = clamp(payload.optLong("timeoutMs", 7000), 2500, 10000);
        long startedAt = System.currentTimeMillis();
        JSONObject preState = getConsentState(Math.min(4000, timeoutMs));
        JSONObject primaryCta = preState.optJSONObject("primaryCta");
        if (primaryCta == null) {
            return new JSONObject()
                    .put("ok", true)
                    .put("dispatched", false)
                    .put("reason", "no_target")
                    .put("sessionGeneration", mSessionGeneration)
                    .put("preState", preState)
                    .put("postState", preState)
                    .put("durationMs", System.currentTimeMillis() - startedAt);
        }
        String expectedTargetLabel =
                payload.optString("targetLabelNormalized", "").trim().toLowerCase();
        String actualTargetLabel =
                primaryCta.optString("normalizedLabel", "").trim().toLowerCase();
        boolean targetLabelMatches =
                isBlank(expectedTargetLabel)
                        || actualTargetLabel.equals(expectedTargetLabel)
                        || (actualTargetLabel.length() >= 5
                                && expectedTargetLabel.length() >= 5
                                && (actualTargetLabel.contains(expectedTargetLabel)
                                        || expectedTargetLabel.contains(actualTargetLabel)));
        if (!targetLabelMatches) {
            return new JSONObject()
                    .put("ok", true)
                    .put("dispatched", false)
                    .put("reason", "target_label_mismatch")
                    .put("targetLabel", primaryCta.optString("label", ""))
                    .put("targetLabelNormalized", actualTargetLabel)
                    .put("expectedTargetLabelNormalized", expectedTargetLabel)
                    .put("sessionGeneration", mSessionGeneration)
                    .put("preState", preState)
                    .put("postState", preState)
                    .put("durationMs", System.currentTimeMillis() - startedAt);
        }

        JSONObject viewport = preState.optJSONObject("viewport");
        double viewportWidth = viewport == null ? 0 : viewport.optDouble("width", 0);
        double viewportHeight = viewport == null ? 0 : viewport.optDouble("height", 0);
        double left = primaryCta.optDouble("left", Double.NaN);
        double top = primaryCta.optDouble("top", Double.NaN);
        double right = primaryCta.optDouble("right", Double.NaN);
        double bottom = primaryCta.optDouble("bottom", Double.NaN);
        if (!(viewportWidth > 0)
                || !(viewportHeight > 0)
                || !Double.isFinite(left)
                || !Double.isFinite(top)
                || !Double.isFinite(right)
                || !Double.isFinite(bottom)
                || right <= left
                || bottom <= top) {
            return new JSONObject()
                    .put("ok", false)
                    .put("dispatched", false)
                    .put("reason", "invalid_target_geometry")
                    .put("sessionGeneration", mSessionGeneration)
                    .put("preState", preState)
                    .put("durationMs", System.currentTimeMillis() - startedAt);
        }

        JSONObject uiPreflight =
                ThreadUtils.runOnUiThreadBlocking(
                        () -> {
                            JSONObject output = new JSONObject();
                            try {
                                ChromeTabbedActivity activity = mActivity.get();
                                Tab tab = activity == null ? null : activity.getActivityTab();
                                View contentView = tab == null ? null : tab.getContentView();
                                if (activity == null
                                        || tab == null
                                        || contentView == null
                                        || !contentView.isShown()
                                        || !activity.hasWindowFocus()) {
                                    return output
                                            .put("ok", false)
                                            .put("dispatched", false)
                                            .put("reason", "foreground_mismatch");
                                }
                                return output
                                        .put("ok", true)
                                        .put(
                                                "activityIdentity",
                                                System.identityHashCode(activity))
                                        .put("tabId", tab.getId())
                                        .put(
                                                "contentViewIdentity",
                                                System.identityHashCode(contentView))
                                        .put(
                                                "orientation",
                                                activity
                                                        .getResources()
                                                        .getConfiguration()
                                                        .orientation);
                            } catch (Throwable t) {
                                return output
                                        .put("ok", false)
                                        .put("dispatched", false)
                                        .put("reason", "foreground_preflight_exception")
                                        .put("error", t.toString());
                            }
                        });
        if (!uiPreflight.optBoolean("ok", false)) {
            uiPreflight.put("sessionGeneration", mSessionGeneration);
            uiPreflight.put("preState", preState);
            uiPreflight.put("durationMs", System.currentTimeMillis() - startedAt);
            return uiPreflight;
        }
        int expectedActivityIdentity = uiPreflight.optInt("activityIdentity", 0);
        int expectedTabId = uiPreflight.optInt("tabId", -1);
        int expectedContentViewIdentity = uiPreflight.optInt("contentViewIdentity", 0);
        int expectedOrientation = uiPreflight.optInt("orientation", 0);

        CountDownLatch touchLatch = new CountDownLatch(1);
        AtomicReference<JSONObject> dispatchResult = new AtomicReference<>();
        AtomicBoolean delayedUpScheduled = new AtomicBoolean(false);
        ThreadUtils.postOnUiThread(
                () -> {
                    try {
                        ChromeTabbedActivity activity = mActivity.get();
                        Tab tab = activity == null ? null : activity.getActivityTab();
                        WebContents webContents = tab == null ? null : tab.getWebContents();
                        View contentView = tab == null ? null : tab.getContentView();
                        int orientation =
                                activity == null
                                        ? 0
                                        : activity
                                                .getResources()
                                                .getConfiguration()
                                                .orientation;
                        if (activity == null
                                || System.identityHashCode(activity) != expectedActivityIdentity
                                || tab == null
                                || tab.getId() != expectedTabId
                                || webContents == null
                                || contentView == null
                                || !contentView.isShown()
                                || !activity.hasWindowFocus()) {
                            dispatchResult.set(
                                    new JSONObject()
                                            .put("ok", false)
                                            .put("dispatched", false)
                                            .put("reason", "foreground_changed_before_dispatch"));
                            return;
                        }
                        if (orientation != expectedOrientation) {
                            dispatchResult.set(
                                    new JSONObject()
                                            .put("ok", false)
                                            .put("dispatched", false)
                                            .put("reason", "orientation_changed_before_dispatch"));
                            return;
                        }

                        int viewWidth = contentView.getWidth();
                        int viewHeight = contentView.getHeight();
                        if (viewWidth <= 4 || viewHeight <= 4) {
                            dispatchResult.set(
                                    new JSONObject()
                                            .put("ok", false)
                                            .put("dispatched", false)
                                            .put("reason", "content_view_not_laid_out"));
                            return;
                        }

                        double scaleX = viewWidth / viewportWidth;
                        double scaleY = viewHeight / viewportHeight;
                        double mappedLeft = Math.max(2, Math.min(viewWidth - 3, left * scaleX));
                        double mappedRight = Math.max(2, Math.min(viewWidth - 3, right * scaleX));
                        double mappedTop = Math.max(2, Math.min(viewHeight - 3, top * scaleY));
                        double mappedBottom = Math.max(2, Math.min(viewHeight - 3, bottom * scaleY));
                        double jitterX =
                                (Math.random() - 0.5)
                                        * Math.min(12, Math.max(2, (mappedRight - mappedLeft) * 0.12));
                        double jitterY =
                                (Math.random() - 0.5)
                                        * Math.min(10, Math.max(2, (mappedBottom - mappedTop) * 0.12));
                        float viewTouchX =
                                (float)
                                        Math.max(
                                                mappedLeft + 2,
                                                Math.min(
                                                        mappedRight - 2,
                                                        (mappedLeft + mappedRight) / 2 + jitterX));
                        float viewTouchY =
                                (float)
                                        Math.max(
                                                mappedTop + 2,
                                                Math.min(
                                                        mappedBottom - 2,
                                                        (mappedTop + mappedBottom) / 2 + jitterY));
                        int[] screenLocation = new int[2];
                        contentView.getLocationOnScreen(screenLocation);
                        long downTime = SystemClock.uptimeMillis();
                        MotionEventSynthesizer synthesizer =
                                MotionEventSynthesizer.create(contentView);
                        synthesizer.setPointer(
                                0,
                                viewTouchX,
                                viewTouchY,
                                0,
                                MotionEvent.TOOL_TYPE_FINGER);
                        synthesizer.inject(
                                MotionEventAction.START, 1, 0, downTime);
                        View dispatchContentView = contentView;
                        MotionEventSynthesizer dispatchSynthesizer = synthesizer;
                        ThreadUtils.postOnUiThreadDelayed(
                                () -> {
                                    try {
                                        ChromeTabbedActivity dispatchActivity = mActivity.get();
                                        Tab dispatchTab =
                                                dispatchActivity == null
                                                        ? null
                                                        : dispatchActivity.getActivityTab();
                                        View currentContentView =
                                                dispatchTab == null
                                                        ? null
                                                        : dispatchTab.getContentView();
                                        int dispatchOrientation =
                                                dispatchActivity == null
                                                        ? 0
                                                        : dispatchActivity
                                                                .getResources()
                                                                .getConfiguration()
                                                                .orientation;
                                        if (dispatchActivity == null
                                                || System.identityHashCode(dispatchActivity)
                                                        != expectedActivityIdentity
                                                || dispatchTab == null
                                                || dispatchTab.getId() != expectedTabId
                                                || currentContentView == null
                                                || currentContentView != dispatchContentView
                                                || System.identityHashCode(currentContentView)
                                                        != expectedContentViewIdentity
                                                || !currentContentView.isShown()
                                                || !dispatchActivity.hasWindowFocus()) {
                                            dispatchResult.set(
                                                    new JSONObject()
                                                            .put("ok", false)
                                                            .put("dispatched", false)
                                                            .put(
                                                                    "reason",
                                                                    "foreground_changed_before_touch_up"));
                                            return;
                                        }
                                        if (dispatchOrientation != expectedOrientation) {
                                            dispatchResult.set(
                                                    new JSONObject()
                                                            .put("ok", false)
                                                            .put("dispatched", false)
                                                            .put(
                                                                    "reason",
                                                                    "orientation_changed_before_touch_up"));
                                            return;
                                        }
                                        long upTime = SystemClock.uptimeMillis();
                                        dispatchSynthesizer.inject(
                                                MotionEventAction.END, 1, 0, upTime);
                                        dispatchResult.set(
                                                new JSONObject()
                                                        .put("ok", true)
                                                        .put("dispatched", true)
                                                        .put("reason", "motion_event_synthesized")
                                                        .put(
                                                                "pointerToolType",
                                                                MotionEvent.TOOL_TYPE_FINGER)
                                                        .put(
                                                                "touchDurationMs",
                                                                upTime - downTime)
                                                        .put(
                                                                "touchPoint",
                                                                new JSONObject()
                                                                        .put("viewX", viewTouchX)
                                                                        .put("viewY", viewTouchY)
                                                                        .put(
                                                                                "screenX",
                                                                                screenLocation[0]
                                                                                        + viewTouchX)
                                                                        .put(
                                                                                "screenY",
                                                                                screenLocation[1]
                                                                                        + viewTouchY))
                                                        .put(
                                                                "mapping",
                                                                new JSONObject()
                                                                        .put(
                                                                                "dispatcher",
                                                                                "chromium_motion_event_synthesizer")
                                                                        .put(
                                                                                "viewportWidth",
                                                                                viewportWidth)
                                                                        .put(
                                                                                "viewportHeight",
                                                                                viewportHeight)
                                                                        .put(
                                                                                "viewWidth",
                                                                                viewWidth)
                                                                        .put(
                                                                                "viewHeight",
                                                                                viewHeight)
                                                                        .put(
                                                                                "contentViewScreenX",
                                                                                screenLocation[0])
                                                                        .put(
                                                                                "contentViewScreenY",
                                                                                screenLocation[1])
                                                                        .put("scaleX", scaleX)
                                                                        .put("scaleY", scaleY)
                                                                        .put(
                                                                                "orientation",
                                                                                dispatchOrientation)));
                                    } catch (Throwable t) {
                                        JSONObject errorResult = new JSONObject();
                                        try {
                                            errorResult
                                                    .put("ok", false)
                                                    .put("dispatched", false)
                                                    .put("reason", "motion_event_up_exception")
                                                    .put("error", t.toString());
                                        } catch (Exception jsonError) {
                                            Log.e(
                                                    TAG,
                                                    "Failed to serialize MotionEvent up exception",
                                                    jsonError);
                                        }
                                        dispatchResult.set(errorResult);
                                    } finally {
                                        touchLatch.countDown();
                                    }
                                },
                                NATIVE_CONSENT_TOUCH_DURATION_MS);
                        delayedUpScheduled.set(true);
                    } catch (Throwable t) {
                        JSONObject errorResult = new JSONObject();
                        try {
                            errorResult
                                    .put("ok", false)
                                    .put("dispatched", false)
                                    .put("reason", "motion_event_exception")
                                    .put("error", t.toString());
                        } catch (Exception jsonError) {
                            Log.e(TAG, "Failed to serialize MotionEvent exception", jsonError);
                        }
                        dispatchResult.set(errorResult);
                    } finally {
                        if (!delayedUpScheduled.get()) touchLatch.countDown();
                    }
                });

        if (!touchLatch.await(Math.min(2500, timeoutMs), TimeUnit.MILLISECONDS)) {
            return new JSONObject()
                    .put("ok", false)
                    .put("dispatched", false)
                    .put("reason", "motion_event_timeout")
                    .put("sessionGeneration", mSessionGeneration)
                    .put("preState", preState)
                    .put("durationMs", System.currentTimeMillis() - startedAt);
        }
        JSONObject dispatch = dispatchResult.get();
        if (dispatch == null || !dispatch.optBoolean("dispatched", false)) {
            if (dispatch == null) dispatch = new JSONObject().put("reason", "missing_dispatch_result");
            dispatch.put("sessionGeneration", mSessionGeneration);
            dispatch.put("preState", preState);
            dispatch.put("durationMs", System.currentTimeMillis() - startedAt);
            return dispatch;
        }

        sleep(Math.min(800, Math.max(350, timeoutMs - (System.currentTimeMillis() - startedAt) - 1000)));
        JSONObject postState =
                getConsentState(
                        Math.max(
                                1000,
                                Math.min(
                                        3500,
                                        timeoutMs - (System.currentTimeMillis() - startedAt))));
        JSONObject postCta = postState.optJSONObject("primaryCta");
        boolean renderChanged =
                postCta == null
                        || postState.optBoolean("blockingOverlay", true)
                                != preState.optBoolean("blockingOverlay", true)
                        || !postState.optString("url", "")
                                .equals(preState.optString("url", ""))
                        || postState.optInt("bodyTextLength", -1)
                                != preState.optInt("bodyTextLength", -1);
        dispatch.put("sessionGeneration", mSessionGeneration);
        dispatch.put("label", primaryCta.optString("label", ""));
        dispatch.put("rect", primaryCta);
        dispatch.put("url", preState.optString("url", ""));
        dispatch.put("preState", preState);
        dispatch.put("postState", postState);
        dispatch.put("renderChanged", renderChanged);
        dispatch.put("noEffect", !renderChanged);
        dispatch.put("durationMs", System.currentTimeMillis() - startedAt);
        return dispatch;
    }

    private JSONObject getConsentState(long requestedTimeoutMs) throws Exception {
        long timeoutMs = clamp(requestedTimeoutMs, 1000, 10000);
        String expression =
                "(() => {"
                        + "const norm=(v)=>String(v||'').normalize('NFD')"
                        + ".replace(/[\\u0300-\\u036f]/g,'').toLowerCase()"
                        + ".replace(/[^a-z0-9\\s]/g,' ').replace(/\\s+/g,' ').trim();"
                        + "const positive=["
                        + "'w porzadku','akceptuje wszystkie','akceptuj wszystkie',"
                        + "'zaakceptuj wszystkie','zaakceptuj zgody',"
                        + "'akceptuj wszystkie pliki cookie','akceptuje cookies',"
                        + "'akceptuj cookies','zezwol na wszystkie',"
                        + "'zgoda na wszystko','zgode na wszystko','zgadzam sie',"
                        + "'akceptuje i przechodze do serwisu',"
                        + "'zgadzam sie i przechodze do serwisu',"
                        + "'wlacz wszystko i przejdz do serwisu','przejdz do serwisu',"
                        + "'accept','accept cookies','accept all','allow all','agree','i agree'];"
                        + "const negative=/(odrzuc|odmow|reject|decline|ustaw|preferenc|manage|configure|konfigur)/;"
                        + "const nodes=Array.from(document.querySelectorAll("
                        + "'button,[role=\"button\"],input[type=\"button\"],input[type=\"submit\"],a'));"
                        + "const candidates=[];"
                        + "for(const node of nodes){"
                        + "const r=node.getBoundingClientRect();const s=getComputedStyle(node);"
                        + "if(r.width<4||r.height<4||s.display==='none'||s.visibility==='hidden'||Number(s.opacity||1)===0)continue;"
                        + "const label=norm(node.innerText||node.value||node.textContent||node.getAttribute('aria-label'));"
                        + "if(!label||negative.test(label))continue;"
                        + "const exact=positive.includes(label);"
                        + "const contextual=!exact&&label.length>=5&&positive.some((p)=>label.length<=80&&(label.includes(p)||p.includes(label)));"
                        + "if(!exact&&!contextual)continue;"
                        + "const left=Math.max(0,r.left),top=Math.max(0,r.top);"
                        + "const right=Math.min(innerWidth,r.right),bottom=Math.min(innerHeight,r.bottom);"
                        + "if(right-left<4||bottom-top<4)continue;"
                        + "candidates.push({label:String(node.innerText||node.value||node.textContent||node.getAttribute('aria-label')||'').trim().slice(0,120),"
                        + "normalizedLabel:label,exact,left,top,right,bottom,width:right-left,height:bottom-top});"
                        + "}"
                        + "candidates.sort((a,b)=>(Number(b.exact)-Number(a.exact))||((b.width*b.height)-(a.width*a.height)));"
                        + "const consentWords=/(cookie|ciastecz|zgod|consent|privacy|prywatno|personal data|dane osobowe)/;"
                        + "const overlay=Array.from(document.querySelectorAll("
                        + "'[role=\"dialog\"],dialog,[aria-modal=\"true\"],#onetrust-banner-sdk,"
                        + "[id*=\"cookie\" i],[class*=\"cookie\" i],[id*=\"consent\" i],[class*=\"consent\" i],"
                        + "[id*=\"cmp\" i],[class*=\"cmp\" i]')).some((node)=>{"
                        + "const r=node.getBoundingClientRect();const s=getComputedStyle(node);"
                        + "const modal=node.matches('[role=\"dialog\"],dialog,[aria-modal=\"true\"]');"
                        + "const text=norm(node.innerText||node.textContent||node.getAttribute('aria-label'));"
                        + "const positioned=s.position==='fixed'||s.position==='sticky'||modal;"
                        + "return positioned&&consentWords.test(text)&&r.width>innerWidth*.35"
                        + "&&r.height>innerHeight*.08&&s.display!=='none'&&s.visibility!=='hidden'"
                        + "&&Number(s.opacity||1)!==0;});"
                        + "return {ok:true,url:location.href,readyState:document.readyState,"
                        + "viewport:{width:innerWidth,height:innerHeight,dpr:devicePixelRatio||1},"
                        + "bodyTextLength:(document.body&&document.body.innerText||'').length,"
                        + "primaryCta:candidates[0]||null,primaryCtaCount:candidates.length,"
                        + "blockingOverlay:overlay,capturedAt:Date.now()};"
                        + "})()";
        Object raw = evaluateInternal(expression, timeoutMs);
        JSONObject result =
                raw instanceof JSONObject
                        ? (JSONObject) raw
                        : new JSONObject().put("ok", false).put("reason", "invalid_consent_state");
        result.put("nativeState", getNativeState());
        result.put("sessionGeneration", mSessionGeneration);
        return result;
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
                        if (!isRendererHealthyForCommands()) {
                            error.set("Renderer unhealthy " + describeActivityState(activity));
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
        if (forceNew) return null;
        tab = activity.getActivityTab();
        if (isUsableTab(tab)) attachAutomationObserver(tab);
        return tab;
    }

    private int closeOtherRegularTabs(ChromeTabbedActivity activity, int keepTabId) {
        if (activity == null || keepTabId < 0) return 0;
        try {
            TabModel model = activity.getTabModelSelector().getModel(false);
            List<Tab> staleTabs = new ArrayList<>();
            for (int i = model.getCount() - 1; i >= 0; i--) {
                Tab candidate = model.getTabAt(i);
                if (candidate == null || candidate.getId() == keepTabId) continue;
                if (candidate.isClosing() || candidate.isDestroyed()) continue;
                staleTabs.add(candidate);
            }
            if (staleTabs.isEmpty()) return 0;
            model.getTabRemover()
                    .forceCloseTabs(
                            TabClosureParams.closeTabs(staleTabs)
                                    .allowUndo(false)
                                    .saveToTabRestoreService(false)
                                    .build());
            addBridgeLog("info", "tab:closed_stale_regular_tabs", String.valueOf(staleTabs.size()));
            return staleTabs.size();
        } catch (Throwable t) {
            addBridgeLog("warn", "tab:close_stale_failed", t.toString());
            return 0;
        }
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
                attachAutomationWebContentsObserver(tab);
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
            attachAutomationWebContentsObserver(tab);
            recordTabSnapshot(tab, "tab_observed");
        } catch (Throwable t) {
            addBridgeLog("warn", "tab:observe_failed", t.toString());
        }
    }

    private void attachAutomationWebContentsObserver(Tab tab) {
        try {
            WebContents webContents = tab == null ? null : tab.getWebContents();
            if (mObservedWebContents == webContents) return;
            mAutomationWebContentsObserver.observe(null);
            mObservedWebContents = webContents;
            if (webContents != null) {
                mRenderProcessGone = false;
                mLastRenderProcessTerminationStatus = -1;
                mRendererResponsive = true;
                mLastCrash = "";
                mAutomationWebContentsObserver.observe(webContents);
            }
        } catch (Throwable t) {
            addBridgeLog("warn", "renderer:observe_failed", t.toString());
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
        boolean foreground = false;
        String orientation = "unknown";
        int screenWidth = 0;
        int screenHeight = 0;
        boolean tabModelsReady = false;
        int tabCount = -1;
        int activityTabId = -1;
        Tab tab = null;
        if (activity != null) {
            try {
                foreground = activity.hasWindowFocus();
            } catch (Throwable ignored) {
            }
            try {
                orientation =
                        activity.getResources().getConfiguration().orientation == 2
                                ? "landscape"
                                : "portrait";
                Point realSize = new Point();
                activity.getWindowManager().getDefaultDisplay().getRealSize(realSize);
                screenWidth = realSize.x;
                screenHeight = realSize.y;
            } catch (Throwable ignored) {
            }
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
        boolean rendererHealthy = isRendererHealthyForCommands();
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
                        && mainFrameLive
                        && rendererHealthy;
        return new JSONObject()
                .put("sessionGeneration", mSessionGeneration)
                .put("foreground", foreground)
                .put("orientation", orientation)
                .put("screenWidth", screenWidth)
                .put("screenHeight", screenHeight)
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
                .put("rendererHealthy", rendererHealthy)
                .put("rendererResponsive", mRendererResponsive)
                .put("renderProcessGone", mRenderProcessGone)
                .put("lastRenderProcessTerminationStatus", mLastRenderProcessTerminationStatus)
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

    private boolean isRendererHealthyForCommands() {
        return mRendererResponsive && !mRenderProcessGone && isBlank(mLastCrash);
    }

    private boolean isTabReadyForJs(Tab tab) {
        if (tab == null || !tab.isInitialized() || tab.isDestroyed() || tab.isClosing()) {
            return false;
        }
        WebContents webContents = tab.getWebContents();
        RenderFrameHost mainFrame = webContents == null ? null : webContents.getMainFrame();
        return webContents != null
                && mainFrame != null
                && mainFrame.isRenderFrameLive()
                && isRendererHealthyForCommands();
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
        boolean rendererHealthy = isRendererHealthyForCommands();
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
                + ", rendererHealthy="
                + rendererHealthy
                + ", renderProcessGone="
                + mRenderProcessGone
                + ", lastRenderProcessTerminationStatus="
                + mLastRenderProcessTerminationStatus
                + ", rendererResponsive="
                + mRendererResponsive
                + ", lastCrash="
                + mLastCrash
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
            JSONObject body =
                    new JSONObject()
                            .put("id", id)
                            .put("token", mToken)
                            .put("sessionGeneration", mSessionGeneration)
                            .put("ok", ok);
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
        if (!isBlank(mSessionGeneration)) {
            connection.setRequestProperty(
                    "X-IPTEST-Browser-Generation", mSessionGeneration);
        }
        byte[] bytes = body.toString().getBytes(StandardCharsets.UTF_8);
        connection.setFixedLengthStreamingMode(bytes.length);
        try (OutputStream output = connection.getOutputStream()) {
            output.write(bytes);
        }
        int code = connection.getResponseCode();
        InputStream stream = code >= 400 ? connection.getErrorStream() : connection.getInputStream();
        String response = readAll(stream);
        if (code >= 400) {
            if (code == 401) {
                try {
                    JSONObject errorBody = isBlank(response) ? null : new JSONObject(response);
                    JSONObject recovery =
                            errorBody == null
                                    ? null
                                    : errorBody.optJSONObject("brokerAuthRecovery");
                    if (recovery != null
                            && "re_register".equals(recovery.optString("action", ""))) {
                        mStopped = true;
                        addBridgeLog(
                                "warn",
                                "auth:stale_session_stopped",
                                "generation="
                                        + mSessionGeneration
                                        + " endpoint="
                                        + path);
                    }
                } catch (Throwable ignored) {
                }
            }
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
