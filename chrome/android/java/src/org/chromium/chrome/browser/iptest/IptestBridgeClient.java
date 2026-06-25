// Copyright 2026 The IP-TEST Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

package org.chromium.chrome.browser.iptest;

import android.content.Context;
import android.content.Intent;

import org.chromium.base.Log;
import org.chromium.base.ThreadUtils;
import org.chromium.chrome.browser.browsing_data.BrowsingDataBridge;
import org.chromium.chrome.browser.browsing_data.BrowsingDataType;
import org.chromium.chrome.browser.ChromeTabbedActivity;
import org.chromium.chrome.browser.profiles.Profile;
import org.chromium.chrome.browser.tab.Tab;
import org.chromium.chrome.browser.tab.TabLaunchType;
import org.chromium.chrome.browser.browsing_data.TimePeriod;
import org.chromium.content_public.browser.LoadUrlParams;
import org.chromium.content_public.browser.RenderFrameHost;
import org.chromium.content_public.browser.WebContents;

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
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
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
    private static final Object LOCK = new Object();

    private static IptestBridgeClient sClient;

    private WeakReference<ChromeTabbedActivity> mActivity;
    private final Context mAppContext;
    private final String mSerial;
    private final String mHubUrl;
    private final String mToken;
    private final String mPackageName;
    private final List<JSONObject> mBridgeLogs = new ArrayList<>();
    private volatile boolean mStopped;
    private volatile boolean mPreferIsolatedWorldEval;

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

        synchronized (LOCK) {
            if (sClient != null
                    && sClient.matches(serial.trim(), hubUrl.trim(), token.trim())) {
                sClient.updateActivity(activity);
                return true;
            }
            if (sClient != null) sClient.stop();
            sClient = new IptestBridgeClient(activity, serial.trim(), hubUrl.trim(), token.trim());
            sClient.start();
        }
        return true;
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
            Object result = executeCommand(name, payload);
            Log.i(TAG, "Command success: %s id=%s", name, id);
            submitResult(id, true, result, null);
        } catch (Exception e) {
            Log.w(TAG, "Command failed: %s id=%s error=%s state=%s", name, id, e.toString(), readActivityState());
            submitResult(id, false, null, e.toString());
        }
    }

    private Object executeCommand(String name, JSONObject payload) throws Exception {
        addBridgeLog("debug", "command:start", name);
        switch (name) {
            case "navigate":
                return navigate(payload.optString("url", ""));
            case "evaluate":
                return evaluate(payload.optString("expression", ""), 15000);
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

    private Object navigate(String url) throws Exception {
        if (isBlank(url)) throw new IllegalArgumentException("navigate url is required");
        return runWithTab(
                url,
                tab -> {
                    tab.loadUrl(new LoadUrlParams(url));
                    return new JSONObject().put("ok", true).put("url", url);
                });
    }

    private Object cleanup() throws Exception {
        long startedAt = System.currentTimeMillis();
        JSONObject profileResult = clearNativeProfileData();
        JSONObject pageResult = runPageLevelCleanup();
        boolean nativeOk = profileResult.optBoolean("ok", false);
        boolean pageOk = pageResult.optBoolean("ok", false);
        JSONObject result =
                new JSONObject()
                        .put("ok", nativeOk && pageOk)
                        .put("mode", "native_profile_plus_page")
                        .put("nativeProfileCleared", nativeOk)
                        .put("pageLevelCleared", pageOk)
                        .put("profile", profileResult)
                        .put("page", pageResult)
                        .put("durationMs", System.currentTimeMillis() - startedAt);
        addBridgeLog(nativeOk && pageOk ? "debug" : "warn", "cleanup", result.toString());
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

    private JSONObject runPageLevelCleanup() throws Exception {
        Object result =
                evaluate(
                        "(async function(){"
                                + "const out={ok:true,mode:'page_level',steps:[],skipped:[]};"
                                + "const protocol=location.protocol||'';"
                                + "const hasOrigin=protocol==='http:'||protocol==='https:'||protocol==='file:';"
                                + "function skip(name,reason){out.skipped.push(name+':'+reason);}"
                                + "function fail(key,e){out.ok=false;out[key]=String(e);}"
                                + "try{if(hasOrigin&&window.localStorage){localStorage.clear();out.steps.push('localStorage');}else{skip('localStorage','no_origin');}}catch(e){hasOrigin?fail('localStorageError',e):skip('localStorage','no_origin:'+String(e));}"
                                + "try{if(hasOrigin&&window.sessionStorage){sessionStorage.clear();out.steps.push('sessionStorage');}else{skip('sessionStorage','no_origin');}}catch(e){hasOrigin?fail('sessionStorageError',e):skip('sessionStorage','no_origin:'+String(e));}"
                                + "try{if(hasOrigin){document.cookie.split(';').forEach(function(c){var name=c.replace(/^\\s*/,'').replace(/=.*/,'');if(name){document.cookie=name+'=;expires=Thu, 01 Jan 1970 00:00:00 GMT;path=/';document.cookie=name+'=;expires=Thu, 01 Jan 1970 00:00:00 GMT;path=/;domain='+location.hostname;}});out.steps.push('cookies');}else{skip('cookies','no_origin');}}catch(e){hasOrigin?fail('cookieError',e):skip('cookies','no_origin:'+String(e));}"
                                + "try{if(hasOrigin&&'caches' in window){const keys=await caches.keys();await Promise.all(keys.map(k=>caches.delete(k)));out.cacheKeysDeleted=keys.length;out.steps.push('cacheStorage');}else{skip('cacheStorage',hasOrigin?'unsupported':'no_origin');}}catch(e){hasOrigin?fail('cacheStorageError',e):skip('cacheStorage','no_origin:'+String(e));}"
                                + "try{if(hasOrigin&&navigator.serviceWorker&&navigator.serviceWorker.getRegistrations){const regs=await navigator.serviceWorker.getRegistrations();await Promise.all(regs.map(r=>r.unregister()));out.serviceWorkersUnregistered=regs.length;out.steps.push('serviceWorkers');}else{skip('serviceWorkers',hasOrigin?'unsupported':'no_origin');}}catch(e){hasOrigin?fail('serviceWorkerError',e):skip('serviceWorkers','no_origin:'+String(e));}"
                                + "try{if(hasOrigin&&'indexedDB' in window&&indexedDB&&indexedDB.databases){const dbs=await indexedDB.databases();await Promise.all(dbs.filter(db=>db&&db.name).map(db=>new Promise(resolve=>{const req=indexedDB.deleteDatabase(db.name);req.onsuccess=req.onerror=req.onblocked=function(){resolve();};})));out.indexedDbsDeleted=dbs.filter(db=>db&&db.name).length;out.steps.push('indexedDB');}else{skip('indexedDB',hasOrigin?'unsupported':'no_origin');}}catch(e){hasOrigin?fail('indexedDbError',e):skip('indexedDB','no_origin:'+String(e));}"
                                + "if(!out.ok){out.reason=Object.keys(out).filter(k=>/Error$/.test(k)).map(k=>k+'='+out[k]).join(';')||'page_level_cleanup_failed';}"
                                + "return out;"
                                + "})()",
                        20000);
        if (result instanceof JSONObject) return (JSONObject) result;
        return new JSONObject().put("ok", true).put("result", result);
    }

    private Object getPageSnapshot() throws Exception {
        return evaluate(
                "(function(){return {url:location.href,title:document.title,readyState:document.readyState,webdriver:navigator.webdriver,userAgent:navigator.userAgent,cookie:document.cookie,localStorageKeys:Object.keys(localStorage||{}),sessionStorageKeys:Object.keys(sessionStorage||{}),viewport:{width:innerWidth,height:innerHeight,dpr:devicePixelRatio||1},bodyTextLength:document.body&&document.body.innerText?document.body.innerText.trim().length:0};})()",
                8000);
    }

    private Object clickSelector(String selector) throws Exception {
        if (isBlank(selector)) throw new IllegalArgumentException("selector is required");
        return evaluate(
                "(function(){var el=document.querySelector(" + JSONObject.quote(selector) + ");"
                        + "if(!el)return {found:false};"
                        + "el.scrollIntoView({block:'center',inline:'center'});"
                        + "el.click();"
                        + "return {found:true};})()",
                8000);
    }

    private Object fillSelector(String selector, String value) throws Exception {
        if (isBlank(selector)) throw new IllegalArgumentException("selector is required");
        return evaluate(
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
                .put("page", page);
    }

    private Object evaluate(String expression, long timeoutMs) throws Exception {
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
        if (activity == null) return null;
        Tab tab = activity.getActivityTab();
        if (tab != null) return tab;
        if (!activity.didFinishNativeInitialization() || !activity.areTabModelsInitialized()) {
            return null;
        }
        try {
            String url = isBlank(fallbackUrl) ? "about:blank" : fallbackUrl;
            tab =
                    activity.getTabCreator(false)
                            .createNewTab(
                                    new LoadUrlParams(url),
                                    TabLaunchType.FROM_CHROME_UI,
                                    /* parent= */ null);
            if (tab != null) {
                addBridgeLog("debug", "tab:create", url);
                return tab;
            }
        } catch (Throwable t) {
            addBridgeLog("warn", "tab:create_failed", t.toString());
        }
        return activity.getActivityTab();
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
        waitForWebContents(fallbackUrl, 15000);
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
