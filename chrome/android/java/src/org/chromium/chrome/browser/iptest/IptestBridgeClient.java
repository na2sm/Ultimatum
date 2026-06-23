// Copyright 2026 The IP-TEST Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

package org.chromium.chrome.browser.iptest;

import android.content.Context;
import android.content.Intent;

import org.chromium.base.Log;
import org.chromium.base.ThreadUtils;
import org.chromium.chrome.browser.ChromeTabbedActivity;
import org.chromium.chrome.browser.tab.Tab;
import org.chromium.content_public.browser.LoadUrlParams;
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
    private volatile boolean mStopped;

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
            Object result = executeCommand(name, payload);
            submitResult(id, true, result, null);
        } catch (Exception e) {
            submitResult(id, false, null, e.toString());
        }
    }

    private Object executeCommand(String name, JSONObject payload) throws Exception {
        switch (name) {
            case "navigate":
                return navigate(payload.optString("url", ""));
            case "evaluate":
                return evaluate(payload.optString("expression", ""), 15000);
            case "cleanup":
                return cleanup();
            case "getLogs":
                return new JSONArray();
            case "reload":
                return runWithTab(
                        tab -> {
                            tab.reload();
                            return new JSONObject().put("ok", true);
                        });
            case "goForward":
                return runWithTab(
                        tab -> {
                            tab.goForward();
                            return new JSONObject().put("ok", true);
                        });
            case "handleDialog":
                return false;
            case "getBrowserInfo":
                return new JSONObject()
                        .put("packageName", mPackageName)
                        .put("bridgeVersion", BRIDGE_VERSION)
                        .put("userAgent", System.getProperty("http.agent", ""));
            default:
                throw new IllegalArgumentException("native_command_not_implemented:" + name);
        }
    }

    private Object navigate(String url) throws Exception {
        if (isBlank(url)) throw new IllegalArgumentException("navigate url is required");
        return runWithTab(
                tab -> {
                    tab.loadUrl(new LoadUrlParams(url));
                    return new JSONObject().put("ok", true).put("url", url);
                });
    }

    private Object cleanup() throws Exception {
        return evaluate(
                "(function(){"
                        + "try{"
                        + "localStorage.clear();"
                        + "sessionStorage.clear();"
                        + "document.cookie.split(';').forEach(function(c){"
                        + "var name=c.replace(/^\\s*/,'').replace(/=.*/,'');"
                        + "if(name){document.cookie=name+'=;expires=Thu, 01 Jan 1970 00:00:00 GMT;path=/';"
                        + "document.cookie=name+'=;expires=Thu, 01 Jan 1970 00:00:00 GMT;path=/;domain='+location.hostname;}"
                        + "});"
                        + "return {ok:true,mode:'native_page_level'};"
                        + "}catch(e){return {ok:false,reason:String(e)}}"
                        + "})()",
                15000);
    }

    private Object evaluate(String expression, long timeoutMs) throws Exception {
        if (isBlank(expression)) throw new IllegalArgumentException("evaluate expression is required");
        CountDownLatch latch = new CountDownLatch(1);
        AtomicReference<String> rawResult = new AtomicReference<>();
        AtomicReference<String> error = new AtomicReference<>();

        ThreadUtils.postOnUiThread(
                () -> {
                    try {
                        ChromeTabbedActivity activity = mActivity.get();
                        WebContents webContents =
                                activity == null ? null : activity.getCurrentWebContents();
                        if (webContents == null) {
                            error.set("No current WebContents");
                            latch.countDown();
                            return;
                        }
                        webContents.evaluateJavaScriptForTests(
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
            throw new IllegalStateException("evaluate timeout");
        }
        if (!isBlank(error.get())) throw new IllegalStateException(error.get());
        return parseJsonResult(rawResult.get());
    }

    private <T> T runWithTab(TabCallable<T> callable) throws Exception {
        AtomicReference<Exception> error = new AtomicReference<>();
        T result =
                ThreadUtils.runOnUiThreadBlocking(
                        () -> {
                            try {
                                ChromeTabbedActivity activity = mActivity.get();
                                Tab tab = activity == null ? null : activity.getActivityTab();
                                if (tab == null) throw new IllegalStateException("No current tab");
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
