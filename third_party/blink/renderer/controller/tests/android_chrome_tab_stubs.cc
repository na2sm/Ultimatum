// Copyright 2026 The Chromium Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "chrome/browser/android/tab_android.h"
#include "chrome/browser/ui/android/tab_model/tab_model_list.h"

// Blink unit tests do not create Chrome's Java-backed tab model. The
// extension host is linked by the fork's navigation loader but must observe
// no Chrome tabs in this test process.
TabAndroid* TabAndroid::FromWebContents(content::WebContents*) {
  return nullptr;
}

const TabModelList::TabModelVector& TabModelList::models() {
  static const TabModelVector* const empty_models = new TabModelVector();
  return *empty_models;
}
