// Copyright 2026 The Chromium Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "cc/layers/layer.h"
#include "cc/trees/layer_tree_host.h"
#include "cc/trees/property_tree.h"
#include "content/test/test_blink_web_unit_test_support.h"
#include "testing/gtest/include/gtest/gtest.h"
#include "third_party/blink/renderer/core/dom/document.h"
#include "third_party/blink/renderer/core/dom/element.h"
#include "third_party/blink/renderer/core/frame/local_dom_window.h"
#include "third_party/blink/renderer/core/frame/local_frame_view.h"
#include "third_party/blink/renderer/core/html/html_iframe_element.h"
#include "third_party/blink/renderer/core/layout/layout_object.h"
#include "third_party/blink/renderer/core/paint/object_paint_properties.h"
#include "third_party/blink/renderer/core/script/classic_script.h"
#include "third_party/blink/renderer/core/testing/sim/sim_request.h"
#include "third_party/blink/renderer/core/testing/sim/sim_test.h"

namespace blink {

// Candidate triggers exercise real DOM, paint and animation initialization.
// A passing candidate excludes only that transition, not the production crash.
class IpTestOpacityLifecycleTest : public SimTest {
 public:
  IpTestOpacityLifecycleTest() {
    content::TestBlinkWebUnitTestSupport::SetThreadedAnimationEnabled(true);
  }

 protected:
  void LoadAnimatedScene() {
    ResizeView(gfx::Size(360, 800));
    SimRequest request("https://example.com/opacity.html", "text/html");
    LoadURL("https://example.com/opacity.html");
    request.Complete(R"HTML(
      <!DOCTYPE html>
      <style>
        body { margin: 0; height: 12000px; }
        @keyframes fade { from { opacity: .2; } to { opacity: .9; } }
        #target { position: absolute; left: 32px; top: 64px;
                  width: 150px; height: 80px; background: green;
                  animation: fade 60s infinite; will-change: opacity; }
      </style>
      <div id="container"><div id="target">Animated content</div></div>
      <div id="sibling">Independent paint</div>
    )HTML");
    Compositor().BeginFrame();
  }

  cc::PropertyTrees& Trees() {
    return *GetDocument().View()->RootCcLayer()->layer_tree_host()->property_trees();
  }

  void AssertRealOpacityAnimation(Document& document) {
    auto* target = document.getElementById(AtomicString("target"));
    ASSERT_TRUE(target);
    ASSERT_TRUE(target->GetLayoutObject());
    const auto* properties =
        target->GetLayoutObject()->FirstFragment().PaintProperties();
    ASSERT_TRUE(properties);
    ASSERT_TRUE(properties->Effect());
    ASSERT_TRUE(properties->Effect()->HasActiveOpacityAnimation());
    effect_id_ = properties->Effect()->GetCompositorElementId();
    const auto* node = Trees().effect_tree().FindNodeFromElementId(effect_id_);
    ASSERT_TRUE(node);
    ASSERT_TRUE(node->has_potential_opacity_animation);
  }

  void AssertRealOpacityAnimation() {
    AssertRealOpacityAnimation(GetDocument());
  }

  Document* LoadAnimatedFrameScene() {
    ResizeView(gfx::Size(360, 800));
    SimRequest main("https://example.com/frame.html", "text/html");
    SimRequest child("https://other.example.com/opacity.html", "text/html");
    LoadURL("https://example.com/frame.html");
    main.Complete(R"HTML(
      <!DOCTYPE html>
      <style>body { margin: 0; height: 12000px; }</style>
      <iframe id="frame" src="https://other.example.com/opacity.html"
              width="300" height="200"></iframe>
      <div id="sibling">Independent paint</div>
    )HTML");
    child.Complete(R"HTML(
      <!DOCTYPE html>
      <style>
        @keyframes fade { from { opacity: .2; } to { opacity: .9; } }
        #target { width: 150px; height: 80px; background: green;
                  animation: fade 60s infinite; will-change: opacity; }
      </style>
      <div id="target">Animated child frame</div>
    )HTML");
    Compositor().BeginFrame();
    auto* iframe = To<HTMLIFrameElement>(
        GetDocument().getElementById(AtomicString("frame")));
    return iframe->contentDocument();
  }

  void MutateAndPaint(const char* source) {
    ClassicScript::CreateUnspecifiedScript(String::FromUTF8(source))
        ->RunScript(GetDocument().domWindow());
    Compositor().BeginFrame();
  }

  cc::ElementId effect_id_;
};

TEST_F(IpTestOpacityLifecycleTest, OrdinaryLiveAnimationPaintRebuild) {
  LoadAnimatedScene();
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation());
  const int sequence = Trees().sequence_number();
  MutateAndPaint(
      "document.getElementById('container').style.transform='translateX(1px)'");
  EXPECT_GT(Trees().sequence_number(), sequence);
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation());
}

TEST_F(IpTestOpacityLifecycleTest, DetachedAnimatedElementWithRetainedReference) {
  LoadAnimatedScene();
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation());
  MutateAndPaint(
      "window.retainedTarget=document.getElementById('target');"
      "window.retainedTarget.remove();"
      "document.getElementById('sibling').style.transform='translateX(1px)'");
  EXPECT_FALSE(Trees().effect_tree().FindNodeFromElementId(effect_id_));
}

TEST_F(IpTestOpacityLifecycleTest, DisplayNoneDuringLiveOpacityAnimation) {
  LoadAnimatedScene();
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation());
  MutateAndPaint(
      "document.getElementById('target').style.display='none';"
      "document.getElementById('sibling').style.transform='translateX(1px)'");
  EXPECT_FALSE(Trees().effect_tree().FindNodeFromElementId(effect_id_));
}

TEST_F(IpTestOpacityLifecycleTest, HiddenAnimatedElementThenVisibleAgain) {
  LoadAnimatedScene();
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation());
  MutateAndPaint(
      "document.getElementById('target').style.visibility='hidden';"
      "document.getElementById('sibling').style.transform='translateX(1px)'");
  MutateAndPaint("document.getElementById('target').style.visibility='visible'");
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation());
}

TEST_F(IpTestOpacityLifecycleTest, AnimatedContentOutsideViewportThenRestored) {
  LoadAnimatedScene();
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation());
  MutateAndPaint(
      "window.scrollTo(0,8000);"
      "document.getElementById('sibling').style.transform='translateX(1px)'");
  MutateAndPaint("window.scrollTo(0,0)");
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation());
}

TEST_F(IpTestOpacityLifecycleTest, OffscreenAnimatedCrossOriginFrame) {
  Document* child = LoadAnimatedFrameScene();
  ASSERT_TRUE(child);
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation(*child));
  ASSERT_FALSE(child->View()->ShouldThrottleRenderingForTest());
  MutateAndPaint(
      "document.getElementById('frame').style.cssText="
      "'position:absolute;left:4000px;top:4000px';");
  GetDocument().View()->UpdateAllLifecyclePhasesForTest();
  ASSERT_TRUE(child->View()->ShouldThrottleRenderingForTest());
  const int sequence = Trees().sequence_number();
  MutateAndPaint(
      "document.getElementById('sibling').style.transform='translateX(1px)'");
  EXPECT_GT(Trees().sequence_number(), sequence);
  ASSERT_TRUE(child->View()->ShouldThrottleRenderingForTest());
  MutateAndPaint("document.getElementById('frame').style.cssText=''");
  GetDocument().View()->UpdateAllLifecyclePhasesForTest();
  ASSERT_FALSE(child->View()->ShouldThrottleRenderingForTest());
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation(*child));
}

TEST_F(IpTestOpacityLifecycleTest, DisplayNoneAnimatedCrossOriginFrame) {
  Document* child = LoadAnimatedFrameScene();
  ASSERT_TRUE(child);
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation(*child));
  ASSERT_FALSE(child->View()->ShouldThrottleRenderingForTest());
  MutateAndPaint("document.getElementById('frame').style.display='none'");
  GetDocument().View()->UpdateAllLifecyclePhasesForTest();
  ASSERT_TRUE(child->View()->ShouldThrottleRenderingForTest());
  const int sequence = Trees().sequence_number();
  MutateAndPaint(
      "document.getElementById('sibling').style.transform='translateX(1px)'");
  EXPECT_GT(Trees().sequence_number(), sequence);
  ASSERT_TRUE(child->View()->ShouldThrottleRenderingForTest());
  MutateAndPaint("document.getElementById('frame').style.display=''");
  GetDocument().View()->UpdateAllLifecyclePhasesForTest();
  ASSERT_FALSE(child->View()->ShouldThrottleRenderingForTest());
  ASSERT_NO_FATAL_FAILURE(AssertRealOpacityAnimation(*child));
}

}  // namespace blink
