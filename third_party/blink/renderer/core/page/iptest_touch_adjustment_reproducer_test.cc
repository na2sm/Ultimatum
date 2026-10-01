// Copyright 2026 The Chromium Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "testing/gtest/include/gtest/gtest.h"
#include "third_party/blink/public/common/input/web_gesture_event.h"
#include "third_party/blink/renderer/core/frame/local_frame.h"
#include "third_party/blink/renderer/core/frame/local_frame_view.h"
#include "third_party/blink/renderer/core/input/event_handler.h"
#include "third_party/blink/renderer/core/page/page.h"
#include "third_party/blink/renderer/core/testing/core_unit_test_helper.h"

namespace blink {

class IpTestTouchAdjustmentTest : public RenderingTest {
 protected:
  WebGestureEvent Tap() {
    WebGestureEvent tap(WebInputEvent::Type::kGestureTap,
                        WebInputEvent::kNoModifiers, base::TimeTicks::Now(),
                        WebGestureDevice::kTouchscreen);
    tap.SetPositionInWidget(gfx::PointF(20, 20));
    tap.SetPositionInScreen(gfx::PointF(20, 20));
    tap.SetFrameScale(1);
    tap.data.tap.width = 5;
    tap.data.tap.height = 5;
    tap.data.tap.tap_count = 1;
    return tap;
  }

  void ThinTarget() {
    SetBodyInnerHTML(R"HTML(
      <style>body { margin: 0; }
      button { position: absolute; left: 12px; top: 0; width: .5px;
               height: 60px; border: 0; padding: 0; }</style>
      <button id="target" aria-label="thin target"></button>
    )HTML");
    GetPage().SetPageScaleFactor(1.3f);
  }
};

TEST_F(IpTestTouchAdjustmentTest, RoundedCandidateStaysInsideActualTapRect) {
  ThinTarget();
  auto& frame = *GetDocument().GetFrame();
  const auto tap = Tap();
  const PhysicalSize size =
      GetHitTestRectForAdjustment(frame, PhysicalSize(5, 5));
  PhysicalOffset top_left =
      PhysicalOffset::FromPointFRound(tap.PositionInRootFrame());
  top_left -= PhysicalOffset(LayoutUnit(size.width * .5f),
                             LayoutUnit(size.height * .5f));
  HitTestLocation location(PhysicalRect(top_left, size));
  ASSERT_GT(top_left.left.ToFloat(), 12);
  ASSERT_LT(top_left.left.ToFloat(), 12.5f);
  auto& handler = frame.GetEventHandler();
  const auto hit = handler.HitTestResultAtLocation(
      location, HitTestRequest::kReadOnly | HitTestRequest::kListBased);
  gfx::Point adjusted;
  Node* node = nullptr;
  ASSERT_TRUE(handler.BestNodeForHitTestResult(
      TouchAdjustmentCandidateType::kClickable, location, hit, adjusted, node));
  ASSERT_EQ(node, GetDocument().getElementById(AtomicString("target")));
  EXPECT_TRUE(location.ContainsPoint(
      gfx::PointF(frame.View()->ConvertFromRootFrame(adjusted))))
      << "Adjusted integer point escaped the fractional tap area: "
      << adjusted.ToString();
}

TEST_F(IpTestTouchAdjustmentTest, FullGestureCallerPreservesFractionalTapBounds) {
  ThinTarget();
  const auto target =
      GetDocument().GetFrame()->GetEventHandler().TargetGestureEvent(Tap(), true);
  EXPECT_EQ(target.InnerNode(), GetDocument().getElementById(AtomicString("target")));
}

TEST_F(IpTestTouchAdjustmentTest, OrdinaryTargetControl) {
  SetBodyInnerHTML(R"HTML(
    <style>body { margin: 0; } button { width: 60px; height: 60px; }</style>
    <button id="target">Accept</button>
  )HTML");
  GetPage().SetPageScaleFactor(1.3f);
  const auto target =
      GetDocument().GetFrame()->GetEventHandler().TargetGestureEvent(Tap(), true);
  EXPECT_EQ(target.GetHitTestResult().InnerElement(),
            GetDocument().getElementById(AtomicString("target")));
}

}  // namespace blink
