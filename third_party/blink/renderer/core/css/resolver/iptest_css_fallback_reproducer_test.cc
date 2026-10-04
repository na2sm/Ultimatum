// Copyright 2026 The Chromium Authors
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "testing/gtest/include/gtest/gtest.h"
#include "third_party/blink/renderer/core/css/css_computed_style_declaration.h"
#include "third_party/blink/renderer/core/css/css_property_names.h"
#include "third_party/blink/renderer/core/dom/element.h"
#include "third_party/blink/renderer/core/testing/core_unit_test_helper.h"

namespace blink {

class IpTestCssFallbackTest : public RenderingTest {
 protected:
  String Computed(const String& declarations,
                  CSSPropertyID property = CSSPropertyID::kWidth) {
    SetBodyInnerHTML(String("<style>#target {") + declarations +
                     "}</style><div id='target'></div>");
    UpdateAllLifecyclePhasesForTest();
    auto* target = GetDocument().getElementById(AtomicString("target"));
    CHECK(target);
    return MakeGarbageCollected<CSSComputedStyleDeclaration>(target)
        ->GetPropertyValue(property);
  }
};

// These controls distinguish initial declaration parsing from substitution.
TEST_F(IpTestCssFallbackTest, OrdinaryDeclarationWithComments) {
  EXPECT_EQ("12px", Computed("width: /* leading */ 12px /* trailing */;"));
}

TEST_F(IpTestCssFallbackTest, DirectFallbackWithComments) {
  EXPECT_EQ("12px", Computed("width: var(--missing, 12px/**/);"));
}

TEST_F(IpTestCssFallbackTest, EmptySubstitutionWithoutSlash) {
  EXPECT_EQ("12px", Computed("--empty: ;"
                             "width: var(--missing, var(--empty) 12px);"));
}

// Empty substitution introduces leading whitespace only AFTER tokenization.
// A comment or slash selects the parser's general trailing-trim path.
TEST_F(IpTestCssFallbackTest, EmptySubstitutionWithTrailingComment) {
  EXPECT_EQ("12px", Computed("--empty: ;"
                             "width: var(--missing, var(--empty) 12px/**/);"));
}

TEST_F(IpTestCssFallbackTest, EmptySubstitutionWithNestedComment) {
  EXPECT_EQ("12px", Computed("--empty: ;"
                             "width: var(--missing, var(--empty) "
                             "var(--also-missing, 12px/**/));"));
}

TEST_F(IpTestCssFallbackTest, EmptySubstitutionBeforeQuotedSlash) {
  EXPECT_EQ("\"a/b\"", Computed("--empty: ;"
                                  "--result: var(--missing, var(--empty) \"a/b\");"
                                  "content: var(--result);",
                                  CSSPropertyID::kContent));
}

TEST_F(IpTestCssFallbackTest, WhitespaceSeparatesTokensAfterEmptySubstitution) {
  EXPECT_EQ("12px 14px", Computed("--empty: ;"
                                 "--result: 12px var(--missing, "
                                 "var(--empty) 14px/**/);"
                                 "margin: var(--result);",
                                 CSSPropertyID::kMargin));
}

TEST_F(IpTestCssFallbackTest, EmptyFallbackWithOnlyWhitespaceAndComment) {
  EXPECT_EQ("12px", Computed("--empty: ;"
                             "--result: 12px var(--missing, var(--empty) /**/);"
                             "width: var(--result);"));
}

}  // namespace blink
