"""Regression checks for mathematical headings, prose and literal source."""
import unittest

from build_site import latex_heading
from math_notation import display_docstring, plain_math_text, render_prose_math
from verify_math_notation import markdown_notation_issues, notation_issues


class MathNotationTests(unittest.TestCase):
    def test_heading_preserves_latex_and_provides_readable_bookmark(self):
        value = latex_heading(r"Continuity in \(L^2\)")
        self.assertIn(r"\(L^2\)", value)
        self.assertNotIn(r"\textbackslash{}", value)
        self.assertIn("L²", value)

    def test_metadata_uses_plain_math_without_tex_commands(self):
        self.assertEqual(plain_math_text(r"Compatibility: \(\alpha\le L\)"),
                         "Compatibility: α≤ L")

    def test_visible_headings_render_but_attributes_and_source_are_protected(self):
        value = r'<h2 title="Use \(L^2\)">Use \(L^2\)</h2><pre><code>\(x\)</code></pre>'
        rendered = render_prose_math(value, lambda formula: "<span>MATH</span>")
        self.assertIn('title="Use L²"', rendered)
        self.assertIn("Use <span>MATH</span>", rendered)
        self.assertIn(r"<pre><code>\(x\)</code></pre>", rendered)

    def test_comparison_symbols_inside_math_do_not_become_html_tags(self):
        self.assertEqual(render_prose_math(r"<p>\(0<h<2/L\)</p>", lambda _: "FORMULA"),
                         "<p>FORMULA</p>")

    def test_katex_source_annotation_is_never_rendered_twice(self):
        value = r'<annotation encoding="application/x-tex">a\\(b)</annotation><p>\(x\)</p>'
        self.assertEqual(render_prose_math(value, lambda _: "MATH"),
                         r'<annotation encoding="application/x-tex">a\\(b)</annotation><p>MATH</p>')

    def test_extracted_comments_format_math_and_preserve_identifiers(self):
        tick = chr(96)
        value = display_docstring(f"An L² field, {tick}sqrt (2h){tick} and {tick}sourceLaw{tick}.")
        self.assertIn(r"\(L^{2}\)", value)
        self.assertIn(r"\(\sqrt{2h}\)", value)
        self.assertIn("<code>sourceLaw</code>", value)
        self.assertEqual(display_docstring("An L∞ bound"), r"An \(L^{\infty}\) bound")

    def test_audit_distinguishes_math_prose_from_katex_and_lean(self):
        self.assertTrue(notation_issues("<p>Assume C3 and h=1/M.</p>"))
        self.assertEqual(notation_issues('<span class="katex">α≤L</span><pre>h=1</pre>'), [])
        self.assertEqual(notation_issues("<p>Assumption C1 is used.</p>"), [])

    def test_audit_catches_ascii_formulas_and_mathematical_constants(self):
        for formula in ("n+1", "u-v", "V/N", "K>0", "T_t(Y_t)", "coefficient 6",
                        "1/sqrt(K)", "Dⱼf", "operator J", "constant Lpsi"):
            with self.subTest(formula=formula):
                self.assertTrue(notation_issues("<p>Use " + formula + ".</p>"))

    def test_printed_paper_labels_are_not_differentiability_classes(self):
        self.assertEqual(notation_issues('<h3><span class="paper-label">C1</span> — Source premise</h3>'), [])
        self.assertTrue(notation_issues('<p>Assume C1 differentiability.</p>'))

    def test_comment_formulas_are_formatted_as_complete_expressions(self):
        self.assertEqual(display_docstring("Use T_t(Y_t) for n+1 particles."),
                         r"Use \(T_t(Y_t)\) for \(n+1\) particles.")
        value = display_docstring("Bound 2 sqrt(V₀/(M*N))/m.")
        self.assertIn(r"\(\frac2m\sqrt{\frac{V_0}{MN}}\)", value)
        self.assertEqual(value.count(r"\("), 1)
        self.assertEqual(display_docstring("The 1/sqrt(K) rate."), r"The \(1/\sqrt{K}\) rate.")

    def test_markdown_audit_preserves_math_code_and_link_targets(self):
        tick = chr(96)
        value = f"Use $L^2$, {tick}h=1{tick} and [source](a/b).\n{tick*3}\nx=1\n{tick*3}"
        self.assertEqual(markdown_notation_issues(value), [])
        self.assertTrue(markdown_notation_issues("Assume x<y and C³ regularity."))


if __name__ == "__main__":
    unittest.main()
