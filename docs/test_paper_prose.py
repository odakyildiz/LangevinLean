"""Regressions for separating mathematical exposition from source notes."""
import unittest

from full_proofs import mathematical_prose, paper_prose
from verify_exposition import reader_issues


class PaperProseTests(unittest.TestCase):
    def test_nested_source_note_does_not_remove_neighboring_proof(self):
        value = ('<p>Assume strong convexity.</p>'
                 '<p class="formal-note">Lean <strong>source <code>foo</code></strong>'
                 '<br>correspondence.</p><p>The quadratic lower bound follows.</p>')
        self.assertEqual(mathematical_prose(value),
                         '<p>Assume strong convexity.</p><p>The quadratic lower bound follows.</p>')

    def test_strict_inequality_inside_math_is_not_parsed_as_html(self):
        formula = r'\[0<h<2/L,\qquad a_{n+1}\le q a_n+b.\]'
        value = '<p>Take a stable step.</p>' + formula + '<p>Sum the recurrence.</p>'
        self.assertEqual(mathematical_prose(value), value)
        self.assertIn(formula, paper_prose(value))
        self.assertIn('Sum the recurrence.', paper_prose(value))

    def test_unmarked_mathematical_hypotheses_are_never_heuristically_removed(self):
        value = '<p>A probability kernel preserves total mass.</p>'
        self.assertEqual(mathematical_prose(value), value)

    def test_unclosed_source_note_cannot_silently_swallow_a_proof(self):
        with self.assertRaisesRegex(ValueError, 'Unclosed formal-note'):
            mathematical_prose('<p class="formal-note">Source note <strong>unfinished')

    def test_entities_and_formulas_survive_source_note_removal(self):
        value = (r'<p>Let \(a&lt;b\).</p><aside class="formal-note">'
                 r'\(c&lt;d\) is represented by a declaration.</aside>'
                 r'<p>Then \(a\le b\).</p>')
        rendered = paper_prose(value)
        self.assertIn(r'\(a<b\)', rendered)
        self.assertIn(r'\(a\le b\)', rendered)
        self.assertNotIn('declaration', rendered)
        self.assertNotIn('c<d', rendered)

    def test_paper_checker_distinguishes_notation_from_source_identifiers(self):
        self.assertEqual(reader_issues(r'<p>Use \(mL\|x-y\|^2\) and \(\operatorname{Var}(X)\).</p>'), [])
        self.assertTrue(reader_issues(r'<p>Use \(\operatorname{gibbsMeasure}(U)\).</p>'))
        self.assertTrue(reader_issues(r'<p>Use \(\operatorname{some_theorem}(x)\).</p>'))
        self.assertTrue(reader_issues(r'<p>Use \(\texttt{theorem}\).</p>'))
        self.assertTrue(reader_issues('<p>Apply <code>some_theorem</code>.</p>'))
        self.assertTrue(reader_issues('<p>lean prints the axiom dependencies.</p>'))
        self.assertTrue(reader_issues(r'<p>Use \(\operatorname{ennreal}(x)\).</p>'))
        self.assertTrue(reader_issues('<p>The Implementation uses a namespace.</p>'))
        self.assertTrue(reader_issues('<p>Apply brownian euler noise pullback.</p>'))
        self.assertTrue(reader_issues('<p>The product-source modules derive the premise.</p>'))
        self.assertTrue(reader_issues('<p>Use the wasserstein2 definition.</p>'))
        self.assertEqual(reader_issues('<p class="formal-note">Apply <code>some_theorem</code> in Lean.</p>'), [])


if __name__ == '__main__':
    unittest.main()
