#!/usr/bin/env python3
"""Regressions for complete PBGSO theorem contracts and rendered excerpts.

Named arguments and result-type lets contain Lean's assignment token without
starting the proof. These cases exercise the original screenshot failure,
including the real native Theorem 4 and projected spectral criterion.
"""
import importlib.util
from pathlib import Path
import unittest

from build_pbgso import exact_header, header_lines, header_text, pbgso_declarations
from verify_site import Page

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('verify_pbgso_headers', ROOT/'scripts/verify-pbgso.py')
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)


class CompleteHeaderTests(unittest.TestCase):
    def statement(self, source, name='complete'):
        declaration = pbgso_declarations(source)[name]
        return declaration, header_text(source, declaration)

    def test_named_argument_does_not_remove_later_hypotheses_or_conclusion(self):
        source = '''theorem complete
    (U : Solution (J := Fin N))
    (hregular : Regular U)
    (hvariance : Variance U ≤ V) :
    error U ≤ constant V := by
  exact proved_bound U hregular hvariance
'''
        declaration, header = self.statement(source)
        self.assertEqual(declaration['marker'], 5)
        self.assertIn('(J := Fin N)', header)
        self.assertIn('(hvariance : Variance U ≤ V)', header)
        self.assertTrue(header.endswith('error U ≤ constant V'))
        self.assertNotIn('exact proved_bound', header)

    def test_result_type_lets_and_named_arguments_belong_to_the_statement(self):
        source = '''theorem complete :
    let ρ := min (rate (a := a)) (rate (a := x))
    let κ := ρ + 1
    0 < ρ ∧ Bound κ := by
  exact spectral_bound
'''
        declaration, header = self.statement(source)
        self.assertEqual(declaration['marker'], 4)
        self.assertIn('let ρ := min', header)
        self.assertIn('let κ := ρ + 1', header)
        self.assertTrue(header.endswith('0 < ρ ∧ Bound κ'))

    def test_same_line_named_argument_keeps_its_exact_column(self):
        source = 'theorem complete : Bound (seed (J := Fin N)) := by\n  exact proof\n'
        declaration, header = self.statement(source)
        self.assertEqual(declaration['marker_column'], source.splitlines()[0].rfind(':='))
        self.assertEqual(header, 'theorem complete : Bound (seed (J := Fin N))')

    def test_comments_strings_and_all_binder_delimiters_are_ignored(self):
        source = '''theorem complete (h : P ":= by") /- := /- nested := -/ -/
    (r : R {field := 1} [value (i := 2)]) :
    Bound ⟨value (i := 3), h⟩ := by -- := is not a second proof
  exact proof
'''
        declaration, header = self.statement(source)
        self.assertEqual(declaration['marker'], 3)
        self.assertIn('P ":= by"', header)
        self.assertIn('{field := 1}', header)
        self.assertTrue(header.endswith('Bound ⟨value (i := 3), h⟩'))
        self.assertNotIn('not a second proof', header)

    def test_proof_term_need_not_start_with_by(self):
        source = 'theorem complete : Bound (f (n := 2)) := proved (n := 2)\n'
        _, header = self.statement(source)
        self.assertEqual(header, 'theorem complete : Bound (f (n := 2))')

    def test_namespace_disambiguation_does_not_change_original_columns(self):
        # The two genuine declarations share a short name. The first parser
        # key is qualified, but source-column offsets must remain unmodified.
        source = '''namespace Alpha
theorem complete : Bound (f (i := 0)) := proof
end Alpha
namespace Beta
theorem complete : Bound (f (i := 1)) := proof
end Beta
'''
        parsed = pbgso_declarations(source)
        self.assertIn('Alpha.complete', parsed)
        self.assertTrue(header_text(source, parsed['Alpha.complete']).endswith('Bound (f (i := 0))'))
        self.assertTrue(header_text(source, parsed['complete']).endswith('Bound (f (i := 1))'))

    def test_rendered_excerpt_contains_the_whole_header_and_no_proof(self):
        source = '''theorem complete (h : Bound (f (J := Fin N))) :
    Bound (g (J := Fin N)) := by
  exact proof h
'''
        path = 'PBGSO/HeaderFixture.lean'
        parsed = {path: pbgso_declarations(source)}
        rendered = exact_header(path, 'complete', {path: source}, parsed,
                                'PBGSO/exposition/index.html')
        page = Page(); page.feed(rendered)
        block = next(block for block in page.blocks if block['data-role'] == 'statement')
        self.assertEqual(block['lines'], header_lines(source, parsed[path]['complete']))
        self.assertIn('Bound (g (J := Fin N))', '\n'.join(block['lines']))
        self.assertNotIn('exact proof', '\n'.join(block['lines']))

    def test_fidelity_verifier_rejects_the_old_truncated_named_argument_pane(self):
        source = '''theorem complete
    (U : Solution (J := Fin N))
    (h : Regular U) :
    error U ≤ constant := by
  exact proof
'''
        path = 'PBGSO/HeaderFixture.lean'
        parsed = {path: pbgso_declarations(source)}
        block = {'data-source': path, 'data-declaration': 'complete',
                 'data-role': 'statement', 'data-start': '1', 'data-end': '2'}
        with self.assertRaisesRegex(AssertionError, 'Truncated theorem header'):
            VERIFY.expected_source_excerpt(block, {path: source}, parsed, 'fixture.html')
        block['data-end'] = '4'
        self.assertEqual(VERIFY.expected_source_excerpt(block, {path: source}, parsed, 'fixture.html'),
                         header_lines(source, parsed[path]['complete']))

    def test_real_theorem4_contains_all_assumptions_and_the_final_error_bound(self):
        source = (ROOT/'PBGSO/RawConstructedParticleParameter.lean').read_text()
        _, header = self.statement(source, 'original_parameter_bound_constant')
        self.assertGreater(len(header.splitlines()), 45)
        for hypothesis in ('huniqueU', 'hOptimizer', 'hVar', 'hinit'):
            self.assertIn(hypothesis, header)
        self.assertIn('Real.sqrt (∫ ω', header)
        self.assertIn('optimizerLawDistance', header)
        self.assertTrue(header.endswith('(1-Real.exp (-ρ*T))'))
        self.assertNotIn('have hVF', header)

    def test_real_projected_criterion_retains_let_rate_and_final_conjunction(self):
        source = (ROOT/'PBGSO/ProjectedFiniteWork.lean').read_text()
        _, header = self.statement(source, 'canonical_projected_source_criterion_finite')
        self.assertIn('let ρ := min', header)
        self.assertIn('generalizedMinimum hDOpt', header)
        self.assertIn('generalizedMinimum hDSam', header)
        self.assertIn('0 < ρ ∧ TwistedJointMonotonicity', header)
        self.assertTrue(header.endswith('(canonicalGeometry DOpt DSam hDOpt hDSam)'))
        self.assertNotIn('have h :=', header)


class ProseMathVerificationTests(unittest.TestCase):
    def test_raw_inline_math_in_prose_is_rejected(self):
        with self.assertRaisesRegex(AssertionError, 'Unrendered math'):
            VERIFY.verify_prose_math(r'<p>Assume \(x > 0\).</p>', 'fixture.html')

    def test_raw_display_math_in_prose_is_rejected(self):
        with self.assertRaisesRegex(AssertionError, 'Unrendered math'):
            VERIFY.verify_prose_math(r'<div>\[x > 0\]</div>', 'fixture.html')

    def test_valid_katex_linebreak_followed_by_parenthesis_is_accepted(self):
        html = r'''<p>A rendered formula follows.</p><span class="katex">
<span class="katex-mathml"><math><semantics><mrow><mi>x</mi></mrow>
<annotation encoding="application/x-tex">\begin{aligned}x\\(\Pi_x)\end{aligned}</annotation>
</semantics></math></span><span class="katex-html"><span>x</span></span></span>'''
        VERIFY.verify_prose_math(html, 'fixture.html')

    def test_annotation_and_code_source_are_not_visible_prose(self):
        VERIFY.verify_prose_math(
            r'<annotation>\(source\)</annotation><code>\[code\]</code>'
            r'<pre><code>\(Lean string\)</code></pre>', 'fixture.html')

    def test_raw_math_after_katex_remains_rejected(self):
        with self.assertRaisesRegex(AssertionError, 'Unrendered math'):
            VERIFY.verify_prose_math(
                r'<span class="katex"><span>Rendered</span></span><p>\(raw\)</p>',
                'fixture.html')

    def test_inline_markup_does_not_hide_a_raw_math_opener(self):
        with self.assertRaisesRegex(AssertionError, 'Unrendered math'):
            VERIFY.verify_prose_math('<p>\\<em>(x > 0)</em></p>', 'fixture.html')

    def test_omitted_code_cannot_synthesize_a_false_math_opener(self):
        VERIFY.verify_prose_math('<p>Backslash \\<code>example</code>(words).</p>',
                                 'fixture.html')


if __name__ == '__main__':
    unittest.main()
