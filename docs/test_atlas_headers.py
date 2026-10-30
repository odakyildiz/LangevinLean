#!/usr/bin/env python3
"""Keep exact mathematical contracts intact in ordinary atlas HTML and PDFs."""
import unittest

from build_site import ROOT, declaration_header, declarations
from lean_latex import escape_code, header_lines, statement_block, statement_lines
from verify_site import Page, verify_source_excerpt


class AtlasHeaderTests(unittest.TestCase):
    def assert_exported_header(self, source, expected, name='complete'):
        parsed = declarations(source)
        declaration = parsed[name]
        self.assertEqual('\n'.join(header_lines(source, declaration)), expected)
        self.assertEqual('\n'.join(statement_lines(source, declaration)), expected)
        path = 'AverageLMC/HeaderFixture.lean'
        html = declaration_header(path, name, {path: source}, {path: parsed},
                                  'AverageLMC/exposition/index.html')
        page = Page(); page.feed(html)
        blocks = [block for block in page.blocks if block['data-role'] == 'statement']
        self.assertEqual(len(blocks), 1)
        self.assertEqual('\n'.join(blocks[0]['lines']), expected)
        self.assertNotIn('exact proof', '\n'.join(blocks[0]['lines']))
        verify_source_excerpt(blocks[0], {path: source}, {path: parsed}, 'fixture.html')
        return declaration

    def test_result_type_let_remains_before_its_conclusion(self):
        source = '''theorem complete (x : ℝ) :
    let κ := x + 1
    0 ≤ κ ^ 2 := by
  exact proof
'''
        declaration = self.assert_exported_header(source, '''theorem complete (x : ℝ) :
    let κ := x + 1
    0 ≤ κ ^ 2''')
        self.assertEqual(declaration['marker'], 3)

    def test_absolute_value_line_does_not_start_an_equation_style_body(self):
        source = '''theorem complete (x : ℝ) :
    ∀ t : ℝ,
      |x + t| ≤ |x| + |t| := by
  exact proof
'''
        self.assert_exported_header(source, '''theorem complete (x : ℝ) :
    ∀ t : ℝ,
      |x + t| ≤ |x| + |t|''')

    def test_same_line_named_argument_keeps_its_exact_delimiter_column(self):
        source = 'theorem complete : Bound (seed (I := I)) := by\n  exact proof\n'
        declaration = self.assert_exported_header(source,
            'theorem complete : Bound (seed (I := I))')
        self.assertEqual(declaration['marker_column'], source.splitlines()[0].rfind(':='))

    def test_comments_and_string_literals_cannot_end_a_header(self):
        source = '''theorem complete (h : P ":= by") /- := /- nested := -/ -/
    (x : R {field := 1}) : Bound x := by
  exact proof
'''
        self.assert_exported_header(source, '''theorem complete (h : P ":= by") /- := /- nested := -/ -/
    (x : R {field := 1}) : Bound x''')

    def test_verifier_rejects_old_same_line_named_argument_truncation(self):
        source = 'theorem complete : Bound (seed (I := I)) := by\n  exact proof\n'
        path = 'AverageLMC/HeaderFixture.lean'
        parsed = {path: declarations(source)}
        block = {'data-source': path, 'data-start': '1', 'data-end': '1',
                 'data-role': 'statement', 'data-declaration': 'complete',
                 'lines': [source.splitlines()[0].split(':=', 1)[0].rstrip()]}
        with self.assertRaisesRegex(AssertionError, 'Altered source lines'):
            verify_source_excerpt(block, {path: source}, parsed, 'fixture.html')

    def test_verifier_rejects_incomplete_statement_range(self):
        source = ('theorem complete (x : ℝ) :\n    let κ := x + 1\n'
                  '    0 ≤ κ ^ 2 := by\n  exact proof\n')
        path = 'AverageLMC/HeaderFixture.lean'
        parsed = {path: declarations(source)}
        block = {'data-source': path, 'data-start': '1', 'data-end': '2',
                 'data-role': 'statement', 'data-declaration': 'complete',
                 'lines': source.splitlines()[:2]}
        with self.assertRaisesRegex(AssertionError, 'Truncated statement'):
            verify_source_excerpt(block, {path: source}, parsed, 'fixture.html')
        block['data-start'], block['data-end'] = '2', '3'
        with self.assertRaisesRegex(AssertionError, 'Truncated statement'):
            verify_source_excerpt(block, {path: source}, parsed, 'fixture.html')

    def test_long_theorem_statement_is_not_capped_before_its_conclusion(self):
        source = ('theorem complete\n' + ''.join(f'    (h{i} : True)\n' for i in range(90))
                  + '    : 0 ≤ (0 : ℝ) := by\n  exact proof\n')
        declaration = declarations(source)['complete']
        rows = statement_lines(source, declaration)
        self.assertEqual(len(rows), 92)
        self.assertEqual(rows[-1], '    : 0 ≤ (0 : ℝ)')
        pdf = statement_block('Fixture.lean', 'complete', source, declaration)
        self.assertIn('h89', pdf)
        self.assertIn(escape_code('0 ≤ (0 : ℝ)'), pdf)
        self.assertNotIn('further lines', pdf)

    def test_actual_variable_step_and_absolute_remainder_conclusions_survive(self):
        checks = [
            ('AverageLMC/Theorem.lean', 'lmc_variable_step', 'a / (κ +', 'let κ :='),
            ('AverageLMC/SGLDTheorem.lean', 'sgld_one_step_rms', 'h ^ 2 * p', 'let R :='),
            ('AverageLMC/CompactC2Taylor.lean', 'compactC2_secondOrderExpansion_remainder',
             'η * ‖v‖ ^ 2 + C * ‖v‖ ^ 3', None),
        ]
        for path, name, conclusion, local_binding in checks:
            with self.subTest(path=path, declaration=name):
                source = (ROOT / path).read_text()
                header = '\n'.join(statement_lines(source, declarations(source)[name]))
                self.assertIn(conclusion, header)
                if local_binding:
                    self.assertIn(local_binding, header)
                self.assertNotIn(':= by', header)


if __name__ == '__main__':
    unittest.main()
