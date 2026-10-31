#!/usr/bin/env python3
"""Check source-versus-extra hypothesis presentation across the theorem entries."""
from html.parser import HTMLParser
import json
from pathlib import Path
import unittest

from average_content import LAPLACIAN
from entropy_content import IPLA_STATEMENT, ULA_STATEMENT
from kinetic_overviews import KINETIC_CONFIG
from site_content import CONFIG, project_document

ROOT = Path(__file__).resolve().parents[1]


class AssumptionText(HTMLParser):
    """Collect only text explicitly marked as an extra assumption."""
    def __init__(self, source):
        super().__init__()
        self.stack = []
        self.extra = []
        self.feed(source)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        marked = (attrs.get('data-assumption-kind') == 'added' or
                  'added-assumption' in attrs.get('class', '').split())
        inherited = self.stack[-1][1] if self.stack else False
        if tag not in ('br', 'hr', 'img', 'input', 'meta', 'link'):
            self.stack.append((tag, marked or inherited))

    def handle_endtag(self, tag):
        for i in range(len(self.stack) - 1, -1, -1):
            if self.stack[i][0] == tag:
                del self.stack[i:]
                break

    def handle_data(self, data):
        if self.stack and self.stack[-1][1]:
            self.extra.append(data)

    @property
    def text(self):
        return ''.join(self.extra)


class ExtraAssumptionTests(unittest.TestCase):
    def test_corrected_kinetic_simplification_marks_its_new_dimension_premise(self):
        result = next(result for result in KINETIC_CONFIG['KineticLangevin']['results']
                      if result['name'] == 'klmc2_wasserstein_bound')
        self.assertIn(r'\(p\ge2\)', AssumptionText(result['body']).text)

    def test_optional_printed_budget_marks_the_extra_curvature_comparison(self):
        result = next(result for result in KINETIC_CONFIG['KineticLangevin']['results']
                      if result['name'] == 'secondOrderTailFree_iterationCount_conditionNumber')
        marked = AssumptionText(result['body']).text
        self.assertIn(r'\(M(1-p^{-1/3})\le M_2^{2/3}\)', marked)
        self.assertIn(r'\(\rho\ge\kappa\)', marked)
        # The corrected max-condition-number theorem itself needs no such comparison.
        self.assertNotIn(r'R=\max', marked)

    def test_new_particle_entropy_extension_identifies_its_functional_hypotheses(self):
        marked = AssumptionText(IPLA_STATEMENT).text
        self.assertIn('lifted target satisfies the logarithmic Sobolev inequality', marked)
        self.assertIn(r'\(H_{\Pi_N}(\mu_0)<\infty\)', marked)
        self.assertIn(r'\(\beta_N=N\alpha\)', marked)
        self.assertNotIn('gradient', marked)

    def test_paper_hypotheses_are_not_misclassified_as_extra(self):
        # VW19 already assumes its LSI and finite initial KL. The AverageLMC
        # source's Laplacian theorem already assumes C3 and its Laplacian bound.
        self.assertIn(r'\(f\in C^3', LAPLACIAN)
        self.assertIn(r'\|\nabla\Delta f(x)\|^2\le M_\Delta^2p', LAPLACIAN)
        for body in (ULA_STATEMENT, LAPLACIAN):
            self.assertEqual(AssumptionText(body).text, '')
        for key in ('UnadjustedLangevin', 'IPLA', 'ProximalLangevin', 'KIPLMC'):
            for result in CONFIG[key]['results']:
                with self.subTest(entry=key, theorem=result['name']):
                    self.assertEqual(AssumptionText(result['body']).text, '')

    def test_kinetic_supporting_proofs_keep_the_same_classification(self):
        notes = json.loads((ROOT/'KineticLangevin/exposition/module_notes.json').read_text())
        for name in ('KineticLangevin/CanonicalKLMC2.lean',
                     'KineticLangevin/SecondOrderRecurrence.lean'):
            self.assertIn(r'\(p\ge2\)', AssumptionText(notes[name]['steps'][2]['body']).text)
        marked = AssumptionText(notes['KineticLangevin/ConditionNumber.lean']['steps'][5]['body']).text
        self.assertIn(r'\(\kappa\le\rho\)', marked)

    def test_archived_particle_entropy_states_the_same_extra_assumptions(self):
        archive = json.loads((ROOT/'IPLA/LSI/exposition/chapters.json').read_text())
        marked = AssumptionText(archive['sections'][0]['steps'][0]['body']).text
        self.assertIn('logarithmic Sobolev inequality', marked)
        self.assertIn(r'\(H_0=H_{\Pi_N}(\mu_0)<\infty\)', marked)
        linear = AssumptionText(archive['sections'][0]['steps'][2]['body']).text
        self.assertIn(r'\(\beta=N\alpha\)', linear)

    def test_homepage_extra_assumptions_have_the_shared_marker(self):
        body = project_document({})
        marked = AssumptionText(body).text
        self.assertIn('R1–R7', marked)
        self.assertIn('R1–R3', marked)
        self.assertIn('Entropy extension', marked)
        self.assertIn('simplified KLMC2', marked)
        self.assertNotIn('added regularity', body.lower())


if __name__ == '__main__':
    unittest.main()
