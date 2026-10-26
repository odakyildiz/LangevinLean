#!/usr/bin/env python3
"""Regression examples for the PBGSO theorem-page presentation contract.

These deliberately remove reader-facing mathematical content or misclassify
stronger assumptions. A technically valid source catalog must not make those
regressions pass as a satisfactory landing page.
"""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('verify_pbgso', ROOT/'scripts/verify-pbgso.py')
VERIFY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFY)


class LandingContractTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        script = self.root/'scripts/check-example.py'
        script.parent.mkdir(parents=True)
        script.write_text('# fixture verification entry point\n')
        identifiers = ['thm:invariant_measure', 'thm:twisted_joint_strong_monotonicity',
                       'thm:finite_particle_error', 'thm:parameter_error_full']
        appendix = ['cor:separate_monotonicity', 'cor:projected_strong_convexity',
                    'unlabeled:mpgd_hypocoercivity', 'lemma:vol_preserve_ode']
        self.sources = {f'PBGSO/Appendix{i}.lean': '' for i in range(4)}
        self.audit = {
            'results': [dict(id=identifier, kind='theorem', number=str(i+1))
                        for i, identifier in enumerate(identifiers)] +
                       [dict(id=identifier, kind='corollary') for identifier in appendix],
            'formal_coverage': {identifier: dict(declarations=[dict(file=f'PBGSO/Appendix{i}.lean')])
                                for i, identifier in enumerate(appendix)},
        }
        paper = []
        for i, identifier in enumerate(identifiers):
            status = ('<div class="added-assumption" data-assumption-kind="added">'
                      'Explicit regularity: FiniteCouplingWork.</div>' if i == 1 else
                      '<p class="no-added-assumption">Added analytic assumptions: none.</p>')
            paper.append(f'<article data-source-result="{identifier}"><h3>Theorem {i+1} — Paper name</h3>'
                         '<p>Paper assumptions: the stated initial laws and model hypotheses.</p>' +
                         status + '<div class="katex">The mathematical conclusion.</div></article>')
        new = ''.join(f'<article data-new-theory="{label}"><h3>Theorem New {label} — Final bound</h3>'
                      '<p>Assumptions: the explicit primitive force conditions.</p>'
                      '<div class="katex">The final numerical parameter bound.</div></article>'
                      for label in 'AB')
        roadmap_links = ''.join(f'<a href="proofs/Appendix{i}.html#decl-final">Appendix result {i}</a>'
                                for i in range(4))
        self.roadmap_prose = ('The proof constructs the original processes, derives their comparison '
                             'and transports genuine couplings before taking the final infimum. ')*12
        self.overview = (
            '<main id="main"><a href="technical.html">Separate proof catalog</a>'
            '<section id="assumptions"><span class="interpretation-assumption" '
            'data-assumption-kind="interpretation">A2 means an actual stationary weak SDE.</span></section>' +
            '<section id="paper-theorems">'+''.join(paper)+'</section>' +
            '<section id="new-theory">'+new+'</section>' +
            '<section id="standalone-verification"><pre>python3 scripts/check-example.py '
            '--output /tmp/generated-proof\nlake env lean /tmp/generated-proof/NewA.lean</pre>'
            '<a href="../../standalone/PBGSO/NewA.lean">New A entry</a>'
            '<a href="../../standalone/PBGSO/NewB.lean">New B entry</a></section>'
            '<section id="proof-roadmap">'+self.roadmap_prose+roadmap_links+
            '<a href="technical.html">Complete details</a><a href="source_audit.md">Source audit</a>'
            '</section></main>')
        self.catalog = ''.join(f'<article class="module-card"><a href="proofs/Appendix{i}.html">'
                               f'Complete module {i}</a></article>' for i in range(4))

    def check(self, overview=None, catalog=None):
        VERIFY.verify_landing(self.overview if overview is None else overview,
                              self.catalog if catalog is None else catalog,
                              self.audit, self.sources, 'PBGSO/exposition/technical.html', self.root)

    def test_complete_page_accepts_generated_future_output(self):
        self.check()

    def test_source_link_does_not_replace_a_mathematical_statement(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace('class="katex"', 'class="not-mathematics"', 1))

    def test_missing_paper_theorem_is_rejected(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace('data-source-result="thm:finite_particle_error"', ''))

    def test_work_condition_cannot_be_downgraded_to_interpretation(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace('class="added-assumption" data-assumption-kind="added"',
                                             'class="interpretation-assumption" data-assumption-kind="interpretation"'))

    def test_per_result_addition_status_is_required(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace('class="no-added-assumption"', '', 1))

    def test_third_new_result_is_rejected(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace('</main>', '<article data-new-theory="C"></article></main>'))

    def test_catalog_cannot_return_to_landing(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace('</main>', '<article class="module-card"></article></main>'))

    def test_separate_catalog_still_requires_every_module(self):
        with self.assertRaises(AssertionError):
            self.check(catalog=self.catalog.replace('class="module-card"', 'class="missing"', 1))

    def test_nonexistent_repository_verification_command_is_rejected(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace('scripts/check-example.py', 'scripts/missing.py'))

    def test_short_link_list_is_not_a_substantial_roadmap(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace(self.roadmap_prose, 'Follow these links.'))

    def test_roadmap_must_finish_the_page(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace('</main>', '<section id="after">After roadmap.</section></main>'))

    def test_roadmap_must_include_each_appendix_result(self):
        with self.assertRaises(AssertionError):
            self.check(self.overview.replace('proofs/Appendix3.html#decl-final', 'source_audit.md'))


if __name__ == '__main__':
    unittest.main()
