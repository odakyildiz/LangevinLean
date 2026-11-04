#!/usr/bin/env python3
"""One regression contract for paper labels, citations, and extra assumptions.

Run normally for metadata and deliberately broken HTML fixtures.  ``--site``
additionally reads the eleven generated main pages without generating anything.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from html.parser import HTMLParser
from pathlib import Path
import re
import sys
import unittest
from urllib.parse import urlsplit

from paper_sources import (assumption_sections, correspondence_section,
                           result_notice, source_metadata)
from site_content import CONFIG

ROOT = Path(__file__).resolve().parents[1]
SITE = '--site' in sys.argv
if SITE:
    sys.argv.remove('--site')
EXTRA = re.compile(r'Extra A[1-9]\d*\Z')
PRINTED_RESULT = re.compile(r'(?:Theorem|Proposition|Lemma|Corollary) (?:[A-Z]\.)?\d+(?:\.\d+)*(?:\([a-z]\))?\Z')
SHARED = {'UnadjustedLangevin', 'UnadjustedLangevin/LSI', 'IPLA', 'IPLA/LSI',
          'ProximalLangevin', 'KineticLangevin', 'KIPLMC', 'AverageLMC', 'WassersteinMixing'}
# These expectations are independent of metadata and distinguish TeX identifiers
# from printed theorem counters.  Both kinetic wrappers have the same paper label.
EXPECTED_LABELS = {
    'WassersteinMixing': {'bias_bound': 'Theorem 1',
                         'convergence_bound': 'Corollary 1.1',
                         'accuracy_bound': 'Corollary 1.1'},
    'UnadjustedLangevin': {'dalalyan': 'Theorem 1(a)', 'dalalyan_large_step': 'Theorem 1(b)'},
    'UnadjustedLangevin/LSI': {'ula_kl_bound': 'Theorem 2'},
    'IPLA': {'theorem1': 'Theorem 1'},
    'ProximalLangevin': {'moreau_myipla_parameter_rms_original': 'Theorem 4.1',
                         'pipgla_parameter_rms_original': 'Theorem 4.2',
                         'moreau_mypgd_parameter_rms_original': 'Theorem B.1'},
    'KineticLangevin': {'kineticPositionLaw_wasserstein2Real_general': 'Theorem 1',
                        'kineticPositionLaw_wasserstein2_general': 'Theorem 1',
                        'wasserstein2_gibbs_general': 'Theorem 1',
                        'klmc_wasserstein_bound': 'Theorem 2',
                        'klmc2_wasserstein_bound_exact': 'Theorem 3',
                        'klmc2_wasserstein_bound': 'Theorem 3'},
    'KIPLMC': {'kipld_parameter_sampling_bound': 'Proposition 3',
               'kiplmc1_parameter_bound_independent': 'Theorem 1',
               'kiplmc2_parameter_paper_bound': 'Theorem 2',
               'parameter_secondMoment_le': 'Proposition 2',
               'kiplmc1Step_particle_velocity': 'Algorithm 1',
               'kiplmc2Step_velocity': 'Algorithm 2'},
    'AverageLMC': {'lmc_one_step': 'Theorem 1',
                   'lmc_constant_step_extended': 'Theorem 1',
                   'lmc_variable_step': 'Proposition 1',
                   'lmc_variable_step_extended_initial': 'Proposition 1',
                   'lmc_laplacian_extended': 'Theorem 2',
                   'sgld_constant_step_paper': 'Theorem 3'},
}
LATENT_LABELS = ['Proposition 2.1', 'Theorem 3.1', 'Theorem 3.2', 'Lemma A.1',
                 'Proposition A.2', 'Proposition C.2', 'Lemma C.3', 'Lemma C.4',
                 'Lemma C.5', 'Theorem C.6', 'Lemma C.8', 'Lemma C.9',
                 'Lemma C.10', 'Theorem C.11', 'Theorem C.12', 'Lemma C.14',
                 'Lemma C.15', 'Lemma C.16', 'Theorem C.17']
VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link',
        'meta', 'param', 'source', 'track', 'wbr'}


@dataclass
class Element:
    tag: str
    attrs: dict
    children: list = field(default_factory=list)
    parent: Element | None = None

    def elements(self):
        for child in self.children:
            if isinstance(child, Element):
                yield child
                yield from child.elements()

    def text(self):
        return ''.join(child.text() if isinstance(child, Element) else child
                       for child in self.children)

    def has_class(self, value):
        return value in self.attrs.get('class', '').split()

    def contains(self, node):
        while node:
            if node is self:
                return True
            node = node.parent
        return False


class Document(HTMLParser):
    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.root = Element('document', {})
        self.stack = [self.root]
        self.feed(source)
        self.nodes = list(self.root.elements())

    def handle_starttag(self, tag, attrs):
        node = Element(tag, dict(attrs), parent=self.stack[-1])
        self.stack[-1].children.append(node)
        if tag not in VOID:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.stack.pop()

    def handle_endtag(self, tag):
        for index in range(len(self.stack) - 1, 0, -1):
            if self.stack[index].tag == tag:
                del self.stack[index:]
                return

    def handle_data(self, data):
        self.stack[-1].children.append(data)

    def unique(self, identifier):
        matches = [node for node in self.nodes if node.attrs.get('id') == identifier]
        require(len(matches) == 1, f'Expected exactly one #{identifier}')
        return matches[0]

    def section(self, identifier):
        # Dedicated pages retain historical IDs and expose the standard ID as
        # an empty span inside the relevant section.
        node = self.unique(identifier)
        while node.tag != 'section' and node.parent:
            node = node.parent
        require(node.tag == 'section', f'#{identifier} must identify a section')
        return node


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def normalized(value):
    return ' '.join(value.split())


def source_link(href):
    parsed = urlsplit(href)
    return (parsed.scheme in {'http', 'https'} and bool(parsed.netloc)) or (
        not parsed.scheme and parsed.path.endswith('.html') and
        bool(re.fullmatch(r'L\d+', parsed.fragment)))


def has_citation(card):
    for node in [card, *card.elements()]:
        if node.has_class('source-citation') or node.has_class('statement-source'):
            if any(link.tag == 'a' and source_link(link.attrs.get('href', ''))
                   for link in [node, *node.elements()]):
                return True
    return False


def heading_label(card, expected, exact=False):
    headings = [node for node in card.elements() if node.tag == 'h3']
    require(bool(headings), f'Missing result/assumption heading for {expected}')
    text = normalized(headings[0].text())
    require(text == expected if exact else text == expected or text.startswith(expected + ' — '),
            f'Heading does not retain exact source label {expected}: {text}')


def validate_metadata(data, configs):
    require(set(data) == set(configs) == SHARED, 'Every shared page needs source metadata')
    for library, config in configs.items():
        record = data[library]
        labels = [extra['label'] for extra in record['extras']]
        require(labels == [f'Extra A{i}' for i in range(1, len(labels) + 1)],
                f'{library}: extra labels must be sequential Extra A1, Extra A2, etc.')
        require(all(EXTRA.fullmatch(label) for label in labels), f'{library}: malformed extra label')
        for assumption in record['assumptions']:
            require(assumption.get('label') and assumption.get('body'), f'{library}: incomplete paper assumption')
            require(assumption.get('location') and source_link(assumption.get('url', '')),
                    f'{library}: each original assumption needs a paper citation')
            require(not EXTRA.fullmatch(assumption['label']), f'{library}: extra in original assumptions')
        for result in config['results']:
            name = result['name']
            require(name in record['results'], f'{library}: missing correspondence for {name}')
            item = record['results'][name]
            require(item['status'] in {'proved', 'corrected', 'conditional', 'auxiliary', 'new'}, f'{library}: unknown proof status')
            if item['status'] in {'proved', 'corrected', 'conditional'}:
                require(PRINTED_RESULT.fullmatch(item['label']), f'{library}: original paper label required')
                require(item.get('location') and source_link(item.get('url', '')),
                        f'{library}: paper result needs a source citation')
            if item['status'] == 'conditional':
                require(bool(item.get('extras')), f'{library}: conditional result needs explicit extra assumptions')
            for label in item.get('extras', []):
                require(EXTRA.fullmatch(label) and label in labels,
                        f'{library}:{name}: unresolved extra assumption {label}')
            if name in EXPECTED_LABELS.get(library, {}):
                require(item['label'] == EXPECTED_LABELS[library][name],
                        f'{library}:{name}: incorrect printed paper label')
    require([a['label'] for a in data['KIPLMC']['assumptions'][:2]] == ['H1', 'H2'],
            'KIPLMC must retain printed H1/H2, not invented A1/A2')
    for name in ('lmc_constant_step_extended', 'lmc_laplacian_extended'):
        require(name in {r['name'] for r in configs['AverageLMC']['results']},
                'Average global results must show their source-exact extended endpoints')
        require(data['AverageLMC']['results'][name]['status'] == 'proved' and
                not data['AverageLMC']['results'][name].get('extras'),
                'Average extended global estimates must not impose unnecessary extra assumptions')


def original_assumptions(doc, section, expected):
    cards = [node for node in section.elements() if 'data-paper-assumption' in node.attrs]
    require([card.attrs['data-paper-assumption'] for card in cards] == expected,
            'Original assumptions must retain their exact source labels and order')
    for card in cards:
        label = card.attrs['data-paper-assumption']
        heading_label(card, label)
        require(has_citation(card), f'Original assumption {label} is missing its source citation')
        require(not card.has_class('added-assumption'), f'{label}: original assumption marked extra')
    return cards


def extra_cards(doc, expected, first_section, first_count=None):
    cards = []
    for node in doc.nodes:
        label = node.attrs.get('data-extra-assumption')
        if label is None and EXTRA.fullmatch(node.attrs.get('data-assumption-id', '')):
            label = node.attrs['data-assumption-id']
        if label is None:
            continue
        require(EXTRA.fullmatch(label), f'Extra assumption label must match Extra A<number>: {label}')
        cards.append((label, node))
    require([label for label, _ in cards] == expected,
            'Extra assumptions must appear exactly once with sequential Extra A labels')
    for index, (label, card) in enumerate(cards):
        heading_label(card, label)
        orange = card.has_class('added-assumption') or card.has_class('category-extra-assumption')
        if not orange:
            orange = any(child.has_class('added-assumption') for child in card.elements())
        require(orange, f'{label}: missing shared orange extra-assumption classification')
        if first_count is None or index < first_count:
            require(first_section.contains(card), f'{label}: outside the extra-assumptions section')
    return cards


def validate_shared_page(source, data, results):
    doc = Document(source)
    ledger = doc.section('paper-correspondence')
    assumptions = doc.section('paper-assumptions')
    extras = doc.section('extra-assumptions')
    original_assumptions(doc, assumptions, [a['label'] for a in data['assumptions']])
    extra_cards(doc, [a['label'] for a in data['extras']], extras)
    rows = [node for node in ledger.elements() if 'data-paper-result' in node.attrs]
    allowed = [(i, result, data['results'][result['name']])
               for i, result in enumerate(results, 1)
               if data['results'][result['name']]['status'] in {'proved', 'corrected', 'conditional'}]
    require(Counter(row.attrs['data-paper-result'] for row in rows) ==
            Counter(item['label'] for _, _, item in allowed),
            'Paper ledger must contain exactly the paper results; new/auxiliary results are excluded')
    allowed_targets = {f'#result-{index}' for index, _, _ in allowed}
    for row in rows:
        targets = {node.attrs.get('href') for node in row.elements() if node.tag == 'a' and
                   node.attrs.get('href', '').startswith('#result-')}
        require(len(targets) == 1 and targets <= allowed_targets,
                'Paper ledger links must resolve only to paper-result statements')
    for index, result in enumerate(results, 1):
        item = data['results'][result['name']]
        card = doc.unique(f'result-{index}')
        if item['status'] in {'proved', 'corrected', 'conditional'}:
            require(card.attrs.get('data-source-label') == item['label'], 'Result data-source-label differs from the original paper label')
            heading_label(card, item['label'], exact=True)
            require(has_citation(card), f'{item["label"]}: missing paper-result citation')
        else:
            require(not ledger.contains(card), 'New/auxiliary statement cannot be in the paper ledger')
        for label in item.get('extras', []):
            target = '#extra-a' + label.split('A')[-1]
            require(any(node.attrs.get('href') == target for node in card.elements()),
                    f'{item["label"]}: missing link to its extra assumption {label}')
    return doc


def validate_dedicated_page(source, library):
    doc = Document(source)
    ledger = doc.section('paper-correspondence')
    assumptions = doc.section('paper-assumptions')
    extras = doc.section('extra-assumptions')
    count = 5 if library == 'PBGSO' else 4
    original_assumptions(doc, assumptions, [f'A{i}' for i in range(1, count + 1)])
    if library == 'PBGSO':
        expected = [f'Theorem {i}' for i in range(1, 5)]
        extra_cards(doc, [f'Extra A{i}' for i in range(1, 6)], extras, first_count=3)
        attr = 'data-paper-result'
    else:
        expected = LATENT_LABELS
        extra_cards(doc, [f'Extra A{i}' for i in range(1, 15)], extras, first_count=7)
        attr = 'data-paper-correspondence'
    rows = [node for node in ledger.elements() if attr in node.attrs]
    require(Counter(node.attrs[attr] for node in rows) == Counter(expected),
            f'{library}: paper ledger must contain the exact original printed result labels')
    result_cards = [node for node in doc.nodes if node.attrs.get('data-source-result')]
    require(Counter(node.attrs.get('data-source-label') for node in result_cards) == Counter(expected),
            f'{library}: every paper result needs its exact data-source-label')
    for card in result_cards:
        label = card.attrs['data-source-label']
        heading_label(card, label)
        require(has_citation(card), f'{library}:{label}: missing result source citation')
    for node in doc.nodes:
        if node.tag in {'h2', 'h3'}:
            require(not re.match(r'\s*(?:R|N|V)\d+\b', node.text()),
                    'Public headings must use original labels or Extra A labels')
    return doc


class MetadataTests(unittest.TestCase):
    def test_all_shared_metadata(self):
        validate_metadata(source_metadata(), CONFIG)

    def test_source_theorem_counters_are_not_tex_identifiers(self):
        for path, expected in (
            ('papers/kinetic_Langevin/mainDR_dec_18.tex', ['th:1', 'th:3', 'th:4']),
            ('papers/Average_LMC/Arxiv_version_May_26.tex', ['th:1', 'th:3', 'th:sgld']),
        ):
            text = re.sub(r'(?m)(?<!\\)%.*$', '', (ROOT/path).read_text())
            labels = re.findall(r'\\begin\{theorem\}\s*\\label\{([^}]+)\}', text)
            self.assertEqual(labels, expected)
        self.assertIn(r'\renewcommand{\theassumptionaux}{H\arabic{assumptionaux}}',
                      (ROOT/'papers/KIPLMC/main.tex').read_text())

    def test_helper_cites_every_original_assumption_and_separates_extras(self):
        for library, data in source_metadata().items():
            with self.subTest(library=library):
                doc = Document(assumption_sections(library, lambda text: text))
                original_assumptions(doc, doc.section('paper-assumptions'),
                                     [row['label'] for row in data['assumptions']])
                extra_cards(doc, [row['label'] for row in data['extras']],
                            doc.section('extra-assumptions'))

    def test_new_and_auxiliary_results_are_excluded_from_helper_ledger(self):
        for library, data in source_metadata().items():
            results = CONFIG[library]['results']
            source = correspondence_section(library, results, lambda text: text)
            doc = Document(source)
            targets = {node.attrs.get('href') for node in doc.nodes if node.tag == 'a'}
            for i, result in enumerate(results, 1):
                if data['results'][result['name']]['status'] in {'new', 'auxiliary'}:
                    self.assertNotIn(f'#result-{i}', targets)

    def test_algorithm_notices_retain_the_paper_citation(self):
        for result in CONFIG['KIPLMC']['results']:
            record = source_metadata()['KIPLMC']['results'][result['name']]
            if record['status'] == 'auxiliary':
                source = result_notice('KIPLMC', result, lambda text: text)
                self.assertTrue(has_citation(Document(source).root))
                self.assertNotIn('not a numbered result', source)

    def test_wasserstein_results_use_original_assumptions_without_extra_inputs(self):
        data = source_metadata()['WassersteinMixing']
        self.assertEqual(data['extras'], [])
        for result in CONFIG['WassersteinMixing']['results'][:3]:
            record = data['results'][result['name']]
            self.assertEqual(record['status'], 'proved')
            self.assertEqual(record['extras'], [])
            notice = result_notice('WassersteinMixing', result, lambda text: text)
            self.assertIn('Paper statement proved', notice)
            self.assertNotIn('source realization pending', notice)
            self.assertNotIn('Conditional result proved', notice)
            self.assertNotIn('Corrected statement proved', notice)
            self.assertTrue(has_citation(Document(notice).root))


class SharedFixtureTests(unittest.TestCase):
    def setUp(self):
        self.data = dict(paper='average-lmc', assumptions=[dict(label='A1', title='Source condition',
            body='<p>Explicit source inequality.</p>', location='A1', url='https://example.org/paper')],
            extras=[dict(label='Extra A1', body='<p>The explicit added condition.</p>')],
            results={'paper': dict(label='Theorem 2.1', status='proved', extras=['Extra A1']),
                     'extra': dict(label='New result', status='new', extras=[])})
        self.results = [dict(name='paper'), dict(name='extra')]
        self.source = ('''<section id="paper-correspondence"><table><tr data-paper-result="Theorem 2.1">
<td><a href="#result-1">Statement</a></td></tr></table></section>
<section id="paper-assumptions"><article data-paper-assumption="A1"><h3>A1 — Source condition</h3>
<p class="source-citation"><a href="https://example.org/paper">Paper, A1</a></p></article></section>
<section id="extra-assumptions"><article data-extra-assumption="Extra A1" class="added-assumption"
id="extra-a1"><h3>Extra A1 — Added condition</h3></article></section>
<section id="main-results"><article id="result-1" data-source-label="Theorem 2.1"><h3>Theorem 2.1</h3>
<p class="source-citation"><a href="https://example.org/paper">Paper, Theorem 2.1</a></p>
<a href="#extra-a1">Extra A1</a></article></section>
<section id="additional-results"><article id="result-2" data-source-label="New result"><h3>New result</h3></article></section>''')

    def check(self, source=None):
        return validate_shared_page(self.source if source is None else source, self.data, self.results)

    def test_valid_standardized_fixture(self):
        self.check()

    def test_wrong_result_heading_fails(self):
        with self.assertRaisesRegex(AssertionError, 'exact source label'):
            self.check(self.source.replace('<h3>Theorem 2.1</h3>', '<h3>Theorem 3</h3>'))

    def test_wrong_data_label_fails(self):
        with self.assertRaisesRegex(AssertionError, 'data-source-label'):
            self.check(self.source.replace('data-source-label="Theorem 2.1"', 'data-source-label="Theorem 3"'))

    def test_missing_original_assumption_citation_fails(self):
        with self.assertRaisesRegex(AssertionError, 'missing its source citation'):
            self.check(self.source.replace('<p class="source-citation"><a href="https://example.org/paper">Paper, A1</a></p>', ''))

    def test_missing_result_citation_fails(self):
        with self.assertRaisesRegex(AssertionError, 'missing paper-result citation'):
            self.check(self.source.replace('<p class="source-citation"><a href="https://example.org/paper">Paper, Theorem 2.1</a></p>', ''))

    def test_extra_label_abbreviation_fails(self):
        with self.assertRaisesRegex(AssertionError, 'Extra A<number>'):
            self.check(self.source.replace('data-extra-assumption="Extra A1"', 'data-extra-assumption="R1"'))

    def test_extra_link_must_resolve(self):
        with self.assertRaisesRegex(AssertionError, 'missing link'):
            self.check(self.source.replace('href="#extra-a1"', 'href="#missing"'))

    def test_new_result_cannot_enter_paper_ledger(self):
        with self.assertRaisesRegex(AssertionError, 'new/auxiliary'):
            self.check(self.source.replace('</table>', '<tr data-paper-result="New result"><td><a href="#result-2">New</a></td></tr></table>'))


@unittest.skipUnless(SITE, 'Use --site after generating the main pages')
class GeneratedSiteTests(unittest.TestCase):
    def test_all_ten_main_pages(self):
        metadata = source_metadata()
        for library in sorted(SHARED):
            with self.subTest(library=library):
                path = ROOT/library/'exposition/index.html'
                self.assertTrue(path.is_file(), f'Missing generated page: {path}')
                validate_shared_page(path.read_text(), metadata[library], CONFIG[library]['results'])
        for library in ('PBGSO', 'LatentDiffusion'):
            with self.subTest(library=library):
                path = ROOT/library/'exposition/index.html'
                self.assertTrue(path.is_file(), f'Missing generated page: {path}')
                validate_dedicated_page(path.read_text(), library)


if __name__ == '__main__':
    unittest.main()
