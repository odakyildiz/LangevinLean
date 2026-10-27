#!/usr/bin/env python3
"""Validate modular reports, precise citations, and corporate bibliographies.

The default check uses only the standard library and the repository's builders.
Run after docs/build_site.py. Add --pdf with a Python containing pypdf to inspect
actual PDF bookmarks and named destinations; no PDF package is needed by the
normal documentation checks. --self-test exercises the real report catalog with
intentionally broken ownership, citations, HTML links, and bibliography entries.
This command never writes generated files.
"""
from __future__ import annotations

import argparse
from collections import Counter
import copy
import hashlib
from html import unescape
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import sys
import unicodedata
import unittest
from urllib.parse import parse_qs, unquote, urlsplit

from build_site import HELPERS, ROOT, imports, load, module_page
from full_proofs import full_proof_inventory
from report_citations import PROJECT_URL, REPORT_ORDER, REPORTS, report_owner
from report_links import CITE, ReportCatalog, citation_target
from site_content import CONFIG


class InvalidReport(ValueError):
    """An authored or generated report reference violates the integration contract."""


def require(condition, message):
    if not condition:
        raise InvalidReport(message)


def normalized_title(value):
    return ' '.join(unicodedata.normalize('NFKC', unescape(value)).split())


def sections(plans):
    """All numbered destinations which may be cited, without guessing from titles."""
    result = {}
    for library, plan in plans.items():
        own = {}
        for detail in plan['module_details'].values():
            for location in [detail] + detail['steps']:
                number = location['section']
                require(number not in own, f'{library}: duplicate section {number}')
                own[number] = location
        for item in plan['results']:
            own[item['section']] = dict(item, anchor='section.' + item['section'])
        for index, part in enumerate(CONFIG[library].get('proof', ()), 1):
            own[f'2.{index}'] = dict(title=part['title'], section=f'2.{index}',
                                    anchor=f'section.2.{index}')
        result[library] = own
    return result


def validate_plans(plans, notes, sources, parsed):
    require(set(plans) == set(REPORTS),
            'Every project report must have an inventory')
    require(list(plans) == list(REPORT_ORDER), 'Reports are not in dependency order')
    rank = {library: index for index, library in enumerate(plans)}
    owners = {}
    for library, plan in plans.items():
        require(len(plan['modules']) == len(set(plan['modules'])),
                f'{library}: a supporting module is repeated')
        require(set(plan['modules']) == set(plan['module_details']),
                f'{library}: module list and section inventory disagree')
        for index, path in enumerate(plan['modules'], 1):
            require(path not in owners, f'{path}: more than one report owner')
            owners[path] = library
            require(report_owner(path) == library, f'{path}: incorrect report owner {library}')
            require(path in sources and path in notes, f'{path}: missing source or exposition')
            detail = plan['module_details'][path]
            require(detail['section'] == f'3.{index}', f'{path}: unexpected section order')
            require(detail['anchor'] == 'section.' + detail['section'],
                    f'{path}: incorrect section destination')
            require(detail['title'] == notes[path]['title'], f'{path}: stale section title')
            require(detail['proof_steps'] == len(notes[path]['steps']) == len(detail['steps']),
                    f'{path}: changed proof-box coverage')
            explained = [name for step in notes[path]['steps'] for name in step['declarations']]
            require(set(explained) == set(parsed.get(path, {})),
                    f'{path}: mathematical declarations are not all represented')
            require(detail['declarations'] == explained, f'{path}: stale declaration inventory')
            for number, (step, authored) in enumerate(zip(detail['steps'], notes[path]['steps']), 1):
                section = f'{detail["section"]}.{number}'
                require(step['section'] == section and step['anchor'] == 'subsection.' + section,
                        f'{path}: incorrect subsection {number}')
                require(step['title'] == authored['title'] and
                        step['declarations'] == authored['declarations'],
                        f'{path}: subsection {number} differs from the authored proof')

    # Check source reachability independently of the inventory's ownership list.
    roots = set()
    for library, plan in plans.items():
        config = CONFIG[library]
        expected_roots = {item['file'] for item in config['results']}
        expected_roots.update(ref['file'] for part in config.get('proof', ())
                              for ref in part.get('references', ()))
        expected_roots.update(node['file'] for node in config.get('diagram', ()))
        require(expected_roots <= set(plan['roots']), f'{library}: omitted configured proof root')
        roots.update(plan['roots'])
    roots.update(path for path, note in notes.items()
                 if any(step['declarations'] for step in note['steps']))
    roots.discard('IPLA/Standalone.lean')
    required = set()

    def collect(path, visited):
        if path in visited or path not in sources:
            return
        visited.add(path)
        for dependency in imports(sources[path]):
            collect(dependency, visited)

    for path in roots:
        collect(path, required)
    require(set(owners) == required,
            'Report coverage mismatch: missing ' + repr(sorted(required - set(owners))) +
            '; unexpected ' + repr(sorted(set(owners) - required)))
    require('IPLA/Standalone.lean' not in owners, 'The generated standalone bundle is duplicated')
    for library, plan in plans.items():
        closure = set()
        for path in set(plan['roots']) | set(plan['modules']):
            collect(path, closure)
        borrowed = {path for path in closure if path in owners and owners[path] != library}
        require(set(plan['referenced_modules']) == borrowed,
                f'{library}: borrowed-module inventory is incomplete')
        dependencies = {owners[path] for path in borrowed}
        require(set(plan['earlier_reports']) == dependencies,
                f'{library}: report dependencies differ from its source prerequisites')
        for earlier in dependencies:
            require(rank[earlier] < rank[library], f'{library}: forward/cyclic dependency on {earlier}')
    return len(owners)


def authored_passages(notes):
    for path, note in notes.items():
        yield path + ': summary', report_owner(path), note['summary']
        for index, step in enumerate(note['steps'], 1):
            yield f'{path}: proof {index}', report_owner(path), step['body']
    for library, config in CONFIG.items():
        for index, item in enumerate(config['results'], 1):
            yield f'{library}: result {index}', library, item['body']
        for index, item in enumerate(config.get('proof', ()), 1):
            yield f'{library}: argument {index}', library, item['body']


def validate_markers(passages, catalog):
    count = 0
    rank = {library: index for index, library in enumerate(catalog.plans)}
    for label, origin, value in passages:
        markers = list(CITE.finditer(value))
        starts = re.findall(r'<cite\b[^>]*\bdata-report-(?:ref|declaration)\s*=', value)
        require(len(starts) == len(markers), f'{label}: malformed/unclosed report citation')
        for match in markers:
            try:
                path, declaration = citation_target(match)
                location = catalog.location(path, declaration)
            except (ValueError, KeyError, AttributeError) as error:
                raise InvalidReport(f'{label}: {error}') from error
            require(location['library'] in rank, f'{label}: unknown report identity')
            if origin in rank:
                require(rank[location['library']] <= rank[origin],
                        f'{label}: authored reference to a later report {location["library"]}')
            require(location['section'] and location['anchor'], f'{label}: unresolved citation location')
            count += 1
    return count


def bib_entries(value, label):
    starts = list(re.finditer(r'@(techreport|misc)\s*\{\s*([^,\s]+)\s*,', value, re.I))
    result = {}
    for index, match in enumerate(starts):
        key = match[2]
        require(key not in result, f'{label}: duplicate bibliography key {key}')
        entry = value[match.start():starts[index + 1].start() if index + 1 < len(starts) else len(value)]
        require(re.search(r'\bauthor\s*=\s*\{\{LangevinLean Project\}\}', entry),
                f'{label}: {key} does not use the protected corporate author')
        result[key] = entry
    require(result, f'{label}: no bibliography entries')
    return result


def validate_bibliographies(plans, root=ROOT):
    combined = bib_entries((root / 'docs/bib/all-reports.bib').read_text(), 'all-reports.bib')
    expected = {REPORTS[library]['key'] for library in plans}
    require(set(combined) == expected, 'Combined BibTeX does not cover exactly the project reports')
    for library, plan in plans.items():
        path = root / f'docs/bib/{library}.bib'
        entries = bib_entries(path.read_text(), str(path.relative_to(root)))
        key = REPORTS[library]['key']
        require(set(entries) == {key}, f'{path}: incorrect report identity')
        entry = entries[key]
        require(entry.strip() == combined[key].strip(), f'{path}: combined/individual citations differ')
        require(plan['revision'] in entry and REPORTS[library]['number'] in entry,
                f'{path}: stale content revision or report number')
        require(PROJECT_URL + plan['pdf'] in entry, f'{path}: incorrect report URL')
    project = bib_entries((root / 'docs/bib/project.bib').read_text(), 'project.bib')
    require(set(project) == {'LangevinLeanProject2026'}, 'Incorrect project-level citation')
    return len(expected) + 1


TEX_CITE = re.compile(r'\\cite(?:\[([^\]]*)\])?\{([^}]+)\}')
RAW_MARKER = re.compile(r'\bdata-report-(?:ref|declaration)\s*=|REPORTREFERENCEPLACEHOLDER')


def validate_tex_content(value, label, registry):
    require(not RAW_MARKER.search(value), f'{label}: unresolved authored citation marker')
    items = re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}', value)
    require(len(items) == len(set(items)), f'{label}: repeated bibliography item')
    provided = set(items)
    key_to_library = {REPORTS[library]['key']: library for library in registry}
    count = 0
    for match in TEX_CITE.finditer(value):
        note, keys = match.groups()
        keys = [key.strip() for key in keys.split(',')]
        for key in keys:
            require(key in provided, f'{label}: missing bibliography item {key}')
            require(key in key_to_library, f'{label}: unknown report citation {key}')
        if note and re.search(r'\bSection\b', note):
            found = re.findall(r'\bSection(?:~|\s)+([0-9]+(?:\.[0-9]+)+)', note)
            require(found, f'{label}: malformed precise section citation {note!r}')
            for number in found:
                for key in keys:
                    require(number in registry[key_to_library[key]],
                            f'{label}: {key} has no Section {number}')
        count += len(keys)
    labels = set(re.findall(r'\\label\{([^}]+)\}', value))
    for reference in re.findall(r'\\ref\{((?:report-step-|proof-module-)[^}]+)\}', value):
        require(reference in labels, f'{label}: unresolved internal proof reference {reference}')
    for key in provided:
        require(key in key_to_library, f'{label}: unknown bibliography item {key}')
        entry = re.search(r'\\bibitem(?:\[[^\]]*\])?\{' + re.escape(key) + r'\}([\s\S]*?)(?=\\bibitem|\\end\{thebibliography\})', value)
        require(entry and 'LangevinLean Project.' in entry[1],
                f'{label}: bibliography item {key} lacks the corporate author')
    return count


class ReportHTML(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.links = []
        self.panels = []
        self._panel = None
        self._depth = 0

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag == 'a':
            self.links.append(attrs)
        if self._panel is not None:
            if tag not in ('br', 'hr', 'img', 'input', 'meta', 'link'):
                self._depth += 1
        elif 'citation-panel' in attrs.get('class', '').split():
            self._panel, self._depth = [], 1

    def handle_endtag(self, tag):
        if self._panel is not None:
            self._depth -= 1
            if not self._depth:
                self.panels.append(''.join(self._panel))
                self._panel = None

    def handle_data(self, value):
        if self._panel is not None:
            self._panel.append(value)


def report_href(href, page, plans, root=ROOT):
    url = urlsplit(unescape(href))
    if url.scheme or url.netloc:
        require(href.startswith(PROJECT_URL), f'{page}: report link points outside the project: {href}')
        target = root / unquote(urlsplit(href.removeprefix(PROJECT_URL)).path)
    else:
        target = (root / page).parent / unquote(url.path)
    target = target.resolve()
    targets = {(root / plan['pdf']).resolve(): library for library, plan in plans.items()}
    require(target in targets, f'{page}: report link has an unknown PDF target: {href}')
    anchor = parse_qs(url.fragment).get('nameddest', [None])[0]
    require(anchor, f'{page}: precise report link lacks a named destination: {href}')
    return targets[target], anchor


def validate_html_content(value, page, plans, registry, expected_key=None, root=ROOT):
    require(not RAW_MARKER.search(value), f'{page}: unresolved authored citation marker')
    parser = ReportHTML()
    parser.feed(value)
    require(parser.panels, f'{page}: missing corporate citation panel')
    for panel in parser.panels:
        entries = bib_entries(panel, str(page) + ' citation panel')
        if expected_key:
            require(expected_key in entries, f'{page}: panel cites the wrong report/project')
    anchors = {library: {item['anchor'] for item in locations.values()}
               for library, locations in registry.items()}
    linked = []
    for attrs in parser.links:
        is_citation = ('report-citation' in attrs.get('class', '').split() or
                       'data-report' in attrs or 'data-report-section' in attrs)
        href = attrs.get('href', '')
        if is_citation:
            library, number = attrs.get('data-report'), attrs.get('data-report-section')
            require(library in registry and number in registry[library],
                    f'{page}: unknown data-report location {library}: {number}')
            location = registry[library][number]
            actual_library, anchor = report_href(href, page, plans, root)
            require(actual_library == library and anchor == location['anchor'],
                    f'{page}: report link disagrees with data-report-section {library}: {number}')
            require(normalized_title(attrs.get('title', '')) == normalized_title(location['title']),
                    f'{page}: report link has a stale destination title')
            linked.append((actual_library, anchor))
        elif 'nameddest=' in urlsplit(href).fragment:
            library, anchor = report_href(href, page, plans, root)
            require(anchor in anchors[library], f'{page}: unknown precise report-panel destination {anchor}')
            linked.append((library, anchor))
    return linked


def generated_checks(plans, catalog, root=ROOT):
    registry = sections(plans)
    coverage = json.loads((root / 'docs/coverage.json').read_text())
    require(json.loads((root / 'docs/full_proofs.json').read_text()) == plans,
            'Stale report inventory; regenerate docs/build_site.py')
    html_links, tex_citations, pages = set(), 0, 0
    source_for_page = {module_page(path): path for path in catalog.notes}
    overview_for_page = {library + '/exposition/index.html': library for library in plans}
    from average_content import AVERAGE_PAGES
    overview_for_page.update({page: config['library'] for page, config in AVERAGE_PAGES.items()})
    for relative in coverage['outputs']:
        if relative.endswith('.tex'):
            tex_citations += validate_tex_content((root / relative).read_text(), relative, registry)
        elif relative.endswith('.html'):
            if relative in source_for_page:
                location = catalog.locations.get(source_for_page[relative])
                library = location['library'] if location else None
            else:
                library = overview_for_page.get(relative)
            key = REPORTS[library]['key'] if library else 'LangevinLeanProject2026'
            html_links.update(validate_html_content((root / relative).read_text(), relative,
                                                   plans, registry, key, root))
            pages += 1
    require(pages, 'No generated HTML pages were checked')
    return pages, tex_citations, html_links


def _outline_tree(items):
    result = []
    for item in items:
        if isinstance(item, list):
            require(result, 'PDF outline has an orphaned child list')
            result[-1]['children'] = _outline_tree(item)
        else:
            result.append(dict(title=str(item.get('/Title', '')), destination=item, children=[]))
    return result


def _destination_signature(reader, destination):
    def coordinate(value):
        try:
            return round(float(value), 3)
        except (TypeError, ValueError):
            return str(value)
    return (reader.get_destination_page_number(destination),
            str(destination.get('/Type')),
            coordinate(destination.get('/Left')), coordinate(destination.get('/Top')))


def validate_pdfs(plans, html_links, root=ROOT):
    try:
        from pypdf import PdfReader
    except ImportError as error:
        raise InvalidReport('--pdf requires pypdf; use the bundled runtime Python, or run without --pdf') from error
    manifest = json.loads((root / 'docs/pdf/manifest.json').read_text())
    records = manifest['documents']
    require(set(records) == {plan['latex'] for plan in plans.values()},
            'PDF manifest does not cover exactly the modular reports')
    destinations, count = {}, 0
    for library, plan in plans.items():
        path = root / plan['pdf']
        record = records[plan['latex']]
        require(record['pdf'] == plan['pdf'], f'{library}: manifest points to another PDF')
        require(hashlib.sha256(path.read_bytes()).hexdigest() == record['pdf_sha256'],
                f'{library}: PDF content hash is stale')
        require(hashlib.sha256((root / plan['latex']).read_bytes()).hexdigest() == record['source_sha256'],
                f'{library}: PDF was compiled from another source revision')
        reader = PdfReader(path)
        require(len(reader.pages) == record['pages'], f'{library}: PDF page count differs from manifest')
        require(reader.metadata.get('/Author') == 'LangevinLean Project',
                f'{library}: PDF metadata lacks the corporate author')
        named = reader.named_destinations
        destinations[library] = set(named)
        tree = _outline_tree(reader.outline)
        supporting = [node for node in tree if normalized_title(node['title']) == 'Supporting proofs']
        require(len(supporting) == 1, f'{library}: missing/ambiguous supporting-proofs chapter bookmark')
        supporting = supporting[0]
        signature = _destination_signature(reader, supporting['destination'])
        chapter_names = [name for name, dest in named.items()
                         if re.fullmatch(r'chapter\.\d+', name) and
                         _destination_signature(reader, dest) == signature]
        require(len(chapter_names) == 1, f'{library}: supporting chapter lacks a numbered named destination')
        chapter = chapter_names[0].split('.')[1]
        actual_sections = supporting['children']
        require(len(actual_sections) == len(plan['modules']),
                f'{library}: PDF supporting-section count differs from its module inventory')
        for index, (path, actual) in enumerate(zip(plan['modules'], actual_sections), 1):
            detail = plan['module_details'][path]
            number = f'{chapter}.{index}'
            require(detail['section'] == number, f'{library}: planned section number disagrees with PDF outline order: {path}')
            require(normalized_title(actual['title']) == normalized_title(detail['title']),
                    f'{library}, Section {number}: PDF bookmark title differs from the authored title')
            require(detail['anchor'] in named and
                    _destination_signature(reader, named[detail['anchor']]) ==
                    _destination_signature(reader, actual['destination']),
                    f'{library}, Section {number}: bookmark and named destination disagree')
            require(len(actual['children']) == len(detail['steps']),
                    f'{library}, Section {number}: missing subsection bookmarks; use bookmarksdepth=2')
            for step_index, (step, actual_step) in enumerate(zip(detail['steps'], actual['children']), 1):
                subsection = f'{number}.{step_index}'
                require(step['section'] == subsection,
                        f'{library}: planned subsection disagrees with PDF outline order')
                require(normalized_title(actual_step['title']) == normalized_title(step['title']),
                        f'{library}, Section {subsection}: PDF subsection title differs from the authored proof')
                require(step['anchor'] in named and
                        _destination_signature(reader, named[step['anchor']]) ==
                        _destination_signature(reader, actual_step['destination']),
                        f'{library}, Section {subsection}: bookmark and named destination disagree')
                count += 1
    for library, anchor in html_links:
        require(anchor in destinations[library], f'HTML cites a missing actual PDF destination: {library}: {anchor}')
    return count


def context():
    sources, parsed, notes = load()
    plans = full_proof_inventory(CONFIG, notes, sources)
    return sources, parsed, notes, plans, ReportCatalog(plans, notes, sources, parsed)


def verify(pdf=False):
    sources, parsed, notes, plans, catalog = context()
    modules = validate_plans(plans, notes, sources, parsed)
    authored = validate_markers(authored_passages(notes), catalog)
    bibs = validate_bibliographies(plans)
    pages, citations, html_links = generated_checks(plans, catalog)
    pdf_steps = validate_pdfs(plans, html_links) if pdf else None
    result = (f'Checked {len(plans)} modular reports, {modules} uniquely owned proof modules, '
              f'{authored} authored use-site citations, {citations} generated TeX report citations, '
              f'{pages} HTML citation panels, and {bibs} corporate-author BibTeX records.')
    if pdf:
        result += f' Verified {pdf_steps} PDF proof-subsection bookmarks and {len(html_links)} linked named destinations.'
    print(result)


class ReportCitationTests(unittest.TestCase):
    """Corrupt real integration data to ensure the checker catches actual failures."""
    @classmethod
    def setUpClass(cls):
        cls.sources, cls.parsed, cls.notes, cls.plans, cls.catalog = context()
        cls.registry = sections(cls.plans)

    def test_real_catalog_owns_every_mathematical_declaration_and_resolves_markers(self):
        self.assertGreater(validate_plans(self.plans, self.notes, self.sources, self.parsed), 0)
        self.assertGreater(validate_markers(authored_passages(self.notes), self.catalog), 0)

    def test_deleting_an_actual_owner_is_rejected(self):
        plans = copy.deepcopy(self.plans)
        library = next(iter(plans))
        path = next(path for path in plans[library]['modules'] if self.notes[path]['steps'])
        plans[library]['modules'].remove(path)
        del plans[library]['module_details'][path]
        with self.assertRaises(InvalidReport):
            validate_plans(plans, self.notes, self.sources, self.parsed)

    def test_unknown_actual_result_and_forward_report_reference_are_rejected(self):
        with self.assertRaises(InvalidReport):
            validate_markers([('broken', 'IPLA', '<cite data-report-ref="UnadjustedLangevin/CanonicalULA.lean" data-report-declaration="missing_result"></cite>')], self.catalog)
        target = next(iter(self.plans['KIPLMC']['modules']))
        with self.assertRaises(InvalidReport):
            validate_markers([('forward', 'UnadjustedLangevin', f'<cite data-report-ref="{target}"></cite>')], self.catalog)

    def test_personal_author_cannot_replace_the_real_corporate_entry(self):
        value = (ROOT / 'docs/bib/UnadjustedLangevin.bib').read_text()
        self.assertTrue(bib_entries(value, 'actual entry'))
        with self.assertRaises(InvalidReport):
            bib_entries(value.replace('{{LangevinLean Project}}', '{Omer Deniz Akyildiz}'), 'broken entry')

    def test_nonexistent_section_in_a_real_generated_tex_citation_is_rejected(self):
        value = (ROOT / self.plans['IPLA']['latex']).read_text()
        self.assertGreater(validate_tex_content(value, 'actual report', self.registry), 0)
        broken, count = re.subn(r'(\\cite\[Section~)[0-9.]+', r'\g<1>999.999', value, count=1)
        self.assertEqual(count, 1)
        with self.assertRaises(InvalidReport):
            validate_tex_content(broken, 'broken report', self.registry)

    def test_combined_prerequisite_citation_requires_each_bibliography_item(self):
        keys = [REPORTS[library]['key'] for library in list(self.plans)[:2]]
        notice = r'\cite{' + ','.join(keys) + '}'
        value = notice + self.catalog.bibliography(notice)
        self.assertEqual(validate_tex_content(value, 'combined report notice', self.registry), 2)
        broken = re.sub(r'\\bibitem(?:\[[^\]]*\])?\{' + re.escape(keys[0]) +
                        r'\}[\s\S]*?(?=\\bibitem|\\end\{thebibliography\})', '', value, count=1)
        with self.assertRaises(InvalidReport):
            validate_tex_content(broken, 'incomplete combined report notice', self.registry)

    def test_actual_html_citation_cannot_point_to_a_different_subsection(self):
        page = 'docs/modules/IPLA/Theorem.html'
        value = (ROOT / page).read_text()
        self.assertTrue(validate_html_content(value, page, self.plans, self.registry))
        match = re.search(r'<a[^>]*data-report="([^"]+)"[^>]*data-report-section="([^"]+)"', value)
        self.assertIsNotNone(match)
        other = next(number for number in self.registry[match[1]] if number != match[2])
        start, end = match.span(2)
        broken = value[:start] + other + value[end:]
        with self.assertRaises(InvalidReport):
            validate_html_content(broken, page, self.plans, self.registry)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdf', action='store_true', help='Also inspect actual PDF bookmarks/destinations with optional pypdf')
    parser.add_argument('--self-test', action='store_true', help='Run corruption regressions against the real repository catalog')
    args = parser.parse_args()
    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(ReportCitationTests)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if result.wasSuccessful() else 1
    try:
        verify(pdf=args.pdf)
    except (InvalidReport, OSError, KeyError, ValueError) as error:
        print('Report citation checks failed: ' + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
