#!/usr/bin/env python3
"""Check PBGSO source correspondence, exact assumptions and generated pages.

This verifier checks documentation fidelity. Strict mode additionally checks
the source and method coverage ledger under its explicit source interpretations. Run `lake build PBGSO` and the logical Check.lean
audit separately to verify the formal proofs and their logical dependencies.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'docs'))

from build_pbgso import (CATALOG, OVERVIEW, assumption_inventory, outputs, proof_page,
                         source_inventory)
from verify_site import Page
from build_site import HELPERS


# The landing-page contract is separate from declaration fidelity. Moving a
# proof catalog must not silently remove source statements or hide stronger
# analytic conditions in code panes or a distant audit file.
from html.parser import HTMLParser


class LandingNode:
    def __init__(self, tag, attrs=None, parent=None):
        self.tag, self.attrs, self.parent = tag, dict(attrs or []), parent
        self.children = []

    def walk(self):
        yield self
        for child in self.children:
            if isinstance(child, LandingNode):
                yield from child.walk()

    def text(self):
        if self.tag in ('script', 'style'):
            return ''
        return ' '.join(child.text() if isinstance(child, LandingNode) else child
                        for child in self.children)

    def classes(self):
        return set(self.attrs.get('class', '').split())

    def ancestors(self):
        node = self.parent
        while node is not None:
            yield node
            node = node.parent


class LandingDocument(HTMLParser):
    VOID = {'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input',
            'link', 'meta', 'param', 'source', 'track', 'wbr'}

    def __init__(self, text):
        super().__init__(convert_charrefs=True)
        self.root = LandingNode('document')
        self.stack = [self.root]
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        node = LandingNode(tag, attrs, self.stack[-1])
        self.stack[-1].children.append(node)
        if tag not in self.VOID:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in self.VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        for index in range(len(self.stack)-1, 0, -1):
            if self.stack[index].tag == tag:
                self.stack = self.stack[:index]
                return

    def handle_data(self, data):
        self.stack[-1].children.append(data)

    def by_id(self, identifier):
        found = [n for n in self.root.walk() if n.attrs.get('id') == identifier]
        assert len(found) == 1, f'Expected one PBGSO landing section #{identifier}'
        return found[0]


def verify_landing(overview, catalog, audit, sources, catalog_path, root=ROOT):
    """Check the reader-facing mathematical hierarchy and assumption markers.

    This checks presentation contracts, not the truth of analytic assumptions.
    Exact Lean contracts and the independent source audit remain necessary.
    """
    doc, technical = LandingDocument(overview), LandingDocument(catalog)
    nodes = list(doc.root.walk())
    main = doc.by_id('main')
    assert not any('module-card' in n.classes() for n in main.walk()), \
        'Move the PBGSO module catalog off the primary theorem page'
    links = [n.attrs['href'] for n in main.walk() if n.tag == 'a' and 'href' in n.attrs]
    wanted_catalog = str(Path(catalog_path).name)
    assert any(urlsplit(href).path == wanted_catalog for href in links), \
        'Primary PBGSO page must link to its separate technical catalog'

    expected_ids = {r['id']: r['number'] for r in audit['results'] if r['kind'] == 'theorem'}
    paper = [n for n in main.walk() if 'data-source-result' in n.attrs]
    assert len(paper) == 4 and {n.attrs['data-source-result'] for n in paper} == set(expected_ids), \
        'Primary PBGSO page must state exactly the four named main paper theorems'
    for node in paper:
        identifier = node.attrs['data-source-result']
        headings = [n.text() for n in node.walk() if n.tag in ('h2', 'h3', 'h4')]
        assert any(re.search(r'\bTheorem\s+'+re.escape(expected_ids[identifier])+r'\b', h, re.I)
                   for h in headings), f'Missing paper theorem name/number: {identifier}'
        assert any('katex' in n.classes() for n in node.walk()), \
            f'Paper theorem needs its mathematical statement, not only a source link: {identifier}'
        text = node.text()
        assert re.search(r'\b(assumptions?|hypotheses)\b', text, re.I), \
            f'Missing explicit assumptions: {identifier}'
        has_added = any(n.attrs.get('data-assumption-kind') == 'added' for n in node.walk())
        has_none = any('no-added-assumption' in n.classes() and
                       re.search(r'\bnone\b', n.text(), re.I) for n in node.walk())
        assert has_added or has_none, \
            f'Each paper theorem must identify additions, or explicitly say none: {identifier}'

    marked = [n for n in nodes if 'data-assumption-kind' in n.attrs or
              {'added-assumption', 'interpretation-assumption'} & n.classes()]
    assert marked, 'Missing reader-facing added-assumption/interpretation semantics'
    assert any(n.attrs.get('data-assumption-kind') == 'interpretation' for n in marked), \
        'The A2 SDE interpretation must be marked distinctly from added assumptions'
    for node in marked:
        kind = node.attrs.get('data-assumption-kind')
        assert kind in ('added', 'interpretation'), 'Assumption colors need an explicit semantic kind'
        expected_class = 'added-assumption' if kind == 'added' else 'interpretation-assumption'
        assert expected_class in node.classes(), f'Assumption marker lacks its color class: {kind}'
        other = 'interpretation-assumption' if kind == 'added' else 'added-assumption'
        assert other not in node.classes(), 'An assumption cannot be both added and an interpretation'
        assert node.text().strip(), 'An assumption color marker cannot be empty'
        if kind == 'interpretation':
            assert not re.search(r'FiniteCouplingWork|finite[\s-]+signed[\s-]+work', node.text(), re.I), \
                'Universal finite signed work is a stronger condition, not merely an interpretation marker'
    contraction = next(n for n in paper if n.attrs['data-source-result'] ==
                       'thm:twisted_joint_strong_monotonicity')
    assert any(n.attrs.get('data-assumption-kind') == 'added' and
               re.search(r'FiniteCouplingWork|finite[\s-]+signed[\s-]+work', n.text(), re.I)
               for n in contraction.walk()), \
        'The constant-diffusion contraction must mark its finite signed-work strengthening as added'

    new = doc.by_id('new-theory')
    additions = [n for n in nodes if 'data-new-theory' in n.attrs]
    assert len(additions) == 2 and {n.attrs['data-new-theory'] for n in additions} == {'A', 'B'}, \
        'New Theory must contain exactly Theorem New A and Theorem New B'
    for node in additions:
        label = node.attrs['data-new-theory']
        assert new in set(node.ancestors()), f'Theorem New {label} must be inside New Theory'
        headings = [n.text() for n in node.walk() if n.tag in ('h2', 'h3', 'h4')]
        assert any(re.search(r'\bTheorem\s+New\s+'+label+r'\b', h, re.I) for h in headings), \
            f'Missing explicit final theorem label New {label}'
        assert any('katex' in n.classes() for n in node.walk()), f'Missing New {label} bound'
        assert re.search(r'\b(assumptions?|hypotheses)\b', node.text(), re.I), \
            f'Missing New {label} assumptions'
        conclusions = [n for n in node.walk() if n.attrs.get('data-time-uniform') == 'true']
        assert len(conclusions) == 1, f'New {label} must identify its time-uniform conclusion'
        assert re.search(r'every (?:iteration|n\b)|all iterations', conclusions[0].text(), re.I), \
            f'New {label} must quantify over all iterations'
        assert re.search(r'independent of time', conclusions[0].text(), re.I), \
            f'New {label} must state that its constants are independent of time'
        assert any(n.attrs.get('data-assumption-kind') == 'added' for n in node.walk()), \
            f'New {label} must color its extra numerical assumptions'
        assert not re.search(r'fixed finite horizon|nh\s*≤\s*T', node.text(), re.I), \
            f'New {label} must not restrict the headline result to a fixed horizon'

    standalone = doc.by_id('standalone-verification')
    commands = '\n'.join(n.text() for n in standalone.walk() if n.tag == 'pre')
    runners = re.findall(r'(?:bash|sh|python3(?:\s+-B)?|lake\s+env\s+lean)\s+'
                         r'([\w./-]+\.(?:sh|py|lean))', commands)
    assert runners, 'Standalone verification needs an executable local command'
    output_directories = [Path(p) for p in re.findall(r'--output\s+([\w./-]+)', commands)]
    for command in runners:
        path = Path(command)
        if path.is_absolute():
            assert any(path.is_relative_to(directory) for directory in output_directories), \
                f'Absolute standalone target is not a declared generated output: {command}'
        else:
            assert (root/path).is_file(), f'Standalone verification command does not exist: {command}'
    standalone_files = {urlsplit(n.attrs['href']).path for n in standalone.walk()
                        if n.tag == 'a' and 'href' in n.attrs and
                        re.search(r'(?:^|/)standalone/', urlsplit(n.attrs['href']).path, re.I) and
                        urlsplit(n.attrs['href']).path.endswith('.lean')}
    assert len(standalone_files) >= 2, 'Link the actual separate New A and New B verification files'

    roadmap = doc.by_id('proof-roadmap')
    sections = [n for n in main.walk() if n.tag == 'section' and
                not any(a.tag == 'section' for a in n.ancestors())]
    assert sections and sections[-1] is roadmap, 'The substantial proof roadmap must finish the main page'
    words = re.findall(r'\b[\w’\'-]+\b', roadmap.text())
    assert len(words) >= 180, 'The final proof roadmap needs a substantial mathematical explanation'
    roadmap_links = [n.attrs['href'] for n in roadmap.walk() if n.tag == 'a' and 'href' in n.attrs]
    assert len(roadmap_links) >= 6, 'The proof roadmap must link its main proof stages'
    for result in audit['results']:
        if result['kind'] == 'theorem':
            continue
        targets = {str(Path(proof_page(d['file'])).name) for d in
                   audit['formal_coverage'][result['id']]['declarations']}
        assert any(Path(urlsplit(link).path).name in targets for link in roadmap_links), \
            f'Proof roadmap omits the appendix result {result["id"]}'

    cards = [n for n in technical.root.walk() if 'module-card' in n.classes()]
    assert len(cards) == len(sources), 'The separate catalog must retain every PBGSO module'
    technical_links = {urlsplit(n.attrs['href']).path for n in technical.root.walk()
                       if n.tag == 'a' and 'href' in n.attrs}
    assert all('proofs/'+Path(proof_page(source)).name in technical_links for source in sources), \
        'The technical catalog must link every complete module proof page'


def verify(require_complete=False):
    sources, parsed = source_inventory()
    expected = outputs()
    for path, value in expected.items():
        assert (ROOT/path).is_file(), f'Missing PBGSO output: {path}'
        assert (ROOT/path).read_text() == value, f'Stale PBGSO output: {path}; run python3 docs/build_site.py'
    inventory = json.loads((ROOT/'PBGSO/exposition/assumption_inventory.json').read_text())
    assert inventory == assumption_inventory(sources, parsed), 'Stale exact assumption inventory'
    assert set(inventory['modules']) == set(sources), 'Missing module assumption inventory'
    for path, source in sources.items():
        masked = '\n'.join(HELPERS.mask_comments(source.splitlines()))
        assert not re.search(r'\b(sorry|admit|sorryAx)\b', masked), f'Incomplete proof in {path}'
        assert not re.search(r'^\s*(?:unsafe\s+)?axiom\s', masked, re.M), f'Custom axiom in {path}'
        assert inventory['modules'][path]['source_sha256'] == hashlib.sha256(source.encode()).hexdigest()
        assert inventory['modules'][path]['scope_note'], f'Missing scope for {path}'
        assert set(inventory['modules'][path]['declarations']) == set(parsed[path])

    audit = json.loads((ROOT/'PBGSO/exposition/reference_audit.json').read_text())
    assert audit['counts']['numbered_results'] == 8 and len(audit['results']) == 8
    assert len(audit['assumptions']) == 10
    for path, checksum in audit['source']['source_hashes'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == checksum, f'Source audit stale: {path}'
    for item in audit['results'] + audit['assumptions']:
        source = (ROOT/item['source']).read_text().splitlines()
        actual = '\n'.join(source[item['start_line']-1:item['end_line']])
        assert item['exact_tex'] in actual, f'Source statement changed: {item.get("label") or item["kind"]}'
    coverage = audit['formal_coverage']
    method_coverage = audit['additional_method_coverage']
    assert set(method_coverage) == {'M-MFPO', 'HOL-MYPGD'}, 'Missing actual method-bound coverage'
    uniform_endpoints = {
        'M-MFPO': ('PBGSO/FullyUniformMomentum.lean', 'numerical_parameter_bound'),
        'HOL-MYPGD': ('PBGSO/FullyUniformHigherOrder.lean', 'parameter_bound'),
    }
    for method, (file, name) in uniform_endpoints.items():
        assert {'file': file, 'name': name} in method_coverage[method]['declarations'], \
            f'Missing all-iteration final endpoint: {method}'
    assert set(coverage) == {r['id'] for r in audit['results']}, 'Missing per-source-result formal coverage'
    for identifier, item in {**coverage, **method_coverage}.items():
        assert item['status'] in ('partial','verified'), f'Invalid coverage status: {identifier}'
        assert bool(item['remaining_obligations']) == (item['status'] == 'partial'), f'Inconsistent obligations: {identifier}'
        for declaration in item['declarations']:
            assert declaration['file'] in parsed and declaration['name'] in parsed[declaration['file']], f'Missing formal coverage declaration: {declaration}'

    cache = {}
    def parse(path):
        path = Path(path).resolve()
        if path not in cache:
            doc = Page(); doc.feed(path.read_text()); cache[path] = doc
        return cache[path]

    excerpts = links = declarations_seen = 0
    for path, text in expected.items():
        if not path.endswith('.html'):
            continue
        target = ROOT/path
        doc = parse(target)
        assert text.startswith('<!doctype html>'), f'Incomplete HTML: {path}'
        assert doc.robots == ['noindex, nofollow, noarchive']
        assert len(doc.ids) == len(set(doc.ids)), f'Duplicate HTML IDs: {path}'
        assert 'katex-error' not in text, f'Invalid math: {path}'
        assert not re.search(r'\\[\[(]', ''.join(doc.text)), f'Unrendered math: {path}'
        assert not any(urlsplit(href).path.endswith('.pdf') for href in doc.links), f'Unestablished PDF link: {path}'
        represented = set()
        for block in doc.blocks:
            excerpts += 1
            source = block['data-source']
            start, end = int(block['data-start']), int(block['data-end'])
            wanted = sources[source].splitlines()[start-1:end]
            if block['data-role'] == 'statement':
                wanted[-1] = wanted[-1].split(':=', 1)[0].rstrip()
            assert block['lines'] == wanted, f'Altered source: {path}: {source}:{start}-{end}'
            if block['data-role'] == 'declaration':
                name = block['data-declaration']
                assert name not in represented, f'Repeated declaration: {path}: {name}'
                represented.add(name); declarations_seen += 1
                decl = parsed[source][name]
                assert (start, end) == (decl['start'], decl['end'])
        if path.startswith('PBGSO/exposition/proofs/'):
            source = next(p for p in sources if proof_page(p) == path)
            assert represented == set(parsed[source]), f'Missing declarations: {source}'
            assert any(b['data-role'] == 'module' and b['data-source'] == source for b in doc.blocks)
        for href in doc.links + doc.resources:
            links += 1
            link = urlsplit(href)
            if link.scheme or link.netloc:
                assert href not in doc.resources, f'Network resource: {path}: {href}'
                assert link.scheme in ('http','https')
                continue
            destination = (target.parent/unquote(link.path)).resolve() if link.path else target
            assert destination.is_relative_to(ROOT) and destination.is_file(), f'Broken link: {path}: {href}'
            assert destination.relative_to(ROOT).parts[0] != 'papers', f'Main-only source link: {path}: {href}'
            if link.fragment and destination.suffix == '.html':
                assert unquote(link.fragment) in parse(destination).ids, f'Broken anchor: {path}: {href}'
    verify_landing((ROOT/OVERVIEW).read_text(), (ROOT/CATALOG).read_text(),
                   audit, sources, CATALOG)
    unfinished = [(identifier, item) for identifier, item in coverage.items() if item['status'] != 'verified']
    unfinished_methods = [(identifier, item) for identifier, item in method_coverage.items() if item['status'] != 'verified']
    open_bridges = audit.get('open_formal_obligations', [])
    print(f'Verified PBGSO documentation fidelity: {len(sources)} module inventories, {declarations_seen} complete declarations, '
          f'{excerpts} exact source excerpts, {links} local links/resources, 8 source results and 10 assumptions. '
          f'{len(unfinished)} source results and {len(unfinished_methods)} method bounds still have partial formal coverage; full completion is a separate strict check.')
    if require_complete and (unfinished or unfinished_methods or open_bridges):
        messages = ['PBGSO full-paper formal coverage is incomplete:']
        for identifier, item in unfinished + unfinished_methods:
            messages.append(f'- {identifier} [{item["status"]}]:')
            messages.extend('  - '+obligation for obligation in item['remaining_obligations'])
        messages.append('Open stochastic/target bridges:')
        messages.extend(f'- {item["id"]}: {item["description"]}' for item in open_bridges)
        raise SystemExit('\n'.join(messages))
    if require_complete:
        print('All eight inventoried source results, both actual method bounds and required formal bridges are verified under the audit file’s explicit source interpretations.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-complete', action='store_true',
                        help='Reject every open source-result, actual method-bound or required proof obligation')
    verify(parser.parse_args().require_complete)
