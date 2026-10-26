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

from build_pbgso import (OVERVIEW, assumption_inventory, outputs, proof_page,
                         source_inventory)
from verify_site import Page
from build_site import HELPERS


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
    overview = (ROOT/OVERVIEW).read_text()
    for phrase in ['not proved here', 'stationary', 'integrability', 'empirical', 'smoothing',
                   'TV', 'critical point', 'right derivative']:
        assert phrase in overview, f'Missing formal-scope qualification: {phrase}'
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
