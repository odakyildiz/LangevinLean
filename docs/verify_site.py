#!/usr/bin/env python3
"""Verify module/declaration coverage, source fidelity, local links and exports."""
from __future__ import annotations
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit
from build_site import ROOT, LIBRARIES, load, module_page, latex_path


class Page(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.links, self.resources, self.blocks = [], [], [], []
        self.block = self.line = None
        self.line_depth = 0
        self.text = []
        self.styles = self.scripts = 0
        self.boxes = []
    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if 'id' in attrs: self.ids.append(attrs['id'])
        if tag=='a' and 'href' in attrs:
            self.links.append(attrs['href'])
            if 'box' in attrs.get('class','').split(): self.boxes.append(attrs['href'])
        if tag in ('script','link','img','iframe','audio','video'):
            url=attrs.get('src',attrs.get('href',''))
            if url: self.resources.append(url)
        if tag=='style': self.styles+=1
        if tag=='script': self.scripts+=1
        if tag=='pre' and 'data-source' in attrs: self.block={**attrs,'lines':[]}
        if tag=='span' and self.block is not None:
            if attrs.get('class')=='line-text': self.line=''; self.line_depth=1
            elif self.line is not None: self.line_depth+=1
    def handle_endtag(self,tag):
        if tag=='style': self.styles-=1
        if tag=='script': self.scripts-=1
        if tag=='span' and self.line is not None:
            self.line_depth-=1
            if not self.line_depth:
                self.block['lines'].append(self.line);self.line=None
        if tag=='pre' and self.block is not None:
            self.blocks.append(self.block);self.block=None
    def handle_data(self,data):
        if self.line is not None: self.line+=data
        elif not self.styles and not self.scripts: self.text.append(data)


def digest(path):
    return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()


def verify():
    sources,parsed,notes=load()
    manifest=json.loads((ROOT/'docs/coverage.json').read_text())
    assert set(manifest['modules'])==set(sources),'Missing module page in coverage manifest'
    for path,checksum in manifest['inputs'].items():
        assert digest(path)==checksum,f'Stale authoring input {path}; run python3 docs/build_site.py'
    for path,checksum in manifest['outputs'].items():
        assert digest(path)==checksum,f'Stale generated file {path}; run python3 docs/build_site.py'
    cache={}
    def parse(path):
        path=Path(path).resolve()
        if path not in cache:
            doc=Page();doc.feed(path.read_text());cache[path]=doc
        return cache[path]
    outputs=[module_page(p) for p in sources]+[l+'/exposition/index.html' for l in LIBRARIES]+['index.html']
    links=blocks=0
    for path in outputs:
        target=ROOT/path
        text=target.read_text()
        doc=parse(target)
        assert text.startswith('<!doctype html>'),f'Incomplete HTML: {path}'
        assert len(doc.ids)==len(set(doc.ids)),f'Duplicate HTML IDs: {path}'
        assert 'katex-error' not in text,f'Invalid rendered formula: {path}'
        assert not re.search(r'\\[\[(]',''.join(doc.text)),f'Unrendered mathematics: {path}'
        for href in doc.links+doc.resources:
            links+=1
            link=urlsplit(href)
            if link.scheme or link.netloc:
                assert href not in doc.resources,f'Network-dependent resource {path}: {href}'
                assert link.scheme in ('https','http'),f'Unexpected scheme: {href}'
                continue
            destination=(target.parent/unquote(link.path)).resolve() if link.path else target
            assert destination.is_relative_to(ROOT) and destination.is_file(),f'Broken link {path}: {href}'
            if link.fragment and destination.suffix=='.html':
                assert unquote(link.fragment) in parse(destination).ids,f'Broken anchor {path}: {href}'
        for href in doc.boxes:
            assert urlsplit(href).path.endswith('.html'),f'Diagram box must open HTML: {path}: {href}'
        represented=set()
        for block in doc.blocks:
            blocks+=1
            source=block['data-source'];start=int(block['data-start']);end=int(block['data-end'])
            expected=sources[source].splitlines()[start-1:end]
            if block['data-role']=='statement': expected[-1]=expected[-1].split(':=',1)[0].rstrip()
            assert block['lines']==expected,f'Altered source lines {path}: {source}:{start}-{end}'
            if block['data-role']=='declaration':
                name=block['data-declaration'];decl=parsed[source][name]
                assert (start,end)==(decl['start'],decl['end']),f'Truncated declaration {source}: {name}'
                assert name not in represented,f'Repeated declaration {path}: {name}'
                represented.add(name)
        if path.startswith('docs/modules/'):
            source=next(p for p in sources if module_page(p)==path)
            assert represented==set(parsed.get(source,{})),f'Missing complete Lean declaration: {source}'
            assert any(b['data-role']=='module' and b['data-source']==source for b in doc.blocks),f'Missing full module: {source}'
            assert (ROOT/latex_path(source)).read_text().endswith('\\end{document}\n'),f'Incomplete LaTeX: {source}'
            assert manifest['modules'][source]['source_sha256']==digest(source),f'Stale source: {source}'
    for lib in LIBRARIES:
        doc=parse(ROOT/lib/'exposition/index.html')
        assert len(doc.boxes)>=8,f'Missing logical proof map: {lib}'
        assert {'main-results','verification','proof-map','modules'}<=set(doc.ids),f'Missing standard section: {lib}'
        assert any(b['data-role']=='statement' for b in doc.blocks),f'Missing exact main theorem: {lib}'
    print(f'Verified {len(sources)} module pages and LaTeX exports; '
          f'{sum(len(d) for d in parsed.values())} explained declarations; '
          f'{blocks} exact source excerpts; {links} links/resources; three standard overviews.')


if __name__=='__main__':
    verify()
