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
from references import DEVELOPMENTS, PAPERS
from lean_latex import header_lines


class Page(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids, self.links, self.resources, self.blocks = [], [], [], []
        self.block = self.line = None
        self.line_depth = 0
        self.text = []
        self.styles = self.scripts = self.annotations = 0
        self.boxes = []
        self.robots = []
        self.references = []
    def handle_starttag(self, tag, attributes):
        attrs = dict(attributes)
        if 'data-reference' in attrs:
            self.references.append((attrs['data-reference'], attrs.get('data-publication-status')))
        if tag=='meta' and attrs.get('name','').lower()=='robots':
            self.robots.append(attrs.get('content',''))
        if 'id' in attrs: self.ids.append(attrs['id'])
        if tag=='a' and 'href' in attrs:
            self.links.append(attrs['href'])
            if 'box' in attrs.get('class','').split(): self.boxes.append(attrs['href'])
        if tag in ('script','link','img','iframe','audio','video'):
            url=attrs.get('src',attrs.get('href',''))
            if url: self.resources.append(url)
        if tag=='style': self.styles+=1
        if tag=='script': self.scripts+=1
        if tag=='annotation': self.annotations+=1
        if tag=='pre' and 'data-source' in attrs: self.block={**attrs,'lines':[]}
        if tag=='span' and self.block is not None:
            if attrs.get('class')=='line-text': self.line=''; self.line_depth=1
            elif self.line is not None: self.line_depth+=1
    def handle_endtag(self,tag):
        if tag=='style': self.styles-=1
        if tag=='script': self.scripts-=1
        if tag=='annotation': self.annotations-=1
        if tag=='span' and self.line is not None:
            self.line_depth-=1
            if not self.line_depth:
                self.block['lines'].append(self.line);self.line=None
        if tag=='pre' and self.block is not None:
            self.blocks.append(self.block);self.block=None
    def handle_data(self,data):
        if self.line is not None: self.line+=data
        elif not self.styles and not self.scripts and not self.annotations: self.text.append(data)


def digest(path):
    return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()


def verify_source_excerpt(block, sources, parsed, page=''):
    """Check exact source rows and the complete range of a theorem statement."""
    source = block['data-source']
    start, end = int(block['data-start']), int(block['data-end'])
    if block['data-role'] == 'statement':
        name = block.get('data-declaration')
        assert name in parsed.get(source, {}), f'Unknown statement {page}: {source}: {name}'
        declaration = parsed[source][name]
        assert (start, end) == (declaration['start'], declaration['marker']), \
            f'Truncated statement {page}: {source}: {name}'
        expected = header_lines(sources[source], declaration)
    else:
        expected = sources[source].splitlines()[start-1:end]
    assert block['lines'] == expected, f'Altered source lines {page}: {source}:{start}-{end}'


def verify():
    workflows=ROOT/'.github/workflows'
    assert not any(workflows.glob('*.yml')) and not any(workflows.glob('*.yaml')), 'GitHub Actions workflows are prohibited; run checks locally'
    sources,parsed,notes=load()
    from site_content import CONFIG
    from average_content import AVERAGE_PAGES
    from ipla_application_content import IPLA_APPLICATION_PAGES
    supplement_pages = {**AVERAGE_PAGES, **IPLA_APPLICATION_PAGES}
    manifest=json.loads((ROOT/'docs/coverage.json').read_text())
    from full_proofs import full_proof_inventory
    volumes=full_proof_inventory(CONFIG,notes,sources)
    assert json.loads((ROOT/'docs/full_proofs.json').read_text())==volumes,'Stale complete-proof dependency inventory'
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
    outputs=[module_page(p) for p in sources]+[l+'/exposition/index.html' for l in CONFIG]+['index.html']+list(supplement_pages)
    links=blocks=0
    for path in outputs:
        target=ROOT/path
        text=target.read_text()
        doc=parse(target)
        assert text.startswith('<!doctype html>'),f'Incomplete HTML: {path}'
        assert doc.robots==['noindex, nofollow, noarchive'],f'Missing publication indexing restrictions: {path}'
        assert len(doc.ids)==len(set(doc.ids)),f'Duplicate HTML IDs: {path}'
        assert 'katex-error' not in text,f'Invalid rendered formula: {path}'
        assert not re.search(r'\\[\[(]',''.join(doc.text)),f'Unrendered mathematics: {path}'
        if path!='index.html':
            if path.startswith('docs/modules/'):
                source_path=path.removeprefix('docs/modules/').removesuffix('.html')+'.lean'
                library=next(lib for lib in LIBRARIES if source_path.startswith(lib))
                if '/LSI/' in source_path: library+='/LSI'
            elif path in supplement_pages:
                library=supplement_pages[path]['library']
            else:
                library=path.removesuffix('/exposition/index.html')
            development=DEVELOPMENTS[library]
            assert doc.references==[(library,development['status'])],f'Missing or incorrect reference/publication notice: {path}'
            content=''.join(doc.text)
            for identifier in development['papers']:
                paper=PAPERS[identifier]
                assert paper['title'] in content and paper['authors'] in content and paper['venue'] in content,f'Incomplete citation: {path}: {identifier}'
                assert paper['url'] in doc.links,f'Missing paper link: {path}: {identifier}'
            if library in ('IPLA/LSI','ProximalLangevin'):
                assert 'unpublished' in content.lower(),f'Missing unpublished-proof notice: {path}'
        for href in doc.links+doc.resources:
            links+=1
            link=urlsplit(href)
            if link.scheme or link.netloc:
                assert href not in doc.resources,f'Network-dependent resource {path}: {href}'
                assert link.scheme in ('https','http'),f'Unexpected scheme: {href}'
                continue
            destination=(target.parent/unquote(link.path)).resolve() if link.path else target
            assert destination.is_relative_to(ROOT) and destination.is_file(),f'Broken link {path}: {href}'
            assert destination.relative_to(ROOT).parts[0] != 'papers',f'Publication must not depend on main-only paper sources: {path}: {href}'
            if link.fragment and destination.suffix=='.html':
                assert unquote(link.fragment) in parse(destination).ids,f'Broken anchor {path}: {href}'
        for href in doc.boxes:
            assert urlsplit(href).path.endswith('.html'),f'Diagram box must open HTML: {path}: {href}'
        destinations={(target.parent/unquote(urlsplit(href).path)).resolve()
                      for href in doc.links if not urlsplit(href).scheme and urlsplit(href).path}
        for destination in destinations:
            if destination.name=='FullProof.tex' and destination.is_relative_to(ROOT/'docs/latex'):
                companion=ROOT/'docs/pdf'/destination.relative_to(ROOT/'docs/latex').with_suffix('.pdf')
                assert companion.resolve() in destinations,f'Missing PDF companion link: {path}: {destination}'
        represented=set()
        for block in doc.blocks:
            blocks+=1
            source=block['data-source'];start=int(block['data-start']);end=int(block['data-end'])
            verify_source_excerpt(block, sources, parsed, path)
            if block['data-role']=='declaration':
                name=block['data-declaration'];decl=parsed[source][name]
                assert (start,end)==(decl['start'],decl['end']),f'Truncated declaration {source}: {name}'
                assert name not in represented,f'Repeated declaration {path}: {name}'
                represented.add(name)
        if path.startswith('docs/modules/'):
            # Numbered report references and the citation panel link to the
            # consolidated PDFs; individual proof boxes still have no PDF export.
            assert not re.search(r'<a[^>]*\bdownload[^>]*href="[^"]*\.pdf', text), 'Individual module pages must not offer separate PDF downloads'
            source=next(p for p in sources if module_page(p)==path)
            assert represented==set(parsed.get(source,{})),f'Missing complete Lean declaration: {source}'
            assert any(b['data-role']=='module' and b['data-source']==source for b in doc.blocks),f'Missing full module: {source}'
            assert (ROOT/latex_path(source)).read_text().endswith('\\end{document}\n'),f'Incomplete LaTeX: {source}'
            assert manifest['modules'][source]['source_sha256']==digest(source),f'Stale source: {source}'
    for lib in CONFIG:
        doc=parse(ROOT/lib/'exposition/index.html')
        volume=lib
        target=ROOT/lib/'exposition/index.html'
        destinations={(target.parent/unquote(urlsplit(href).path)).resolve()
                      for href in doc.links if not urlsplit(href).scheme and urlsplit(href).path}
        assert (ROOT/'docs/pdf'/volume/'FullProof.pdf').resolve() in destinations,f'Missing complete PDF proof: {lib}'
        assert (ROOT/'docs/latex'/volume/'FullProof.tex').resolve() in destinations,f'Missing complete LaTeX proof: {lib}'
        assert len(doc.boxes)>=8,f'Missing logical proof map: {lib}'
        assert {'main-results','verification','proof-map','modules'}<=set(doc.ids),f'Missing standard section: {lib}'
        assert any(b['data-role']=='statement' for b in doc.blocks),f'Missing exact main theorem: {lib}'
        if '/LSI' in lib:
            assert 'mathematical-proof' in doc.ids,f'Missing full entropy argument: {lib}'
            assert (ROOT/'docs/latex'/lib/'Overview.tex').is_file(),f'Missing entropy LaTeX proof: {lib}'
    for path in ['UnadjustedLangevin/exposition/main_theorem.html',
                 'UnadjustedLangevin/exposition/beginner_guide.html',
                 'UnadjustedLangevin/exposition/dist/index.html',
                 'UnadjustedLangevin/LSI/exposition/proof.html',
                 'IPLA/LSI/exposition/proof.html','IPLA/exposition/proof.html',
                 'ProximalLangevin/exposition/proof.html']:
        assert parse(ROOT/path).robots==['noindex, nofollow, noarchive'],f'Missing legacy indexing restrictions: {path}'
    from build_pdfs import verify as verify_pdfs
    verify_pdfs()
    print(f'Verified {len(sources)} module pages, LaTeX exports and complete PDF proofs; '
          f'{sum(len(d) for d in parsed.values())} explained declarations; '
          f'{blocks} exact source excerpts; {links} links/resources; {len(CONFIG)} standard overviews.')


if __name__=='__main__':
    verify()
