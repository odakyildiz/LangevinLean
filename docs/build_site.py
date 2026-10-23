#!/usr/bin/env python3
"""Build the common landing pages and a mathematical proof page for every module.

Python standard library + Node (vendored KaTeX); no network or Python packages.
The hand-authored module_notes.json files are mandatory, declaration-complete
inputs. Exact source is always read from Lean, never copied into annotations.
"""
from __future__ import annotations

import argparse
import hashlib
import html
import importlib.util
import json
import os
from pathlib import Path
import re
from html.parser import HTMLParser
from references import REFERENCE_CSS, reference_notice

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / "docs"
LIBRARIES = ["UnadjustedLangevin", "IPLA", "ProximalLangevin", "KineticLangevin", "KIPLMC"]
SPEC = importlib.util.spec_from_file_location("proof_helpers", ROOT / "UnadjustedLangevin/exposition/build_document.py")
HELPERS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(HELPERS)
E = html.escape


def read_json(path):
    return json.loads((ROOT / path).read_text())


def relative(target, page):
    return Path(os.path.relpath(ROOT / target, (ROOT / page).parent)).as_posix()


def module_page(path):
    return "docs/modules/" + path.removesuffix(".lean") + ".html"


def latex_path(path):
    return "docs/latex/" + path.removesuffix(".lean") + ".tex"


def anchor(name):
    # Preserve case: Lean names are case-sensitive.
    return "decl-" + re.sub(r"[^\w.-]", "-", name)


def inventory():
    return sorted([f"{lib}.lean" for lib in LIBRARIES] + [p.relative_to(ROOT).as_posix()
        for lib in LIBRARIES for p in (ROOT / lib).rglob("*.lean")])


def declarations(source):
    # Give instance commands the same boundaries as named declarations. Anonymous
    # probability instances use stable source-line labels instead of Lean's
    # generated internal names. Keep the legacy teaching parser unchanged.
    lines = source.splitlines()
    for i,line in enumerate(HELPERS.mask_comments(lines)):
        match = re.match(r'^(?P<prefix>(?:local |noncomputable |private )*)instance\b(?P<tail>.*)',line)
        if match:
            tail = match['tail']
            named = re.match(r'\s+([\w.\']+)\s*',tail)
            replacement = 'def' + (tail if named else f' instance_at_{i+1}' + tail)
            lines[i] = match['prefix'].replace('local ','') + replacement
    return HELPERS.declarations(lines)


def load():
    paths = inventory()
    sources = {p: (ROOT / p).read_text() for p in paths}
    parsed = {p: declarations(s) for p, s in sources.items()
              if p != "IPLA/Standalone.lean"}
    notes = {}
    for lib in LIBRARIES:
        notes.update(read_json(f"{lib}/exposition/module_notes.json"))
    if set(paths) != set(notes):
        raise ValueError(f"Module coverage mismatch: missing {set(paths)-set(notes)}, extra {set(notes)-set(paths)}")
    for path, note in notes.items():
        if not note.get("title") or not note.get("summary"):
            raise ValueError(f"Missing title or mathematical summary: {path}")
        passages = [note['title'],note['summary']] + [s['body'] for s in note['steps']]
        if any(re.search(r'[\x00-\x09\x0b-\x1f]',text) for text in passages):
            raise ValueError(f"Control character in authored prose: {path}; check escaped TeX commands")
        names = [n for step in note["steps"] for n in step["declarations"]]
        if path != "IPLA/Standalone.lean" and set(names) != set(parsed[path]):
            raise ValueError(f"Declaration coverage {path}: missing {set(parsed[path])-set(names)}, unknown {set(names)-set(parsed[path])}")
        if len(names) != len(set(names)):
            raise ValueError(f"Repeated explained declaration: {path}")
        for step in note["steps"]:
            if not step.get("body") or not step.get("title") or (not step["declarations"] and parsed.get(path)):
                raise ValueError(f"Incomplete proof explanation: {path} {step}")
    return sources, parsed, notes


def imports(source):
    return [name.replace(".", "/") + ".lean" for name in re.findall(r"^import ([\w.]+)\s*$", source, re.M)]


def shell(page, title, body, active=None):
    navigation=[('UnadjustedLangevin','ULA · SC'),
                ('UnadjustedLangevin/LSI','ULA · LSI'),('IPLA','IPLA'),
                ('ProximalLangevin','Proximal'), ('KineticLangevin','Kinetic'), ('KIPLMC','KIPLMC')]
    nav = ''.join(f'<a href="{relative(lib+"/exposition/index.html",page)}"' +
                  (' aria-current="page"' if active == lib else '') + f'>{label}</a>'
                  for lib,label in navigation)
    return ('<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<meta name="robots" content="noindex, nofollow, noarchive">'
            f'<title>{E(title)} · LangevinLean</title>'
            f'<link rel="stylesheet" href="{relative("docs/assets/katex.css",page)}">'
            f'<link rel="stylesheet" href="{relative("docs/assets/site.css",page)}">'
            f'<link rel="stylesheet" href="{relative("docs/assets/references.css",page)}">'
            f'<script defer src="{relative("docs/assets/site.js",page)}"></script></head><body>'
            '<a class="skip" href="#main">Skip to content</a><header class="site-nav">'
            f'<a class="brand" href="{relative("index.html",page)}">LangevinLean</a>'
            f'<nav aria-label="Main navigation">{nav}</nav></header>'
            f'<main class="container" id="main">{body}'
            '<footer class="footer"><div>'
            f'<a href="{relative("index.html",page)}">Project home</a>'
            f'<a href="{relative("docs/README.md",page)}">Reproduce the proofs</a>'
            '<a href="https://github.com/odakyildiz/LangevinLean">GitHub</a></div>'
            '<span>Lean 4.35.0-rc3 · Mathlib · Mathematical exposition and formal proofs</span></footer></main>'
            '<div id="action-status" role="status" aria-live="polite"></div></body></html>\n')


def toolbar():
    return ('<div class="toolbar"><div><label for="reading-mode">Reading view </label>'
            '<select id="reading-mode"><option value="paired">Mathematics + Lean</option>'
            '<option value="math">Mathematics</option><option value="lean">Lean</option></select></div>'
            '<button id="print-page" type="button">Print page</button></div>')


def code(path, start, end, sources, page, role="declaration", name=None, identifier=""):
    attrs = (f' data-declaration="{E(name)}"' if name else '')
    identifier_attr = f' id="{identifier}"' if identifier else ''
    line_prefix = anchor(name) + ('-header' if role=='statement' else '') if name else (identifier or 'source')
    if role=='proof-fragment': line_prefix=identifier
    rows = ''.join(f'<span class="lean-line" id="{line_prefix}-L{n}"><span class="line-number" aria-hidden="true">{n}</span>'
                   f'<span class="line-text">{HELPERS.highlight(line)}</span></span>'
                   for n, line in enumerate(sources[path].splitlines()[start-1:end], start))
    return (f'<div class="code-wrap"{identifier_attr}><div class="code-meta">'
            f'<a href="{relative(path,page)}">{E(path)}:{start}</a>'
            + (f'<code>{E(name)}</code>' if name else '<span>Complete module context</span>')
            + f'<button class="copy copy-lean" type="button" data-copy-lean aria-label="Copy Lean code from {E(path)}, lines {start} to {end}">Copy Lean</button></div>'
            f'<pre class="lean-code" data-source="{path}" data-start="{start}" data-end="{end}" '
            f'data-role="{role}"{attrs}><code>{rows}</code></pre></div>')


def proof_source_links(prose, path, names, sources, parsed):
    """Make authored Lean references point to the actual lines they explain."""
    if not names:
        return prose
    lines = sources[path].splitlines()
    def link(match):
        token = html.unescape(match[1])
        if not re.fullmatch(r"[\w'.]+",token) or len(token)<4:
            return match[0]
        for name in names:
            decl=parsed[path][name]
            for n in range(decl['start'],decl['end']+1):
                if re.search(r"(?<![\w'])"+re.escape(token)+r"(?![\w'])",lines[n-1]):
                    return (f'<a class="proof-source-ref" href="#{anchor(name)}-L{n}" '
                            f'title="Corresponding Lean, line {n}">{match[0]}</a>')
        return match[0]
    parts=re.split(r'(<a\b[^>]*>.*?</a>)',prose,flags=re.S)
    return ''.join(part if i%2 else re.sub(r'<code>([^<]+)</code>',link,part)
                   for i,part in enumerate(parts))


def resolve_prose(text, path, page):
    """Repair links copied from existing expositions when moving the prose."""
    def link(match):
        href = html.unescape(match[1])
        if re.match(r"https?://", href):
            return match[0]
        if href.startswith("#"):
            if path.startswith("UnadjustedLangevin/LSI/"):
                legacy = "UnadjustedLangevin/LSI/exposition/proof.html"
            elif path.startswith("IPLA/LSI/"):
                legacy = "IPLA/LSI/exposition/proof.html"
            elif path.startswith("ProximalLangevin/"):
                legacy = "ProximalLangevin/exposition/proof.html"
            else:
                legacy = "UnadjustedLangevin/exposition/dist/index.html"
            return f'href="{relative(legacy,page)}{E(href,quote=True)}"'
        filepart, _, fragment = href.partition('#')
        if filepart.endswith('.lean'):
            candidates = [filepart, str(Path(path).parent / filepart)]
            candidates += [p for p in inventory() if p.endswith('/' + filepart.split('/')[-1])]
            for target in candidates:
                if (ROOT / target).is_file():
                    return f'href="{relative(module_page(target),page)}"'
        return match[0]
    return re.sub(r'href="([^"]+)"', link, text)


def proof_diagram(nodes, page, math, label="Proof workflow"):
    """Explicit logical graph, with source-checked HTML destinations."""
    row_height, box_height = 148, 112
    width, height = 960, (max(n['row'] for n in nodes) + 1) * row_height + 12
    coords = {n['id']: (n['col'] * 316 + 12, n['row'] * row_height + 12) for n in nodes}
    parts = [f'<div class="diagram"><svg viewBox="0 0 {width} {height}" role="group" aria-label="{E(label)}">',
             f'<title>{E(label)}</title><desc>Follow the arrows. Every box opens an HTML proof page with mathematics and exact Lean.</desc>',
             '<defs><marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M 0 0 L 10 5 L 0 10 z" fill="#9aafa4"/></marker></defs>']
    lane_counts = {}
    for node in nodes:
        x, y = coords[node['id']]
        for parent in node.get('parents', []):
            px, py = coords[parent]
            lane = lane_counts.get(py,0)
            lane_counts[py] = lane+1
            middle = py+box_height+8+3*(lane%6)
            if py == y:
                # A same-row dependency travels through the gap, never through
                # the body of either box (proximal → Moreau calculus).
                route = f'M {px+290} {py+box_height/2:g} H {x}' if px<x else f'M {px} {py+box_height/2:g} H {x+290}'
            elif y-py == row_height:
                route = f'M {px+145} {py+box_height} V {middle} H {x+145} V {y}'
            else:
                # Dependencies that skip a layer use the outside gutter.
                gutter = 944+4*(lane%3)
                route = f'M {px+145} {py+box_height} V {middle} H {gutter} V {y-12-4*(lane%4)} H {x+145} V {y}'
            parts.append(f'<path class="edge" marker-end="url(#arrow)" d="{route}"/>')
    for node in nodes:
        x, y = coords[node['id']]
        path = node['file']
        if path not in inventory():
            raise ValueError(f"Unknown proof diagram module: {path}")
        parts.append(f'<a class="box{" final" if node.get("final") else ""}" href="{relative(module_page(path),page)}" tabindex="0" aria-label="Read proof: {E(node["title"])}">'
                     f'<rect x="{x}" y="{y}" width="290" height="{box_height}" rx="7"/>'
                     f'<foreignObject x="{x+14}" y="{y+11}" width="262" height="90">'
                     '<div xmlns="http://www.w3.org/1999/xhtml" class="diagram-node-label">'
                     '<div class="diagram-node-title">'+math(E(node['title']))+'</div>'
                     '<div class="diagram-node-detail">'+math(E(node['detail']))+'</div>'
                     f'<div class="diagram-node-file">{E(Path(path).name)} →</div></div></foreignObject></a>')
    return ''.join(parts) + '</svg></div>'


def declaration_header(path, name, sources, parsed, page):
    decl = parsed[path][name]
    # Keep complete binders and conclusion. Exclude := and the proof body.
    lines = sources[path].splitlines()
    rows = lines[decl['start']-1:decl['marker']]
    rows[-1] = rows[-1].split(':=', 1)[0].rstrip()
    header_sources = {path: '\n' * (decl['start']-1) + '\n'.join(rows)}
    return code(path, decl['start'], decl['marker'], header_sources, page, 'statement', name)


def module_document(path, note, sources, parsed, math):
    page = module_page(path)
    lib = next(l for l in LIBRARIES if path.startswith(l))
    if '/LSI/' in path: lib += '/LSI'
    local_imports = [p for p in imports(sources[path]) if p in sources]
    users = [p for p, source in sources.items() if path in imports(source)]
    summary = math(resolve_prose(note['summary'], path, page))
    body = (f'<div class="breadcrumb"><a href="{relative(lib+"/exposition/index.html",page)}">'
            f'{lib} proof overview</a> / {E(path)}</div><header class="hero module-hero">'
            '<div class="eyebrow">Module proof · Mathematics alongside Lean</div>'
            f'<h1>{E(note["title"])}</h1>' + reference_notice(lib, supporting=True) + summary +
            f'<p class="small"><a href="{relative(path,page)}">Open Lean source</a> · '
            f'<a href="{relative(latex_path(path),page)}" download>Download LaTeX proof</a> · '
            '<a href="#verification">Verify this module</a></p></header>')
    body += '<nav class="jump-nav" aria-label="Module contents"><a href="#proof">Mathematical proof + Lean</a><a href="#dependencies">Proof dependencies</a><a href="#complete-source">Complete source</a></nav>'
    body += toolbar() + '<section id="proof" class="section"><h2>Statement and proof</h2>'
    if not note['steps']:
        body += '<p>This module assembles or audits the proved declarations in the linked dependency pages below.</p>'
    if path == "IPLA/Standalone.lean":
        included = re.findall(r"## Included source: ([\w/.]+\.lean)", sources[path])
        body += '<p>Each included source has a complete mathematical proof in the atlas:</p><div class="dependencies">' + ''.join(
            f'<a href="{relative(module_page(p),page)}">{E(p)}</a>' for p in included) + '</div>'
    for i, step in enumerate(note['steps'], 1):
        cards = ''.join(code(path, parsed[path][n]['start'], parsed[path][n]['end'], sources, page,
                             name=n, identifier=anchor(n)) for n in step['declarations'])
        if not step['declarations'] and path != 'IPLA/Standalone.lean':
            cards = code(path,1,len(sources[path].splitlines()),sources,page,'context',identifier=f'context-step-{i}')
        body += (f'<article class="proof-step" id="step-{i}"><h3><span class="step-number">{i:02}</span>'
                 f'{E(step["title"])} <a class="permalink" href="#step-{i}" aria-label="Link to proof step {i}">§</a></h3>'
                 '<div class="pair"><div class="math-pane"><div class="pane-label">Mathematical statement and proof</div>'
                 + math(proof_source_links(resolve_prose(step['body'], path, page),path,step['declarations'],sources,parsed)) + '</div><div class="lean-pane">'
                 '<div class="pane-label">Exact Lean · complete declarations</div>' + cards + '</div></div></article>')
    body += '</section><section class="section" id="dependencies"><h2>Proof dependencies</h2>'
    if local_imports:
        body += '<p class="section-intro">The proof imports these local modules. Each box opens its complete parallel proof.</p>'
        nodes = [dict(id=str(i), row=i//3, col=i%3, file=p, title=Path(p).stem, detail='Imported proof module') for i,p in enumerate(local_imports)]
        body += proof_diagram(nodes, page, math, "Imported mathematical proof modules")
    else:
        body += '<p>This module has no local imports; its external dependencies are Mathlib.</p>'
    if users:
        body += '<h3 style="margin-top:24px">Used by</h3><div class="dependencies">' + ''.join(f'<a href="{relative(module_page(p),page)}">{E(p)}</a>' for p in users) + '</div>'
    body += '</section><section class="section" id="verification"><h2>Verify this module</h2>'
    command = f'lake build {lib.split("/")[0]}\nlake env lean {path}\npython3 docs/verify_site.py'
    body += commands(command, 'module-commands')
    body += '<p class="small">Run from the repository root after installing elan and fetching the pinned Mathlib cache with <code>lake exe cache get</code>. Lean checks the formal proof; the documentation verifier checks source fidelity, mathematical annotation coverage, and links.</p></section>'
    body += '<details class="source-section" id="complete-source"><summary>Complete Lean file, including imports and shared variables</summary>'
    body += code(path, 1, len(sources[path].splitlines()), sources, page, 'module') + '</details><div class="section"></div>'
    return page, shell(page, note['title'], body, lib)


def commands(value, identifier, label="Copy commands"):
    return (f'<button class="copy" type="button" data-copy="{identifier}">{E(label)}</button>'
            f'<pre class="commands"><code id="{identifier}">{E(value)}</code></pre>')


class LatexProse(HTMLParser):
    """Translate the small prose HTML vocabulary; preserve TeX math verbatim."""
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.out = []
        self.list_stack = []
    def handle_starttag(self, tag, attrs):
        if tag in ('p', 'div', 'h3', 'h4'): self.out.append('\n\n')
        elif tag == 'br': self.out.append('\n')
        elif tag in ('ul','ol'):
            env = 'itemize' if tag == 'ul' else 'enumerate'
            self.list_stack.append(env); self.out.append('\n\\begin{' + env + '}\n')
        elif tag == 'li': self.out.append('\n\\item ')
        elif tag in ('strong','b'): self.out.append('\\textbf{')
        elif tag in ('em','i'): self.out.append('\\emph{')
        elif tag == 'code': self.out.append('\\texttt{')
    def handle_endtag(self, tag):
        if tag in ('p','div'): self.out.append('\n\n')
        elif tag in ('ul','ol'): self.out.append('\n\\end{' + self.list_stack.pop() + '}\n')
        elif tag in ('strong','b','em','i','code'): self.out.append('}')
    def handle_data(self, text):
        self.out.append(tex_escape(text))


def tex_escape(text):
    # Mathematical characters in prose/headings need math fonts too. fontspec's
    # default text font otherwise silently drops Greek and subscript glyphs.
    replacements = {'\\':r'\textbackslash{}','_':r'\_','%':r'\%','&':r'\&',
                    '#':r'\#','$':r'\$','{':r'\{','}':r'\}','~':r'\textasciitilde{}',
                    '^':r'\textasciicircum{}','²':r'\ensuremath{{}^{2}}',
                    '³':r'\ensuremath{{}^{3}}','₁':r'\ensuremath{{}_{1}}',
                    '₂':r'\ensuremath{{}_{2}}','ᐟ':'/',
                    'μ':r'\ensuremath{\mu}','α':r'\ensuremath{\alpha}',
                    'θ':r'\ensuremath{\theta}','β':r'\ensuremath{\beta}',
                    '≤':r'\ensuremath{\le}', 'ℝ':r'\ensuremath{\mathbb R}'}
    return r'\ensuremath{{}^{3/2}}'.join(''.join(replacements.get(c,c) for c in part)
                                       for part in text.split('³ᐟ²'))


def latex_prose(value):
    math = []
    def protect(match):
        math.append(html.unescape(match[0]))
        return f'LATEXMATHPLACEHOLDER{len(math)-1}END'
    parser = LatexProse()
    parser.feed(HELPERS.TEX.sub(protect,value))
    result = ''.join(parser.out)
    return re.sub(r'LATEXMATHPLACEHOLDER(\d+)END',lambda m:math[int(m[1])],result)


def latex_document(path, note, notes):
    result = (r'\documentclass[11pt]{article}' + '\n' + r'\usepackage{fontspec,amsmath,amssymb,amsthm,hyperref}' + '\n'
              + r'\usepackage[margin=1in]{geometry}' + '\n' + r'\setlength{\emergencystretch}{3em}' + '\n'
              + r'\title{' + tex_escape(note['title']) + '}\n'
              + r'\author{LangevinLean mathematical exposition}' + '\n'
              + r'\date{}' + '\n' + r'\begin{document}\maketitle' + '\n'
              + (r'\noindent Source module: \texttt{' + tex_escape(path) + '}. ' if not path.endswith('/Overview.lean') else '')
              + 'Compile this proof document with XeLaTeX or LuaLaTeX. The accompanying HTML pairs the mathematical argument with the exact Lean statements and records the scope of the formalization.\n'
              + latex_prose(note['summary']))
    for step in note['steps']:
        result += '\n\\section{' + tex_escape(step['title']) + '}\n' + latex_prose(step['body'])
        if step['declarations']:
            result += '\n\n\\noindent Lean declarations: ' + ', '.join(r'\texttt{' + tex_escape(n) + '}' for n in step['declarations']) + '.\n'
    if path == 'IPLA/Standalone.lean':
        included = re.findall(r'## Included source: ([\w/.]+\.lean)', (ROOT/path).read_text())
        result += '\n\\section*{Complete mathematical dependency proofs}\nThe following sections reproduce the mathematical statements and proofs of every source module included in the generated Lean bundle, in dependency order.\n'
        for dependency in included:
            section = notes[dependency]
            result += '\n\\section{' + tex_escape(section['title']) + '}\n'
            result += '\\noindent Source: \\texttt{' + tex_escape(dependency) + '}.\n' + latex_prose(section['summary'])
            for step in section['steps']:
                result += '\n\\subsection{' + tex_escape(step['title']) + '}\n' + latex_prose(step['body'])
                result += '\n\n\\noindent Lean declarations: ' + ', '.join(r'\texttt{' + tex_escape(n) + '}' for n in step['declarations']) + '.\n'
    return result + '\n\\end{document}\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='Fail if any generated file is stale; do not write')
    args = parser.parse_args()
    sources, parsed, notes = load()
    from site_content import CONFIG, home_document, project_document
    prose = [note['summary'] for note in notes.values()]
    prose += [step['body'] for note in notes.values() for step in note['steps']]
    prose += [result['body'] for config in CONFIG.values() for result in config['results']]
    prose += [part['body'] for config in CONFIG.values() for part in config.get('proof', [])]
    prose += [node[key] for config in CONFIG.values() for node in config['diagram']
              for key in ('title', 'detail')]
    math = HELPERS.render_mathematics(prose)
    outputs = {'docs/assets/katex.css':HELPERS.katex_css(), 'docs/assets/references.css':REFERENCE_CSS}
    for path,note in notes.items():
        page, text = module_document(path,note,sources,parsed,math)
        outputs[page] = text
        outputs[latex_path(path)] = latex_document(path,note,notes)
    for lib,config in CONFIG.items():
        page = lib + '/exposition/index.html'
        outputs[page] = home_document(lib,config,notes,sources,parsed,math)
        if config.get('proof'):
            overview = {'title':config['title'], 'summary':config['status'],
                        'steps':[{'title':part['title'], 'body':part['body']+('<p><strong>Formal scope.</strong> '+part['note']+'</p>' if part.get('note') else ''),
                                  'declarations':[reference['name'] for reference in part.get('references',[])]}
                                 for part in config['proof']]}
            overview['steps'].insert(0,{'title':'Theorem', 'body':config['results'][0]['body'], 'declarations':[]})
            outputs['docs/latex/'+lib+'/Overview.tex'] = latex_document(lib+'/Overview.lean',overview,notes)
    outputs['index.html'] = project_document(notes)
    inputs = ['docs/build_site.py','docs/site_content.py','docs/entropy_content.py',
              'docs/kinetic_content.py','docs/kinetic_overviews.py','docs/references.py',
              'docs/assets/site.css','docs/assets/site.js']
    inputs += [lib+'/exposition/reference_audit.json' for lib in ('KineticLangevin', 'KIPLMC')]
    inputs += [lib+'/exposition/module_notes.json' for lib in LIBRARIES]
    inputs += ['lean-toolchain','lakefile.toml','lake-manifest.json']
    inputs += ['UnadjustedLangevin/exposition/build_document.py']
    inputs += [p.relative_to(ROOT).as_posix() for p in sorted(HELPERS.VENDOR.rglob('*')) if p.is_file()]
    manifest = {'format':1,'modules':{},'inputs':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in inputs}}
    for path,note in notes.items():
        manifest['modules'][path] = {'source_sha256':hashlib.sha256(sources[path].encode()).hexdigest(),
            'page':module_page(path),'latex':latex_path(path),'declarations':list(parsed.get(path,{})),
            'proof_steps':len(note['steps']),'generated_bundle':path=='IPLA/Standalone.lean'}
    manifest['outputs'] = {p:hashlib.sha256(text.encode()).hexdigest() for p,text in outputs.items()}
    outputs['docs/coverage.json'] = json.dumps(manifest,indent=2,ensure_ascii=False)+'\n'
    stale = []
    for path,text in outputs.items():
        target = ROOT/path
        if args.check:
            if not target.is_file() or target.read_text()!=text: stale.append(path)
        else:
            target.parent.mkdir(parents=True,exist_ok=True); target.write_text(text)
    if stale: raise SystemExit('Stale generated pages:\n'+'\n'.join(stale))
    print(f'{"Checked" if args.check else "Built"} {len(notes)} module proof pages and LaTeX files, '
          f'{sum(len(d) for d in parsed.values())} declarations, and {len(CONFIG)} method overviews.')


if __name__ == '__main__':
    main()
