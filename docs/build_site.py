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
from theme import asset_href, theme_head, theme_control
from math_notation import authored_strings, plain_math_text, render_prose_math
from lean_latex import (FALLBACK as LEAN_FALLBACK, PREAMBLE as LEAN_PREAMBLE,
                        refine_declaration_headers, header_lines as source_header_lines)

ROOT = Path(__file__).resolve().parents[1]
HERE = ROOT / "docs"
SITE_CSS = (HERE / "assets/site.css").read_text()
LIBRARIES = ["UnadjustedLangevin", "IPLA", "ProximalLangevin", "KineticLangevin", "KIPLMC", "AverageLMC", "WassersteinMixing"]
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
    return refine_declaration_headers(source, HELPERS.declarations(lines))


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


def shell(page, title, body):
    """Common page frame: no site menu; sub-pages start with a home breadcrumb."""
    home = relative("index.html", page)
    body_class = ' class="project-home"' if page == 'index.html' else ''
    if page != 'index.html':
        crumb = f'<a href="{home}">LangevinLean</a>'
        if body.startswith('<div class="breadcrumb">'):
            body = body.replace('<div class="breadcrumb">', f'<div class="breadcrumb">{crumb} / ', 1)
        else:
            body = f'<div class="breadcrumb">{crumb}</div>' + body
    return ('<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<meta name="robots" content="index, follow">'
            f'<title>{E(plain_math_text(title))} · LangevinLean</title>'
            f'<link rel="stylesheet" href="{relative("docs/assets/katex.css",page)}">'
            f'<link rel="stylesheet" href="{asset_href(relative("docs/assets/site.css",page), SITE_CSS)}">'
            f'<link rel="stylesheet" href="{asset_href(relative("docs/assets/references.css",page), REFERENCE_CSS)}">'
            + theme_head(relative("docs/assets/theme.css", page), relative("docs/assets/theme.js", page)) +
            f'<script defer src="{relative("docs/assets/site.js",page)}"></script>'
            f'<script defer src="{relative("docs/assets/diagrams.js",page)}"></script></head><body data-theme-family="modern"{body_class}>'
            '<a class="skip" href="#main">Skip to content</a>'
            f'<main class="container" id="main">{body}'
            '<footer class="footer"><div>'
            f'<a href="{home}">Project home</a>'
            f'<a href="{relative("docs/README.md",page)}">Reproduce the proofs</a>'
            '<a href="https://github.com/odakyildiz/LangevinLean">GitHub</a></div>'
            '<div class="footer-meta">' + theme_control() +
            '<span>Lean 4.35.0-rc3 · Mathlib</span></div></footer></main>'
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


def lean_logic(step, path, page, sources, parsed, math):
    """How the formal proof follows the mathematics, with identifiers linked to their lines."""
    if not step.get('lean'):
        return ''
    explanation = proof_source_links(resolve_prose(step['lean'], path, page), path,
                                     step.get('declarations', []), sources, parsed)
    return ('<div class="lean-logic"><div class="pane-label">How the Lean proof follows this argument</div>'
            + math(explanation) + '</div>')


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
    """A responsive logical graph whose typeset labels stay in native HTML.

    SVG foreignObject mispositions KaTeX in some iOS/WebKit versions. Native
    cards also let text grow with the user's font size; linked prerequisite
    numbers preserve every edge when the three-column graph becomes a list.
    """
    ordered = sorted(nodes, key=lambda node: (node['row'], node['col']))
    by_id = {node['id']: node for node in ordered}
    numbers = {node['id']: i for i, node in enumerate(ordered, 1)}
    prefix = 'diagram-' + hashlib.sha256((page + label).encode()).hexdigest()[:8]
    if len(by_id) != len(nodes):
        raise ValueError("Repeated proof diagram node")
    parts = [f'<div class="diagram" data-proof-diagram role="group" aria-label="{E(label)}">',
             '<p class="diagram-guide">Read from top to bottom. Each box opens its proof and Lean source. '
             '“Uses” links identify the prerequisite steps.</p><ol class="diagram-grid" data-proof-grid>']
    known = set(inventory())
    for node in ordered:
        path = node['file']
        if node.get('href'):
            # Separately generated developments link to their own proof pages.
            target, _, fragment = node['href'].partition('#')
            if not (ROOT / path).is_file() or not target.endswith('.html'):
                raise ValueError(f"Unknown proof diagram destination: {path} {node['href']}")
            href = relative(target, page) + ('#' + fragment if fragment else '')
        elif path not in known:
            raise ValueError(f"Unknown proof diagram module: {path}")
        else:
            href = relative(module_page(path), page)
        parents = node.get('parents', [])
        if any(parent not in by_id for parent in parents):
            raise ValueError(f"Unknown parent in proof diagram: {node['id']}")
        dependencies = ''.join(
            f'<a href="#{prefix}-{E(parent)}" title="{E(by_id[parent]["title"])}" '
            f'aria-label="Uses step {numbers[parent]}: {E(by_id[parent]["title"])}">{numbers[parent]:02}</a>'
            for parent in parents)
        parts.append(
            f'<li class="diagram-node{" final" if node.get("final") else ""}" '
            f'id="{prefix}-{E(node["id"])}" data-node="{E(node["id"])}" '
            f'data-parents="{E(" ".join(parents))}" '
            f'style="--diagram-row:{node["row"]+1};--diagram-col:{node["col"]+1}">'
            + f'<a class="box" href="{href}" '
            f'aria-label="Read proof: {E(node["title"])}">'
            '<div class="diagram-node-label">'
            f'<div class="diagram-node-step">Step {numbers[node["id"]]:02}</div>'
            '<div class="diagram-node-title">'+math(E(node['title']))+'</div>'
            '<div class="diagram-node-detail">'+math(E(node['detail']))+'</div>'
            f'<div class="diagram-node-file">{E(Path(path).name)} →</div></div></a>'
            + (f'<div class="diagram-dependencies"><span>Uses</span>{dependencies}</div>' if parents else '')
            + '</li>')
    return ''.join(parts) + '</ol></div>'


def declaration_header(path, name, sources, parsed, page):
    decl = parsed[path][name]
    # Keep complete binders and conclusion. Exclude := and the proof body.
    rows = source_header_lines(sources[path], decl)
    header_sources = {path: '\n' * (decl['start']-1) + '\n'.join(rows)}
    return code(path, decl['start'], decl['marker'], header_sources, page, 'statement', name)


def module_document(path, note, sources, parsed, math, catalog=None):
    page = module_page(path)
    if catalog:
        typeset = math
        math = lambda value: catalog.resolve_html(typeset(value), page)
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
    if catalog:
        body += catalog.html_dependencies(path, page=page)
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
                 + math(proof_source_links(resolve_prose(step['body'], path, page),path,step['declarations'],sources,parsed))
                 + (catalog.html_dependencies(path, index=i, page=page) if catalog else '') + '</div><div class="lean-pane">'
                 + lean_logic(step, path, page, sources, parsed, math)
                 + '<div class="pane-label">Exact Lean · complete declarations</div>' + cards + '</div></div></article>')
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
    if catalog:
        from report_citations import citation_panel, report_owner
        library = report_owner(path)
        plan = catalog.plans[library]
        location = catalog.locations.get(path)
        body += (citation_panel(library, plan['title'], plan['revision'], page, section=location)
                 if location else citation_panel(None, None, None, page))
    return page, shell(page, note['title'], render_prose_math(body, math))


def commands(value, identifier, label="Copy commands"):
    return (f'<button class="copy" type="button" data-copy="{identifier}">{E(label)}</button>'
            f'<pre class="commands"><code id="{identifier}">{E(value)}</code></pre>')


def supplement_document(page, config, sources, parsed, math, catalog=None):
    """Source corrections use the same paired mathematics and Lean template."""
    library = config['library']
    if catalog:
        typeset = math
        math = lambda value: catalog.resolve_html(typeset(value), page)
    body = (f'<header class="hero"><div class="eyebrow">{E(config["label"])}</div>'
            f'<h1>{E(config["title"])}</h1>' + reference_notice(library) +
            math(config['intro']) + '</header>' + toolbar())
    for index, section in enumerate(config['sections'], 1):
        # Statement sections pair a theorem with its exact Lean header, as on
        # the overview pages; proof sections show complete declarations.
        statement = section.get('statement', False)
        body += (f'<section class="section" id="section-{index}"><h2>{E(section["title"])}</h2>'
                 '<div class="pair"><div class="math-pane">'
                 + ('<div class="pane-label">Mathematical statement</div>' if statement else '')
                 + math(section['body']) + '</div><div class="lean-pane">'
                 + ('<div class="pane-label">Lean statement</div>' if statement else ''))
        for reference in section.get('references', []):
            path, name = reference['file'], reference['name']
            if statement:
                body += declaration_header(path, name, sources, parsed, page)
                body += (f'<p class="small"><a href="{relative(module_page(path),page)}#{anchor(name)}">'
                         'Full Lean proof and mathematical commentary →</a></p>')
                continue
            decl = parsed[path][name]
            body += code(path, decl['start'], decl['end'], sources, page,
                         name=name, identifier=anchor(name))
            body += (f'<p><a href="{relative(module_page(path),page)}#{anchor(name)}">'
                     'Complete module proof and commentary →</a></p>')
        body += '</div></div></section>'
    body += (f'<p><a href="{relative(library+"/exposition/index.html",page)}">'
             'Return to the main theorem overview</a></p>')
    if catalog:
        from report_citations import citation_panel
        plan = catalog.plans[library]
        body += citation_panel(library, plan['title'], plan['revision'], page)
    return shell(page, config['title'], render_prose_math(body, math))


class LatexProse(HTMLParser):
    """Translate the small prose HTML vocabulary; preserve TeX math verbatim."""
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.out = []
        self.list_stack = []
        self.code_depth = 0
    def handle_starttag(self, tag, attrs):
        if tag in ('p', 'div', 'h3', 'h4'): self.out.append('\n\n')
        elif tag == 'br': self.out.append('\n')
        elif tag in ('ul','ol'):
            env = 'itemize' if tag == 'ul' else 'enumerate'
            self.list_stack.append(env); self.out.append('\n\\begin{' + env + '}\n')
        elif tag == 'li': self.out.append('\n\\item ')
        elif tag in ('strong','b'): self.out.append('\\textbf{')
        elif tag in ('em','i'): self.out.append('\\emph{')
        elif tag == 'code':
            self.code_depth += 1
            self.out.append('\\texttt{')
    def handle_endtag(self, tag):
        if tag in ('p','div'): self.out.append('\n\n')
        elif tag in ('ul','ol'): self.out.append('\n\\end{' + self.list_stack.pop() + '}\n')
        elif tag == 'code':
            self.code_depth -= 1
            self.out.append('}')
        elif tag in ('strong','b','em','i'): self.out.append('}')
    def handle_data(self, text):
        self.out.append(tex_escape(text, breakable=self.code_depth > 0))


def tex_escape(text, *, breakable=False):
    # Mathematical characters in prose/headings need math fonts too. fontspec's
    # default text font otherwise silently drops Greek and subscript glyphs.
    replacements = {'\\':r'\textbackslash{}','_':r'\_','%':r'\%','&':r'\&',
                    '#':r'\#','$':r'\$','{':r'\{','}':r'\}','~':r'\textasciitilde{}',
                    '^':r'\textasciicircum{}','ᐟ':'/'}
    symbols = {
        'α':r'\alpha','β':r'\beta','γ':r'\gamma','δ':r'\delta',
        'ε':r'\varepsilon','η':r'\eta','θ':r'\theta','κ':r'\kappa',
        'λ':r'\lambda','μ':r'\mu','ν':r'\nu','ξ':r'\xi','π':r'\pi',
        'ρ':r'\rho','σ':r'\sigma','τ':r'\tau','φ':r'\varphi',
        'χ':r'\chi','ψ':r'\psi','ω':r'\omega','Δ':r'\Delta',
        'Ψ':r'\Psi','ι':r'\iota','ζ':r'\zeta','υ':r'\upsilon',
        'Γ':r'\Gamma','Σ':r'\Sigma','Ω':r'\Omega',
        'ℝ':r'\mathbb R','ℕ':r'\mathbb N','ℂ':r'\mathbb C','ℤ':r'\mathbb Z',
        '≤':r'\le','≥':r'\ge','→':r'\to','⇒':r'\Rightarrow',
        '∈':r'\in','∉':r'\notin','∀':r'\forall','∃':r'\exists','∂':r'\partial',
        '−':'-','‖':r'\Vert','√':r'\surd','∇':r'\nabla',
        '∫':r'\int','∞':r'\infty','×':r'\times','′':r'\prime',
        '↦':r'\mapsto','∘':r'\circ','⊤':r'\top','•':r'\bullet',
        '⟨':r'\langle','⟩':r'\rangle',
        '⟪':r'\langle\!\langle','⟫':r'\rangle\!\rangle',
    }
    superscripts = dict(zip('⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁿᵗˢᵀᵏ', '0123456789+-=()ntsTk'))
    subscripts = dict(zip('₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ᵥᵢᵤⱼₗ', '0123456789+-=()viujl'))
    result = []
    i = 0
    while i < len(text):
        c = text[i]
        if text.startswith('³ᐟ²', i):
            result.append(r'\ensuremath{{}^{3/2}}')
            i += 3
            continue
        if i + 1 < len(text) and text[i + 1] == '\u0304':
            result.append(r'\ensuremath{\bar{' + symbols.get(c, c) + '}}')
            i += 2
            continue
        script = superscripts if c in superscripts else subscripts if c in subscripts else None
        if script is not None:
            end = i + 1
            while end < len(text) and text[end] in script:
                end += 1
            content = ''.join(script[ch] for ch in text[i:end])
            result.append(r'\ensuremath{{}' + ('^' if script is superscripts else '_') + '{' + content + '}}')
            i = end
            continue
        if breakable and i and c.isupper() and (text[i - 1].islower() or text[i - 1].isdigit()):
            result.append(r'\allowbreak{}')
        if c in LEAN_FALLBACK:
            # Glyphs absent from the text and code fonts (for example 𝓝 in Lean names).
            result.append(r'{\leanfallback ' + c + '}')
            i += 1
            continue
        result.append(r'\ensuremath{' + symbols[c] + '}' if c in symbols else replacements.get(c, c))
        if c == '/' or (breakable and c in '_.-'):
            result.append(r'\allowbreak{}')
        i += 1
    return ''.join(result)


def latex_code(text):
    return r'\texttt{' + tex_escape(text, breakable=True) + '}'


def latex_heading(text):
    # Headings use the same authored math as prose; bookmarks use readable text.
    plain = {'\\':r'\textbackslash{}','_':r'\_','%':r'\%','&':r'\&',
             '#':r'\#','$':r'\$','{':r'\{','}':r'\}',
             '~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
    bookmark = ''.join(plain.get(c,c) for c in plain_math_text(text))
    return r'\texorpdfstring{' + latex_prose(E(text)).strip() + '}{' + bookmark + '}'


def latex_prose(value):
    math = []
    def protect(match):
        formula = html.unescape(match[0])
        # These complete expressions fit comfortably as displays, but their
        # inline placement leaves too little room after the preceding prose.
        # Keep the authored mathematical expressions unchanged.
        display_formulas = {
            r'\sqrt{2\gamma}\int_{nh}^{(n+1)h}e^{-\gamma((n+1)h-s)}dB_s',
            r'W_2(\nu_k,\pi)\le(1-m_Nh)^kW_2(\nu_0,\pi)+(33/20)(L_N/m_N)\sqrt{hD}',
            r'(N_{\psi_0},N_{\psi_1},N_{\varphi_2},N_{\varphi_3})',
        }
        if formula.startswith(r'\(') and formula[2:-2] in display_formulas:
            formula = '\n' + r'\[' + formula[2:-2] + r'\]' + '\n'
        math.append(formula)
        return f'LATEXMATHPLACEHOLDER{len(math)-1}END'
    parser = LatexProse()
    parser.feed(HELPERS.TEX.sub(protect,value))
    result = ''.join(parser.out)
    result = re.sub(r'LATEXMATHPLACEHOLDER(\d+)END',lambda m:math[int(m[1])],result)
    return re.sub(r'[ \t]+(?=\n)', '', result)


def latex_declarations(names):
    return ('\n\n' + r'{\raggedright\noindent Lean declarations: '
            + ', '.join(latex_code(name) for name in names) + r'.\par}' + '\n')


def latex_step_box(path, step, sources, parsed):
    """Exact Lean statements of a step and how the Lean proof follows it."""
    from lean_latex import step_box
    references = step.get('references') or [(path, name) for name in step.get('declarations', [])]
    return step_box(references, step.get('lean', ''), sources, parsed, latex_prose)


def latex_document(path, note, notes, catalog=None, sources=None, parsed=None):
    from full_proofs import paper_prose
    if catalog:
        paper_prose = catalog.latex_prose
    if sources is None or parsed is None:
        sources, parsed, _ = load()
    result = (r'\documentclass[11pt,a4paper]{article}' + '\n'
              + r'\usepackage{fontspec,amsmath,amssymb,amsthm,microtype}' + '\n'
              + r'\setmainfont{lmroman10-regular.otf}[BoldFont=lmroman10-bold.otf,ItalicFont=lmroman10-italic.otf,BoldItalicFont=lmroman10-bolditalic.otf]' + '\n'
              + r'\usepackage{xcolor}' + '\n' + LEAN_PREAMBLE
              + r'\usepackage[margin=25mm]{geometry}' + '\n'
              + r'\usepackage[unicode,hidelinks]{hyperref}' + '\n'
              + r'\hypersetup{pdfauthor={LangevinLean Project}}' + '\n'
              + r'\setlength{\emergencystretch}{3em}' + '\n'
              + r'\setlength{\parskip}{0.4em}' + '\n'
              + r'\setlength{\parindent}{0pt}' + '\n'
              + r'\allowdisplaybreaks[2]' + '\n' + r'\raggedbottom' + '\n'
              + r'\title{' + latex_heading(note['title']) + '}\n'
              + r'\author{LangevinLean Project}' + '\n'
              + r'\date{}' + '\n' + r'\begin{document}\maketitle' + '\n'
              + 'Draft mathematical exposition; these notes may contain mistakes.\n'
              + paper_prose(note['summary']))
    if catalog:
        result += catalog.tex_dependencies(path)
    for index, step in enumerate(note['steps'], 1):
        result += '\n\\section{' + latex_heading(step['title']) + '}\n' + paper_prose(step['body'])
        result += latex_step_box(path, step, sources, parsed)
        if catalog:
            result += catalog.tex_dependencies(path, index=index)
    if path == 'IPLA/Standalone.lean':
        included = re.findall(r'## Included source: ([\w/.]+\.lean)', (ROOT/path).read_text())
        result += '\n\\section*{Complete supporting proofs}\nThe following sections supply the supporting mathematical statements and proofs in dependency order.\n'
        for dependency in included:
            section = notes[dependency]
            result += '\n\\section{' + latex_heading(section['title']) + '}\n'
            result += paper_prose(section['summary'])
            for step in section['steps']:
                result += '\n\\subsection{' + latex_heading(step['title']) + '}\n' + paper_prose(step['body'])
                result += latex_step_box(dependency, step, sources, parsed)
    if catalog:
        result += catalog.bibliography(result)
    return result + '\n\\end{document}\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='Fail if any generated file is stale; do not write')
    args = parser.parse_args()
    sources, parsed, notes = load()
    from site_content import CONFIG, home_document, project_document
    from average_content import AVERAGE_PAGES
    from ipla_application_content import IPLA_APPLICATION_PAGES
    supplement_pages = {**AVERAGE_PAGES, **IPLA_APPLICATION_PAGES}
    from full_proofs import full_proof_inventory
    from report_links import ReportCatalog
    from report_citations import bib_outputs
    catalog = ReportCatalog(full_proof_inventory(CONFIG, notes, sources), notes, sources, parsed)
    from references import PAPERS, DEVELOPMENTS
    from paper_sources import source_metadata
    prose = list(authored_strings(notes)) + list(authored_strings(CONFIG))
    prose += list(authored_strings(supplement_pages))
    prose += list(authored_strings(PAPERS)) + list(authored_strings(DEVELOPMENTS))
    prose += list(authored_strings(source_metadata()))
    math = HELPERS.render_mathematics(prose)
    outputs = {'docs/assets/katex.css':HELPERS.katex_css(), 'docs/assets/references.css':REFERENCE_CSS}
    for path,note in notes.items():
        page, text = module_document(path,note,sources,parsed,math,catalog)
        outputs[page] = text
        outputs[latex_path(path)] = latex_document(path,note,notes,catalog,sources,parsed)
    for lib,config in CONFIG.items():
        page = lib + '/exposition/index.html'
        outputs[page] = home_document(lib,config,notes,sources,parsed,math,catalog)
        if config.get('proof'):
            overview = {'title':config['title'], 'summary':config['status'],
                        'steps':[{'title':part['title'], 'body':part['body'],
                                  'lean':part.get('lean', ''),
                                  'declarations':[reference['name'] for reference in part.get('references',[])],
                                  'references':[(reference['file'], reference['name']) for reference in part.get('references',[])]}
                                 for part in config['proof']]}
            first = config['results'][0]
            overview['steps'].insert(0,{'title':'Theorem', 'body':first['body'], 'declarations':[first['name']],
                                        'references':[(first['file'], first['name'])]})
            outputs['docs/latex/'+lib+'/Overview.tex'] = latex_document(lib+'/Overview.lean',overview,notes,catalog,sources,parsed)
    outputs['index.html'] = project_document(notes,catalog)
    from build_pbgso import outputs as pbgso_outputs, authoring_inputs as pbgso_inputs
    outputs.update(pbgso_outputs())
    from build_latent_diffusion import outputs as latent_outputs, authoring_inputs as latent_inputs
    outputs.update(latent_outputs())
    from full_proofs import full_proof_documents, full_proof_inventory
    outputs.update(full_proof_documents(CONFIG, notes, sources, catalog, parsed))
    import separate_reports
    outputs.update(separate_reports.outputs())
    outputs.update(bib_outputs({**catalog.plans, **separate_reports.plans()}))
    outputs['docs/full_proofs.json'] = json.dumps(
        catalog.plans, indent=2, ensure_ascii=False) + '\n'
    for page, config in supplement_pages.items():
        outputs[page] = supplement_document(page, config, sources, parsed, math, catalog)
    inputs = ['docs/math_notation.py','docs/report_citations.py','docs/report_links.py','docs/build_site.py','docs/full_proofs.py','docs/site_content.py','docs/classical_proofs.py','docs/entropy_content.py',
              'docs/kinetic_content.py','docs/kinetic_overviews.py','docs/average_content.py','docs/wasserstein_mixing_content.py','docs/ipla_application_content.py','docs/references.py',
              'docs/paper_sources.py','docs/paper_sources_classical.py','docs/paper_sources_kinetic.py','docs/paper_sources_wasserstein.py',
              'docs/assets/site.css','docs/assets/site.js','docs/assets/diagrams.js',
              'docs/theme.py','docs/assets/theme.css','docs/assets/theme.js']
    inputs += [lib+'/exposition/reference_audit.json' for lib in ('KineticLangevin', 'KIPLMC', 'AverageLMC', 'WassersteinMixing')]
    inputs += [lib+'/exposition/module_notes.json' for lib in LIBRARIES]
    inputs += ['lean-toolchain','lakefile.toml','lake-manifest.json']
    inputs += pbgso_inputs()
    inputs += latent_inputs()
    inputs += separate_reports.authoring_inputs() + ['docs/lean_latex.py']
    inputs += [p.relative_to(ROOT).as_posix() for p in sorted((HERE/'assets/fonts').glob('*'))
               if p.is_file()]
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
