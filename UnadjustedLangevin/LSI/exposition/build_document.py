#!/usr/bin/env python3
"""Build the offline LSI proof page from explanations and exact Lean sources.

Uses the repository's existing KaTeX, source parser and syntax highlighting.
Only Python's standard library and Node.js are required.
"""
from __future__ import annotations

import hashlib
import html
import importlib.util
import json
import os
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LSI = HERE.parent
OUT = HERE / "index.html"
SPEC = importlib.util.spec_from_file_location(
    "ula_proof_helpers", ROOT / "UnadjustedLangevin/exposition/build_document.py")
SHARED = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SHARED)


def slug(value):
    return re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")


def relative(path):
    return Path(os.path.relpath(ROOT / path, HERE)).as_posix()


def load_inputs():
    content = json.loads((HERE / "chapters.json").read_text())
    audit = json.loads((HERE / "reference_audit.json").read_text())
    sources = {}

    def visit(path):
        if path in sources:
            return
        target = ROOT / path
        if not target.resolve().is_relative_to(ROOT) or not target.is_file():
            raise ValueError(f"Missing local source: {path}")
        source = target.read_text()
        sources[path] = source
        for name in re.findall(r"^import ([\w.]+)\s*$", source, re.M):
            dependency = name.replace(".", "/") + ".lean"
            if (ROOT / dependency).is_file():
                visit(dependency)
            elif not name.startswith("Mathlib."):
                raise ValueError(f"Unexpected external import: {name}")

    for path in sorted(LSI.glob("*.lean")):
        visit(path.relative_to(ROOT).as_posix())
    audit_ids = set()
    for check in audit["checks"]:
        identifier = check["id"]
        if not re.fullmatch(r"[a-z][a-z0-9-]*", identifier) or identifier in audit_ids:
            raise ValueError(f"Invalid or repeated audit id: {identifier}")
        audit_ids.add(identifier)
        for path in check["lean_files"]:
            visit(path)
    for path in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]:
        sources[path] = (ROOT / path).read_text()
    parsed = {path: SHARED.declarations(source.splitlines())
              for path, source in sources.items() if path.endswith(".lean")}
    seen_ids, represented = set(), set()
    for section in content["sections"]:
        for item in [section, *section["steps"]]:
            identifier = item["id"]
            if not re.fullmatch(r"[a-z][a-z0-9-]*", identifier) or identifier in seen_ids:
                raise ValueError(f"Invalid or repeated content id: {identifier}")
            seen_ids.add(identifier)
        for step in section["steps"]:
            if not step["body"].strip() or not step["declarations"]:
                raise ValueError(f"Missing explanation or source: {step['id']}")
            for declaration in step["declarations"]:
                key = declaration["file"], declaration["name"]
                if key[0] not in parsed or key[1] not in parsed[key[0]]:
                    raise ValueError(f"Unknown Lean declaration: {key}")
                represented.add(key)
    expected = {(path, name) for path, declarations in parsed.items()
                if path.startswith("UnadjustedLangevin/LSI/") for name in declarations}
    if missing := expected - represented:
        raise ValueError(f"LSI declarations without an explanation: {sorted(missing)}")
    return content, audit, sources, parsed, represented


def source_id(path, line):
    return f"L-{slug(path)}-{line}"


def code_block(path, start, end, sources, prefix=None, name=None):
    lines = sources[path].splitlines()
    output = []
    for n in range(start, end + 1):
        identifier = f"{prefix}-{n}" if prefix else source_id(path, n)
        code = SHARED.highlight(lines[n - 1]) if path.endswith(".lean") else html.escape(lines[n - 1])
        output.append(f'<span class="line" id="{identifier}"><a class="line-number" '
                      f'href="#{source_id(path, n)}" aria-label="Source line {n}">{n}</a>'
                      f'<span class="line-text">{code}</span></span>')
    role = "declaration" if name else "module"
    named = f' data-declaration="{html.escape(name)}"' if name else ""
    return (f'<pre class="lean-code" data-source="{path}" data-start="{start}" '
            f'data-end="{end}" data-role="{role}"{named}><code>' +
            "".join(output) + '</code></pre>')


def declaration_card(declaration, step_id, index, sources, parsed, shown):
    path, name = declaration["file"], declaration["name"]
    decl = parsed[path][name]
    location = f"{path}:{decl['start']}"
    key = path, name
    if key in shown:
        return (f'<div class="source-repeat"><p><strong>Lean · <code>{html.escape(name)}</code></strong></p>'
                f'<p><a href="#{shown[key]}">Read the complete declaration shown earlier</a> · '
                f'<a class="module-link" href="#{source_id(path, decl["start"])}">Source file</a>'
                '</p></div>')
    shown[key] = f"X-{step_id}-{index}-{decl['start']}"
    return (f'<details class="lean-proof" open><summary>Exact Lean · '
            f'<code>{html.escape(name)}</code></summary><div class="code-label">'
            f'<a class="module-link" href="#{source_id(path, decl["start"])}">'
            f'{location}</a><a href="{relative(path)}">Open file</a></div>' +
            code_block(path, decl["start"], decl["end"], sources,
                       f"X-{step_id}-{index}", name) + '</details>')


def audit_section(audit, math):
    source = audit["source"]
    references = f'<a href="{html.escape(source["url"])}">Reference paper</a>'
    if source.get("supplement_url"):
        label = 'Official supplement (ZIP)' if source['supplement_url'].endswith('.zip') else 'Supplementary proof'
        references += (f' · <a href="{html.escape(source["supplement_url"])}">'
                       f'{label}</a>')
    if source.get("author_full_url"):
        references += (f' · <a href="{html.escape(source["author_full_url"])}">'
                       'Author-hosted full PDF</a>')
    rows = []
    for check in audit["checks"]:
        links = []
        for path in check["lean_files"]:
            links.append(f'<a href="#module-{slug(path)}"><code>{Path(path).name}</code></a>')
        status = html.escape(check["status"])
        claim = math(html.escape(check["claim"]))
        note = math(html.escape(check["note"]))
        rows.append(f'<tr id="audit-{check["id"]}"><th scope="row">{claim}</th>'
                    f'<td>{html.escape(check["paper_location"])}</td>'
                    f'<td><span class="badge" data-status="{slug(check["status"])}">{status}</span><p>{note}</p>' +
                    ' · '.join(links) + '</td></tr>')
    return ('<section class="chapter reference-audit" id="reference-audit">'
            '<h2><span class="chapter-number">Reference audit</span>'
            'What matches the paper</h2><div class="chapter-intro"><p>' + references +
            '</p><p>' + math(html.escape(audit["verdict"])) + '</p></div>'
            '<div class="table-wrap"><table><thead><tr><th scope="col">Claim</th>'
            '<th scope="col">Paper location</th><th scope="col">Lean comparison</th>'
            '</tr></thead><tbody>' + ''.join(rows) + '</tbody></table></div></section>')


def build():
    content, audit, sources, parsed, represented = load_inputs()
    prose = [content["intro"], content["closing"], audit["verdict"]]
    prose.extend(html.escape(check[key]) for check in audit["checks"] for key in ["claim", "note"])
    for section in content["sections"]:
        prose.append(section["intro"])
        prose.extend(step["body"] for step in section["steps"])
    math = SHARED.render_mathematics(prose)
    toc, chapters, shown = [], [], {}
    for number, section in enumerate(content["sections"], 1):
        toc.append(f'<li><a href="#{section["id"]}">{html.escape(section["title"])}</a></li>')
        steps = []
        for index, step in enumerate(section["steps"], 1):
            cards = ''.join(declaration_card(d, step["id"], n, sources, parsed, shown)
                            for n, d in enumerate(step["declarations"], 1))
            steps.append(f'<article class="proof-step" id="{step["id"]}">'
                         f'<h3>{number}.{index} · {html.escape(step["title"])} '
                         f'<a class="permalink" href="#{step["id"]}" aria-label="Link to this step">§</a>'
                         '</h3><div class="proof-pair"><div class="math-explanation">' +
                         math(step["body"]) + '</div><div class="lean-proofs">' + cards +
                         '</div></div></article>')
        chapters.append(f'<section class="chapter" id="{section["id"]}">'
                        f'<h2><span class="chapter-number">Chapter {number}</span>'
                        f'{html.escape(section["title"])}</h2><div class="chapter-intro">' +
                        math(section["intro"]) + '</div>' + ''.join(steps) + '</section>')
    modules = []
    for path in sorted(sources, key=lambda p: (not p.startswith("UnadjustedLangevin/LSI/"), p)):
        modules.append(f'<details class="source-module" id="module-{slug(path)}" data-module="{path}">'
                       f'<summary>{path}</summary><div class="module-actions">'
                       f'<button type="button" class="copy-source" data-source="{path}">Copy file</button>'
                       f'<button type="button" class="save-source" data-source="{path}">Save file</button>'
                       f'<a href="{relative(path)}">Open repository file</a></div>' +
                       code_block(path, 1, len(sources[path].splitlines()), sources) + '</details>')
    appendix = ('<section class="chapter" id="sources"><h2>'
                '<span class="chapter-number">Source appendix</span>Complete sources</h2>'
                '<div class="chapter-intro"><p>Every LSI module and its local Lean dependencies are embedded '
                'below, together with the pinned build configuration. Excerpts above are read directly '
                'from these files. The audit module checks the logical axioms used by the results.</p>'
                '<pre><code>lake build UnadjustedLangevin IPLA +UnadjustedLangevin.LSI.Check\n'
                'lake env lean UnadjustedLangevin/LSI/Check.lean</code></pre></div>'
                '<div class="source-toolbar"><label for="source-search">Find a source file</label> '
                '<input id="source-search" type="search" placeholder="e.g. LSI/OneStep" '
                'aria-controls="source-files"><span id="source-count" aria-live="polite"></span>'
                '</div><div id="source-files">' +
                ''.join(modules) + '</div></section>')
    manifest = {
        "format": 1,
        "sections": len(content["sections"]),
        "steps": sum(len(s["steps"]) for s in content["sections"]),
        "explained_declarations": len(represented),
        "sources": {path: hashlib.sha256(source.encode()).hexdigest() for path, source in sources.items()},
        "inputs": {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
                   for name in ["chapters.json", "reference_audit.json", "page.css", "page.js"]},
    }
    embedded = json.dumps(sources, ensure_ascii=False).replace('<', '\\u003c').replace('\u2028', '\\u2028').replace('\u2029', '\\u2029')
    page = ('<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
            '<meta name="viewport" content="width=device-width,initial-scale=1">'
            '<title>ULA under LSI — proof and reference comparison</title>'
            '<meta name="description" content="A detailed entropy proof for ULA under LSI, '
            'paired with exact Lean source and an explicit audit against Vempala–Wibisono (2019).">'
            '<style>' + SHARED.katex_css() + '\n' + (HERE / 'page.css').read_text() + '</style></head>'
            '<body data-mode="paired"><header class="running-head"><a href="../../../index.html">'
            'LangevinLean</a><div class="controls"><label for="reading-mode">Read </label>'
            '<select id="reading-mode"><option value="paired">Mathematics + Lean</option>'
            '<option value="math">Mathematics only</option></select>'
            '<button type="button" id="toggle-proofs" aria-expanded="true">Fold Lean proofs</button>'
            '<button type="button" id="print-document">Print</button></div></header><main>'
            '<header class="hero"><div class="eyebrow">Sampling algorithms · Entropy analysis</div>'
            '<h1>ULA under the log-Sobolev inequality</h1>'
            '<p class="subtitle">The entropy argument, its Lean proof, and the comparison with the reference paper.</p>'
            '<div class="status-note"><strong>Conditional Lean formalization.</strong> The displayed bound '
            'matches the paper. The current Lean endpoints require additional analytic interpolation '
            'hypotheses. The page identifies exactly which steps are proved and which remain open.</div>' +
            math(content["intro"]) +
            '<p class="hero-actions"><a href="#reference-audit">Reference comparison</a> · '
            '<a href="#sources">Complete sources</a> · <a href="../README.md">Module guide</a> · '
            '<a href="../../exposition/dist/index.html">Strongly convex ULA proof</a></p>'
            '<nav class="toc" aria-label="Contents"><h2>Contents</h2><ol>' + ''.join(toc) +
            '<li><a href="#reference-audit">What matches the paper</a></li>'
            '<li><a href="#sources">Complete sources</a></li></ol></nav></header>' +
            ''.join(chapters) + audit_section(audit, math) +
            '<div class="closing">' + math(content["closing"]) + '</div>' + appendix +
            '</main><div id="action-status" role="status" aria-live="polite"></div>'
            '<script type="application/json" id="lean-sources">' + embedded + '</script>'
            '<script type="application/json" id="source-manifest">' + json.dumps(manifest) + '</script>'
            '<script>' + (HERE / 'page.js').read_text() + '</script></body></html>\n')
    OUT.write_text(page)
    (HERE / "source_manifest.json").write_text(json.dumps(manifest, indent=2) + '\n')
    print(f"Built {OUT.relative_to(ROOT)}: {manifest['sections']} chapters, "
          f"{manifest['steps']} proof steps, {len(represented)} explained declarations, "
          f"{len(sources)} embedded files, {len(page.encode()):,} bytes")


if __name__ == "__main__":
    build()
