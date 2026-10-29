#!/usr/bin/env python3
"""Validate authored module notes and argument parts before they are merged.

Usage:
    python3 docs/validate_notes.py NOTES.json [--latex] [--keep DIR]

NOTES.json has the form
    {"modules": {"Lib/File.lean": {"title": ..., "summary": ..., "steps": [
        {"title": ..., "declarations": [...], "body": ..., "lean": ...}]}},
     "parts": {"<overview key>": [{"id": ..., "title": ..., "body": ..., "lean": ...,
        "references": [{"file": ..., "name": ...}]}]},
     "roadmap": {"<overview key>": [{"id": ..., "row": ..., "col": ..., "file": ...,
        "declaration": ..., "title": ..., "detail": ..., "parents": [...]}]}}
"modules" may also be the file's top-level mapping (the module_notes.json format).

Checks: declaration coverage (complete for the eight annotated libraries; a
subset of existing declarations for PBGSO and LatentDiffusion), pure
mathematical prose in titles, summaries and bodies, balanced HTML, existing
citation targets, KaTeX rendering of every formula and, with --latex, a XeLaTeX
compilation of the report text together with the exact Lean statement boxes.
Identifiers quoted in the Lean explanations that do not occur in the module
source are reported as warnings: check that each one is a real Lean or Mathlib
name.
"""
from __future__ import annotations

import argparse
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

if shutil.which('node') is None:
    bundled = Path.home() / '.cache/codex-runtimes/codex-primary-runtime/dependencies/node/bin'
    if (bundled / 'node').is_file():
        os.environ['PATH'] = str(bundled) + os.pathsep + os.environ.get('PATH', '')

from build_site import HELPERS, LIBRARIES, declarations, latex_prose, tex_escape  # noqa: E402
from full_proofs import mathematical_prose  # noqa: E402
from verify_exposition import reader_issues  # noqa: E402
import lean_latex  # noqa: E402

PARTIAL = ('PBGSO', 'LatentDiffusion')
VOID = {'br', 'hr', 'img', 'input', 'meta', 'link', 'wbr'}
ALLOWED_TAGS = {'p', 'ul', 'ol', 'li', 'strong', 'em', 'b', 'i', 'code', 'cite', 'br', 'div', 'span', 'sup', 'sub', 'a'}


class Balance(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack, self.problems = [], []

    def handle_starttag(self, tag, attrs):
        if tag not in ALLOWED_TAGS:
            self.problems.append(f'unsupported tag <{tag}>')
        if tag not in VOID:
            self.stack.append(tag)

    def handle_endtag(self, tag):
        if tag in VOID:
            return
        if not self.stack or self.stack[-1] != tag:
            self.problems.append(f'unbalanced </{tag}> (open: {self.stack[-3:]})')
            if tag in self.stack:
                while self.stack and self.stack.pop() != tag:
                    pass
        else:
            self.stack.pop()


def html_problems(value):
    protected = HELPERS.TEX.sub(' formula ', value)
    parser = Balance()
    parser.feed(protected)
    parser.close()
    problems = list(parser.problems)
    if parser.stack:
        problems.append(f'unclosed tags {parser.stack}')
    if re.search(r'(?<!\\)\$', protected):
        problems.append('dollar sign outside \\( \\) or \\[ \\] math')
    for formula in HELPERS.TEX.finditer(value):
        text = formula[0]
        if re.search(r'\\(?:label|ref|eqref)\b', text):
            problems.append('\\label/\\ref/\\eqref do not resolve across web and PDF: ' + text[:60])
        if re.search(r'\\(?:begin|end)\{(?:equation|align|eqnarray)\*?\}', text):
            problems.append('use aligned/gathered inside \\[ \\] instead of numbered environments: ' + text[:60])
        if '<' in text and '&lt;' not in text and re.search(r'<\w', text):
            problems.append('write < as &lt; inside formulas: ' + text[:60])
    return problems


def library_of(path):
    for library in sorted(LIBRARIES + list(PARTIAL), key=len, reverse=True):
        if path == library + '.lean' or path.startswith(library + '/'):
            return library
    raise ValueError('Unknown library for ' + path)


def parse(path, source):
    library = library_of(path)
    if library == 'PBGSO':
        from build_pbgso import pbgso_declarations
        return pbgso_declarations(source)
    if library == 'LatentDiffusion':
        from build_latent_diffusion import parse_declarations
        return parse_declarations(source)
    return declarations(source)


def load(path):
    data = json.loads(Path(path).read_text())
    if 'modules' not in data and all(key.endswith('.lean') for key in data):
        data = {'modules': data}
    return data


def identifiers_in(value):
    return [match for match in re.findall(r'<code>([^<]+)</code>', value)]


def check(data):
    errors, warnings = [], []
    sources, parsed = {}, {}

    def module(path):
        if path not in sources:
            target = ROOT / path
            if not target.is_file():
                raise ValueError('missing Lean file ' + path)
            sources[path] = target.read_text()
            parsed[path] = parse(path, sources[path]) if path != 'IPLA/Standalone.lean' else {}
        return sources[path], parsed[path]

    texts = []

    def prose(label, value, *, mathematical=True):
        if not isinstance(value, str) or not value.strip():
            errors.append(f'{label}: empty text')
            return
        texts.append(value)
        for problem in html_problems(value):
            errors.append(f'{label}: {problem}')
        if mathematical:
            for issue in reader_issues(value):
                errors.append(f'{label}: {issue}')
        for match in re.finditer(r'<cite\b([^>]*)>\s*</cite>', value):
            ref = re.search(r'data-report-ref="([^"]+)"', match[1])
            decl = re.search(r'data-report-declaration="([^"]+)"', match[1])
            if not ref:
                errors.append(f'{label}: citation without data-report-ref')
                continue
            try:
                _, target = module(ref[1])
            except ValueError as error:
                errors.append(f'{label}: {error}')
                continue
            if decl and decl[1] not in target:
                errors.append(f'{label}: cited declaration {decl[1]} is not in {ref[1]}')

    for path, note in data.get('modules', {}).items():
        try:
            source, declared = module(path)
        except ValueError as error:
            errors.append(str(error))
            continue
        library = library_of(path)
        prose(f'{path} title', note.get('title'))
        prose(f'{path} summary', note.get('summary'))
        names = []
        steps = note.get('steps')
        if not isinstance(steps, list) or (not steps and (declared or library in PARTIAL)):
            errors.append(f'{path}: no steps')
            continue
        for index, step in enumerate(steps, 1):
            label = f'{path} step {index}'
            prose(label + ' title', step.get('title'))
            prose(label + ' body', step.get('body'))
            step_names = step.get('declarations', [])
            names += step_names
            unknown = [name for name in step_names if name not in declared]
            if unknown:
                errors.append(f'{label}: unknown declarations {unknown}')
            if step_names or library in PARTIAL:
                if 'formal-note' in step.get('body', ''):
                    warnings.append(f'{label}: body still contains a formal-note; move it into "lean"')
                prose(label + ' lean', step.get('lean'), mathematical=False)
                code_lines = '\n'.join(source.splitlines())
                for token in identifiers_in(step.get('lean', '')):
                    bare = token.strip()
                    if re.fullmatch(r"[\w'.₀-₉ᵢ]+", bare) and bare not in code_lines:
                        warnings.append(f'{label}: identifier <code>{bare}</code> does not occur in {path}')
        if len(names) != len(set(names)):
            errors.append(f'{path}: repeated declarations')
        if library not in PARTIAL and path != 'IPLA/Standalone.lean' and set(names) != set(declared):
            errors.append(f'{path}: declaration coverage mismatch: missing {sorted(set(declared)-set(names))}, '
                          f'unknown {sorted(set(names)-set(declared))}')
    for key, parts in data.get('parts', {}).items():
        for index, part in enumerate(parts, 1):
            label = f'part {key} {index} ({part.get("id")})'
            prose(label + ' title', part.get('title'))
            prose(label + ' body', part.get('body'))
            if part.get('lean'):
                prose(label + ' lean', part['lean'], mathematical=False)
            for reference in part.get('references', []):
                try:
                    _, declared = module(reference['file'])
                except ValueError as error:
                    errors.append(f'{label}: {error}')
                    continue
                if reference['name'] not in declared:
                    errors.append(f'{label}: unknown reference {reference}')
    for key, nodes in data.get('roadmap', {}).items():
        identifiers = {node.get('id') for node in nodes}
        for node in nodes:
            label = f'roadmap {key} {node.get("id")}'
            try:
                _, declared = module(node['file'])
            except (KeyError, ValueError) as error:
                errors.append(f'{label}: {error}')
                continue
            if node.get('declaration') and node['declaration'] not in declared:
                errors.append(f'{label}: unknown declaration {node["declaration"]}')
            if any(parent not in identifiers for parent in node.get('parents', [])):
                errors.append(f'{label}: unknown parent')
            prose(label + ' title', node.get('title'))
            prose(label + ' detail', node.get('detail'))
    try:
        HELPERS.render_mathematics(texts)
    except ValueError as error:
        errors.append('KaTeX: ' + str(error))
    return errors, warnings, sources, parsed


def latex_document(data, sources, parsed):
    from full_proofs import _preamble
    from build_site import latex_heading
    parts = [_preamble('Validation document', latex_heading), r'\pagenumbering{arabic}' + '\n']

    def body(value):
        return latex_prose(mathematical_prose(re.sub(r'<cite\b[^>]*>\s*</cite>', 'Section 0', value)))

    def box(names, path, explanation):
        statements = [lean_latex.statement_block(path, name, sources[path], parsed[path][name])
                      for name in names if name in parsed.get(path, {})]
        return lean_latex.lean_box(lean_latex.declaration_title(names), statements,
                                   latex_prose(explanation) if explanation else '')

    for path, note in data.get('modules', {}).items():
        if path not in sources:
            continue
        parts.append(r'\section{' + latex_heading(note['title']) + '}\n' + body(note['summary']))
        for step in note['steps']:
            parts.append(r'\subsection{' + latex_heading(step['title']) + '}\n' + body(step['body']))
            if step.get('declarations') or step.get('lean'):
                parts.append(box(step.get('declarations', []), path, step.get('lean', '')))
    for key, items in data.get('parts', {}).items():
        parts.append(r'\chapter{Argument ' + tex_escape(key) + '}\n')
        for part in items:
            parts.append(r'\section{' + latex_heading(part['title']) + '}\n' + body(part['body']))
            references = part.get('references', [])
            if references or part.get('lean'):
                statements = [lean_latex.statement_block(r['file'], r['name'], sources[r['file']], parsed[r['file']][r['name']])
                              for r in references if r['file'] in sources]
                parts.append(lean_latex.lean_box('Lean formalization', statements,
                                                 latex_prose(part.get('lean', '')) if part.get('lean') else ''))
    parts.append(r'\end{document}' + '\n')
    return ''.join(parts)


def compile_latex(text, keep=None):
    engine = shutil.which('xelatex')
    if not engine:
        return ['xelatex not found; LaTeX compilation skipped']
    directory = Path(keep) if keep else Path(tempfile.mkdtemp(prefix='notes-latex-'))
    directory.mkdir(parents=True, exist_ok=True)
    (directory / 'proof.tex').write_text(text)
    result = subprocess.run([engine, '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
                             '-file-line-error', 'proof.tex'], cwd=directory, capture_output=True, text=True)
    log = (directory / 'proof.log').read_text(errors='replace') if (directory / 'proof.log').exists() else result.stdout
    problems = []
    if result.returncode:
        lines = log.splitlines()
        for i, line in enumerate(lines):
            if line.startswith('!') or re.match(r'^\./proof\.tex:\d+:', line):
                problems.append('\n'.join(lines[i:i + 8]))
                break
        match = re.search(r'proof\.tex:(\d+):', log)
        if match:
            source_lines = text.splitlines()
            n = int(match[1])
            problems.append('TeX source near the error:\n' + '\n'.join(source_lines[max(0, n - 4):n + 2]))
        if not problems:
            problems.append(log[-2000:])
    missing = sorted(set(re.findall(r'Missing character: There is no (.)', log)))
    if missing:
        problems.append('Missing glyphs: ' + ' '.join(missing))
    if not keep:
        shutil.rmtree(directory, ignore_errors=True)
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('notes', nargs='+')
    parser.add_argument('--latex', action='store_true', help='also compile the text with XeLaTeX')
    parser.add_argument('--keep', help='keep the LaTeX build in this directory')
    args = parser.parse_args()
    data = {'modules': {}, 'parts': {}, 'roadmap': {}}
    for path in args.notes:
        loaded = load(path)
        data['modules'].update(loaded.get('modules', {}))
        data['parts'].update(loaded.get('parts', {}))
        data['roadmap'].update(loaded.get('roadmap', {}))
    errors, warnings, sources, parsed = check(data)
    if args.latex and not errors:
        errors += ['LaTeX: ' + problem for problem in compile_latex(latex_document(data, sources, parsed), args.keep)]
    for warning in warnings:
        print('warning:', warning)
    steps = sum(len(note.get('steps', [])) for note in data['modules'].values())
    if errors:
        print(f'{len(errors)} error(s):')
        for error in errors:
            print('error:', error)
        raise SystemExit(1)
    print(f'OK: {len(data["modules"])} modules, {steps} steps, '
          f'{sum(len(v) for v in data["parts"].values())} argument parts'
          + (', LaTeX compiled' if args.latex else ''))


if __name__ == '__main__':
    main()
