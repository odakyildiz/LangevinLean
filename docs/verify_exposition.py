#!/usr/bin/env python3
"""Check that paper-facing exposition contains mathematics, not source metadata.

The source/declaration/dependency checks remain in verify_site.py. This check
guards the separate reader-facing contract of the mathematical documents.
"""
from __future__ import annotations

from html.parser import HTMLParser
import re

from build_site import HELPERS, ROOT, load
from full_proofs import mathematical_prose
from site_content import CONFIG


# Explicit regression cases from source references once converted to spaced
# lowercase words. These are theorem names, not mathematical descriptions.
SPACED_SOURCE_NAMES = (
    'ula chain measurable', 'source euler noise normalized coordinate',
    'pre brownian comp measure preserving', 'brownian euler noise pullback',
    'gaussian innovations vector law', 'gaussian innovations vector independent',
    'initial extension initial', 'mala coupled step pointwise',
    'tilted measure interpolation relative density',
    'interpolation lebesgue density cont diff', 'bounded log weight tendsto',
    'interpolation law log sobolev', 'real gaussian kernel deriv',
    'interpolation relative score field weighted energy',
    'gradient log interpolation relative density', 'tendsto entropy quotient',
)


class Text(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []

    def handle_data(self, value):
        self.parts.append(value)


def reader_issues(value):
    """Inspect prose separately from formulas and their mathematical commands."""
    value = mathematical_prose(value)
    parser = Text()
    parser.feed(HELPERS.TEX.sub(' mathematical expression ', value))
    plain = ' '.join(parser.parts)
    issues = []
    if re.search(r'<code\b|<pre\b', value):
        issues.append('source identifier/code markup in mathematical prose')
    if re.search(r'\\operatorname\{Fin\}|\b(?:MemLp|ENNReal|NNReal|EuclideanSpace|WithLp|Fintype|Finset|'
                 r'IsProbabilityMeasure|HasGradientAt|HasFDerivAt|HasDerivAt|'
                 r'ContinuousOn|IntervalIntegrable|StrongConvexOn|LipschitzWith|'
                 r'toReal|ofReal|toNNReal)\b', value, re.I):
        issues.append('implementation notation in mathematical prose or formulas')
    formula_names = []
    for formula in HELPERS.TEX.finditer(value):
        if re.search(r'\\(?:texttt|mathtt)\b', formula[0]):
            issues.append('monospace source notation in a mathematical formula')
        for named in re.findall(r'\\(?:operatorname|mathrm|mathsf|mathtt|text)\{([^{}]+)\}', formula[0]):
            formula_names.extend(name for name in
                                 re.findall(r'\b[A-Za-z]*[a-z][A-Z][A-Za-z0-9]*\b|\b[A-Za-z][A-Za-z0-9]*_[A-Za-z0-9_]+\b', named)
                                 if len(name) > 3)
    if formula_names:
        issues.append('source-style names in formulas: ' + ', '.join(sorted(set(formula_names))[:6]))
    if re.search(r'\b(?:Lean|Mathlib|declarations?|namespace|typeclass|tactics?|wrappers?|implementations?|API)\b|[\w/]\.lean\b|\bformal development\b|\bsource (?:modules?|files?|code)\b', plain, re.I):
        issues.append('implementation commentary in mathematical prose')
    normalized = re.sub(r'\s+', ' ', plain).lower()
    spaced = [name for name in SPACED_SOURCE_NAMES if name in normalized]
    if spaced or re.search(r'\bwasserstein2(?:real)?\b', normalized):
        issues.append('verbalized source reference: ' + ', '.join(spaced[:3]))
    identifiers = re.findall(r'\b[A-Za-z][A-Za-z0-9]*_[A-Za-z0-9_]+\b|\b[A-Za-z]*[a-z][A-Z][A-Za-z0-9]*\b', plain)
    identifiers = [name for name in identifiers if name not in
                   ('arXiv', 'eV', 'mW', 'McKean', 'McShane', 'McDiarmid', 'LaTeX')]
    if identifiers:
        issues.append('source-style names: ' + ', '.join(sorted(set(identifiers))[:6]))
    return issues


def mathematical_tex(content):
    """A report without its Lean boxes, code blocks and front matter on the formalization.

    The Lean statements and the explanations of the formal proofs belong in the
    marked boxes; the mathematics outside them must not depend on source names.
    """
    content = re.sub(r'\\begin\{leanbox\}.*?\\end\{leanbox\}', '', content, flags=re.S)
    content = re.sub(r'\\begin\{leancode\}.*?\\end\{leancode\}', '', content, flags=re.S)
    content = re.sub(r'\\chapter\*\{About this document\}.*?(?=\\section\*\{Literature and scope\})', '',
                     content, flags=re.S)
    preamble_end = content.find(r'\begin{document}')
    return content[preamble_end:] if preamble_end >= 0 else content


def verify():
    _, _, notes = load()
    issues = []
    boxes = 0
    for path, note in notes.items():
        passages = [('title', note['title']), ('summary', note['summary'])]
        for index, step in enumerate(note['steps'], 1):
            boxes += 1
            if step['declarations'] and not step.get('lean', '').strip():
                issues.append(f'{path}, step {index}: missing Lean correspondence')
            passages.extend([(f'step {index} title', step['title']),
                             (f'step {index}', step['body'])])
        for label, value in passages:
            issues.extend(f'{path}, {label}: {issue}' for issue in reader_issues(value))
    for library, config in CONFIG.items():
        for result in config['results']:
            issues.extend(f'{library}, result {result["title"]}: {issue}'
                          for issue in reader_issues(result['body']))
        for part in config.get('proof', []):
            if not part.get('lean', '').strip():
                issues.append(f'{library}, argument {part["title"]}: missing Lean correspondence')
            issues.extend(f'{library}, argument {part["title"]}: {issue}'
                          for issue in reader_issues(part['body']))
    for path in (ROOT/'docs/latex').rglob('*.tex'):
        if re.search(r'\\texttt\{|Lean declarations:|Source module:|\bMathlib\b|\bLean\b',
                     mathematical_tex(path.read_text())):
            issues.append(f'{path.relative_to(ROOT)}: source metadata outside the marked Lean boxes')
    if issues:
        raise SystemExit('Mathematical exposition checks failed:\n' + '\n'.join(issues))
    print(f'Checked paper-facing exposition for {len(notes)} modules, {boxes} proof boxes, '
          f'{len(CONFIG)} theorem overviews, and all LaTeX exports: no source code, '
          'declaration names or implementation commentary outside the marked Lean boxes.')


if __name__ == '__main__':
    verify()
