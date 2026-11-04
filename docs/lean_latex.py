"""Typeset exact Lean statements and Lean-correspondence boxes in the PDF reports.

The mathematical prose of a report stays ordinary mathematics. Each proof step
is followed by a clearly separated box containing the exact Lean statement(s)
of that step, read from the source at build time, and the authored account of
how the formal proof follows the mathematical argument.

DejaVu Sans Mono covers almost every character used in the Lean sources. The
few it lacks are set in STIX Two Math, so no glyph is silently dropped.
"""
from __future__ import annotations

import re

# Characters used by the Lean sources that DejaVu Sans Mono does not contain.
FALLBACK = set('ℓℱ≪⊔⋀⋂⋃⟪⟫⨅⨆⨍⬝𝓝𝕜∥')
SPECIAL = {'\\': r'\textbackslash{}', '{': r'\{', '}': r'\}', '$': r'\$', '&': r'\&',
           '#': r'\#', '^': r'\textasciicircum{}', '_': r'\_', '%': r'\%',
           '~': r'\textasciitilde{}'}
MAX_STATEMENT_LINES = 80

PREAMBLE = r"""\usepackage[most]{tcolorbox}
\usepackage{mathrsfs}
\providecommand{\lt}{<}
\providecommand{\gt}{>}
\setmonofont{DejaVuSansMono.ttf}[BoldFont=DejaVuSansMono-Bold.ttf,ItalicFont=DejaVuSansMono-Oblique.ttf,BoldItalicFont=DejaVuSansMono-BoldOblique.ttf,Scale=0.86]
\newfontfamily\leanfallback{STIXTwoMath-Regular.otf}[Scale=0.86]
\definecolor{leanrule}{gray}{0.62}
\definecolor{leanback}{gray}{0.962}
\definecolor{leantitle}{gray}{0.22}
\definecolor{leanmuted}{gray}{0.38}
\newtcolorbox{leanbox}[1]{enhanced,breakable,colback=leanback,colframe=leanrule,
  boxrule=0.4pt,arc=0.6mm,left=2.4mm,right=2.4mm,top=1.8mm,bottom=1.8mm,
  before skip=0.8em,after skip=1em,fonttitle=\small\bfseries,coltitle=leantitle,
  colbacktitle=leanback,titlerule=0.3pt,title={#1}}
\newlength{\leancharwidth}
\newenvironment{leancode}{\par\smallskip\begingroup\ttfamily\footnotesize\raggedright
  \settowidth{\leancharwidth}{M}\setlength{\parskip}{0pt}\setlength{\parindent}{0pt}
  \frenchspacing}{\par\endgroup\smallskip}
\newcommand{\leanline}[2]{\hangindent=\dimexpr#1\leancharwidth+4\leancharwidth\relax
  \hangafter=1\noindent\hspace*{#1\leancharwidth}#2\par}
\newcommand{\leansource}[1]{\par{\footnotesize\color{leanmuted}#1}\par}
\newcommand{\leanlabel}[1]{\par\smallskip\noindent{\small\bfseries #1}\par}
"""


def escape_code(text):
    """Escape one line of Lean for the leancode environment, preserving every space."""
    out = []
    for character in text:
        if character in SPECIAL:
            out.append(SPECIAL[character])
        elif character in FALLBACK:
            out.append(r'{\leanfallback ' + character + '}')
        elif character == ' ':
            out.append(r'\ ')
        elif character == '\t':
            out.append(r'\ \ ')
        else:
            out.append(character)
    return ''.join(out)


def code_block(lines, *, max_lines=None):
    """Exact Lean lines; only an explicitly requested definition-body cap applies."""
    if max_lines is not None and len(lines) > max_lines:
        omitted = len(lines) - max_lines
        lines = list(lines[:max_lines]) + [
            f'-- … {omitted} further lines of this declaration are in the source file.']
    rows = []
    for line in lines:
        stripped = line.lstrip(' ')
        indent = len(line) - len(stripped)
        rows.append(r'\leanline{' + str(indent) + '}{' + (escape_code(stripped) if stripped else r'\strut') + '}')
    return r'\begin{leancode}' + '\n' + '\n'.join(rows) + '\n' + r'\end{leancode}' + '\n'


def plain_identifier(name):
    """A declaration name in running text: escaped, breakable at dots and underscores."""
    out = []
    for character in name:
        out.append(SPECIAL.get(character, r'{\leanfallback ' + character + '}' if character in FALLBACK else character))
        if character in '._':
            out.append(r'\allowbreak{}')
    return r'\texttt{' + ''.join(out) + '}'



# This lexical scanner and delimiter walk use the PBGSO header parser's
# established algorithm. They have no site-generator imports, so ordinary
# atlas headers and PDF statements can use it without a circular dependency.
def mask_lean_literals(source):
    """Mask comments/literals without changing source offsets or line breaks.

    The legacy teaching parser is deliberately untouched. In particular, a
    string or comment containing ``:=`` must not end a theorem header.
    """
    out, index, block_depth, string, quoted_name = [], 0, 0, False, False
    while index < len(source):
        char, pair = source[index], source[index:index + 2]
        if block_depth:
            if pair == '/-':
                block_depth += 1; out.extend('  '); index += 2
            elif pair == '-/':
                block_depth -= 1; out.extend('  '); index += 2
            else:
                out.append('\n' if char == '\n' else ' '); index += 1
        elif string:
            if char == '\\' and index + 1 < len(source):
                out.append(' ')
                out.append('\n' if source[index + 1] == '\n' else ' ')
                index += 2
            else:
                out.append('\n' if char == '\n' else ' '); index += 1
                if char == '"':
                    string = False
        elif quoted_name:
            out.append('\n' if char == '\n' else ' '); index += 1
            if char == '»':
                quoted_name = False
        elif pair == '/-':
            block_depth = 1; out.extend('  '); index += 2
        elif pair == '--':
            end = source.find('\n', index)
            if end == -1:
                end = len(source)
            out.extend(' ' * (end - index)); index = end
        elif char == '"':
            string = True; out.append(' '); index += 1
        elif char == '«':
            quoted_name = True; out.append(' '); index += 1
        else:
            out.append(char); index += 1
    if block_depth or string or quoted_name:
        raise ValueError('Unterminated Lean comment or literal')
    return ''.join(out)


def declaration_header_marker(masked, declaration):
    'Locate the actual body delimiter, not a nested named argument.\n\n    ``marker_column`` is a zero-based offset in the ORIGINAL source line.\n    Counting only lines is insufficient when ``(I := I)`` and the actual proof\n    delimiter occur on the same line. A result type may also begin with one\n    or more top-level ``let \\(x\\) := ...;`` terms; their assignments belong to\n    the statement and are skipped. Equation-style declarations retain their\n    preceding header line as the fallback boundary.\n    '
    opening = {'(': ')', '[': ']', '{': '}', '⟨': '⟩', '⦃': '⦄'}
    closing = set(opening.values())
    stack, pending_lets, equation = [], 0, None
    for number in range(declaration['start'], declaration['end'] + 1):
        line, column = masked[number - 1], 0
        while column < len(line):
            char = line[column]
            if char in opening:
                stack.append(opening[char]); column += 1
            elif char in closing:
                if stack and stack[-1] == char:
                    stack.pop()
                column += 1
            elif line[column:column + 2] == ':=':
                if not stack:
                    if pending_lets:
                        pending_lets -= 1
                    else:
                        return number, column, ':='
                column += 2
            elif char.isalpha() or char == '_':
                word = re.match(r"[\w']+", line[column:])[0]
                if not stack:
                    if word in ('let', 'letI'):
                        pending_lets += 1
                    elif word == 'where' and not pending_lets:
                        return number, column, 'where'
                column += len(word)
            else:
                if char == '|' and not stack and equation is None:
                    previous = number - 1
                    equation = (previous, len(masked[previous - 1]), '')
                column += 1
    if equation is not None:
        return equation
    raise ValueError(f"Cannot locate Lean body of {declaration['name']} at {declaration['start']}")


def refine_declaration_headers(source, parsed):
    """Locate actual body delimiters in the original source for every declaration.

    Named arguments and result-type let bindings contain assignments that are
    part of the statement. A leading absolute-value bar also does not start an
    equation-style body when a later real body delimiter exists.
    """
    masked = mask_lean_literals(source).splitlines()
    for declaration in parsed.values():
        line, column, token = declaration_header_marker(masked, declaration)
        declaration.update(marker=line, marker_column=column, marker_token=token)
        suffix = masked[line - 1][column + len(token):].strip()
        declaration['body_start'] = line + 1 if suffix in ('', 'by') else line
    return parsed


def header_lines(source, declaration):
    """Exact statement rows, excluding the actual body delimiter and proof."""
    rows = source.splitlines()[declaration['start'] - 1:declaration['marker']]
    column = declaration.get('marker_column')
    rows[-1] = (rows[-1][:column] if column is not None else rows[-1].split(':=', 1)[0]).rstrip()
    return rows

def statement_lines(source, declaration, *, full=False):
    """The exact source rows of a declaration statement (definitions in full)."""
    rows = source.splitlines()
    if full or declaration['kind'] in ('def', 'abbrev', 'structure', 'inductive', 'class', 'instance'):
        return rows[declaration['start'] - 1:declaration['end']]
    return header_lines(source, declaration)


def statement_block(path, name, source, declaration):
    """File location, exact statement and its source range."""
    lines = statement_lines(source, declaration)
    body_kind = declaration['kind'] in ('def', 'abbrev', 'structure', 'inductive', 'class', 'instance')
    location = (path + ', lines ' + str(declaration['start']) + '–' + str(declaration['end']))
    return (r'\leansource{' + plain_identifier(name) + r' \quad ' + escape_location(location) + '}\n'
            + code_block(lines, max_lines=MAX_STATEMENT_LINES if body_kind else None))


def escape_location(text):
    return ''.join(SPECIAL.get(c, c) for c in text).replace('/', r'/\allowbreak{}')


def lean_box(title, statements, explanation=''):
    """A breakable box: exact Lean statements, then how the proof follows the mathematics."""
    parts = [r'\begin{leanbox}{' + title + '}' + '\n']
    parts += statements
    if explanation.strip():
        parts.append(r'\leanlabel{How the Lean proof follows the argument}' + '\n' + explanation.strip() + '\n')
    parts.append(r'\end{leanbox}' + '\n')
    return ''.join(parts)


def step_box(references, explanation, sources, parsed, prose):
    """The Lean box of one proof step or argument part.

    ``references`` lists (path, declaration) pairs; ``prose`` converts the
    authored HTML explanation to LaTeX. Declarations absent from the parsed
    source raise an error instead of silently disappearing from the report.
    """
    statements = []
    for path, name in references:
        if name not in parsed.get(path, {}):
            raise ValueError(f'Unknown Lean declaration in report box: {path}: {name}')
        statements.append(statement_block(path, name, sources[path], parsed[path][name]))
    if not statements and not (explanation or '').strip():
        return ''
    return lean_box(declaration_title([name for _, name in references]), statements,
                    prose(explanation) if (explanation or '').strip() else '')


def declaration_title(names):
    if not names:
        return 'Lean formalization'
    shown = ', '.join(plain_identifier(name) for name in names[:3])
    more = '' if len(names) <= 3 else ' and ' + str(len(names) - 3) + ' more'
    return 'Lean: ' + shown + more


def strip_lean_markers(value):
    """Plain-text check helper: remove the escaped identifiers of a box."""
    return re.sub(r'\\texttt\{[^}]*\}', '', value)
