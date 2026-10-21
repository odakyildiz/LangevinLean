"""Build the standalone tutorial from exact Lean source ranges and annotations.

Run from any directory. Every listing is copied from a checked-in Lean file;
the generated .tex is standalone for the desktop LaTeX editor.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN_ROOT = HERE.parent

PREAMBLE = r"""\documentclass[11pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage{lmodern}
\usepackage[margin=23mm]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{microtype}
\usepackage{booktabs,longtable,array}
\usepackage[obeyspaces,spaces]{url}
\usepackage{xcolor,listings,needspace}
\usepackage[colorlinks=true,linkcolor=blue,urlcolor=blue]{hyperref}
\usepackage{enumitem}
\setlist{itemsep=2pt,topsep=4pt}
\setlength{\parindent}{0pt}
\setlength{\parskip}{5pt plus 1pt}
\setlength{\emergencystretch}{3em}
\setcounter{tocdepth}{1}
\newcommand{\R}{\mathbb{R}}
\newcommand{\N}{\mathbb{N}}
\newcommand{\ip}[2]{\langle #1,#2\rangle}
\newcommand{\norm}[1]{\lVert #1\rVert}
\newcommand{\lean}[1]{\ifmmode\text{\nolinkurl{#1}}\else\nolinkurl{#1}\fi}
\newcommand{\grad}{\nabla f}
\newsavebox{\proofstepbox}
\newenvironment{proofstep}{%
 \begin{lrbox}{\proofstepbox}\begin{minipage}{\linewidth}%
}{%
 \end{minipage}\end{lrbox}%
 \par\Needspace{\dimexpr\ht\proofstepbox+\dp\proofstepbox+8pt\relax}%
 \noindent\usebox{\proofstepbox}\par\medskip%
}
\definecolor{codebg}{RGB}{247,249,252}
\definecolor{coderule}{RGB}{205,214,224}
\definecolor{codeblue}{RGB}{25,65,110}
\lstdefinelanguage{Lean}{
 morekeywords={theorem,lemma,def,variable,namespace,end,noncomputable,section,
 open,scoped,by,have,let,fun,show,exact,apply,intro,constructor,obtain,
 refine,change,calc,induction,with,zero,succ,omit,in,using},
 sensitive=true,morecomment=[l]{--},morecomment=[s]{/-}{-/}}
\lstdefinestyle{leanproof}{
 language=Lean,basicstyle=\ttfamily\fontsize{9}{11}\selectfont,
 keywordstyle=\color{codeblue}\bfseries,commentstyle=\color{gray},
 columns=fullflexible,keepspaces=true,showstringspaces=false,
 numbers=left,numberstyle=\ttfamily\scriptsize\color{gray},numbersep=8pt,
 xleftmargin=18pt,frame=single,framesep=5pt,rulecolor=\color{coderule},
 backgroundcolor=\color{codebg},breaklines=true,breakatwhitespace=false,
 postbreak=\mbox{\textcolor{gray}{\(\hookrightarrow\)}\space},
 aboveskip=6pt,belowskip=7pt,
 literate=
 {ℝ}{{\ensuremath{\mathbb{R}}}}1 {ℕ}{{\ensuremath{\mathbb{N}}}}1
 {α}{{\ensuremath{\alpha}}}1 {ρ}{{\ensuremath{\rho}}}1
 {‖}{{\ensuremath{\Vert}}}1 {•}{{\ensuremath{\bullet}}}1
 {·}{{\ensuremath{\cdot}}}1 {ᵃ}{{\ensuremath{{}^{a}}}}1
 {₀}{{\ensuremath{{}_{0}}}}1 {₁}{{\ensuremath{{}_{1}}}}1
 {←}{{\ensuremath{\leftarrow}}}1 {→}{{\ensuremath{\to}}}1
 {↦}{{\ensuremath{\mapsto}}}1 {∀}{{\ensuremath{\forall}}}1
 {∃}{{\ensuremath{\exists}}}1 {∈}{{\ensuremath{\in}}}1
 {∘}{{\ensuremath{\circ}}}1 {∧}{{\ensuremath{\wedge}}}1
 {≠}{{\ensuremath{\ne}}}1 {≤}{{\ensuremath{\le}}}1
 {≥}{{\ensuremath{\ge}}}1 {⊢}{{\ensuremath{\vdash}}}1
 {⟨}{{\ensuremath{\langle}}}1 {⟩}{{\ensuremath{\rangle}}}1
 {𝓝}{{\ensuremath{\mathcal{N}}}}1 {¬}{{\ensuremath{\neg}}}1
 {²}{{\ensuremath{{}^{2}}}}1 {Ł}{{\L}}1}
\hypersetup{pdftitle={Gradient descent: reading the Lean proof step by step},
 pdfauthor={A guide to the verified GradientDescent source}}
\title{Gradient descent\\Reading the Lean proof step by step}
\author{Code, mathematical derivations, and proof-state explanations}
\date{6 October 2026}
\begin{document}
\maketitle
This guide is intended to be read with the Lean editor open. Every numbered
code block reproduces an exact range of lines from the current source file.
Immediately below it, the mathematical calculation and the role of each tactic
explain what that block adds to the proof. Line numbers refer to the original
\lean{.lean} files, rather than the numbering of this document. A gray hooked
arrow marks a display-only line wrap.

The logical order is: supporting planes, strong convexity, an auxiliary
contraction and minimizer existence, smoothness, geometric sequences, the
actual gradient-descent proof, and the endpoint examples. The code uses
Mathlib's gradient and derives its required properties from the stated
function assumptions.
\tableofcontents
\clearpage
"""

def code_block(file, start, end):
    lines = (LEAN_ROOT / file).read_text().splitlines()
    assert 1 <= start <= end <= len(lines), (file, start, end)
    code = "\n".join(lines[start - 1:end])
    return (rf"\textit{{Source: \lean{{{file}}}, lines {start}--{end}.}}" + "\n"
            + rf"\begin{{lstlisting}}[style=leanproof,firstnumber={start}]" + "\n"
            + code + "\n" + r"\end{lstlisting}" + "\n")

def build():
    parts = [PREAMBLE, (HERE / 'introduction.texpart').read_text()]
    files = ['annotations_strong.json', 'annotations_smooth.json',
             'annotations_rates.json', 'annotations_endpoints.json']
    coverage = {}
    manifest = []
    order = ['StrongConvexity.lean', 'Step.lean', 'Minimizer.lean',
             'Smooth.lean', 'Rates.lean', 'Convergence.lean', 'Sharpness.lean']
    sections = []
    for name in files:
        sections.extend(json.loads((HERE / name).read_text())['sections'])
    sections.sort(key=lambda section: min(order.index(b['file']) for b in section['blocks']))
    previous_file = None
    for section in sections:
        first_file = min((b['file'] for b in section['blocks']), key=order.index)
        if first_file != previous_file:
            parts.append(r'\clearpage')
        previous_file = first_file
        for i, block in enumerate(section['blocks'], 1):
            file, start, end = block['file'], block['start'], block['end']
            parts.append(r'\begin{proofstep}')
            if i == 1:
                parts += ['\\section{' + section['title'] + '}',
                          section.get('intro', '')]
            parts += ['\\subsection*{Step ' + str(i) + ': ' + block['title'] + '}',
                      code_block(file, start, end),
                      r'\textbf{Mathematics and Lean.} ' + block['explanation'],
                      r'\end{proofstep}']
            coverage.setdefault(file, set()).update(range(start, end + 1))
            manifest.append({'file': file, 'start': start, 'end': end})
    parts += [(HERE / 'conclusion.texpart').read_text(), r'\end{document}']
    (HERE / 'GradientDescent.tex').write_text('\n\n'.join(parts) + '\n')
    hashes = {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
              for p in LEAN_ROOT.glob('*.lean')}
    (HERE / 'source_manifest.json').write_text(json.dumps(
        {'lean_sha256': hashes, 'blocks': manifest,
         'coverage': {k: sorted(v) for k, v in coverage.items()}}, indent=2) + '\n')
    print(f'Embedded {len(manifest)} exact source blocks from {len(coverage)} Lean files.')

if __name__ == '__main__':
    build()
