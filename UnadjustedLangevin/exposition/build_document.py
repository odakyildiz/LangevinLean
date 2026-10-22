#!/usr/bin/env python3
"""Build one offline proof document. Requires Python 3 and Node.js, no packages."""
from __future__ import annotations
import base64
import hashlib
import html
import json
import re
import subprocess
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OUT = HERE / "dist" / "index.html"
VENDOR = HERE / "vendor" / "katex"
TEMPLATES = HERE / "templates"
ENTRY_POINTS = {
    "main_theorem.html": "dist/index.html#main-theorem",
    "beginner_guide.html": "dist/index.html#lean-beginner-guide",
}
NOTES = ["notes_analytic.json", "notes_probability.json", "notes_assembly.json"]
ORDER = ["UnadjustedLangevin/StrongConvexity.lean",
         "UnadjustedLangevin/Analysis/Smooth.lean", "UnadjustedLangevin/GradientStep.lean",
         "UnadjustedLangevin/ULAupdate.lean", "UnadjustedLangevin/SharpContraction.lean",
         "UnadjustedLangevin/Dynamics.lean", "UnadjustedLangevin/Coupling.lean",
         "UnadjustedLangevin/Integrability.lean", "UnadjustedLangevin/LocalError.lean",
         "UnadjustedLangevin/GaussianMoments.lean", "UnadjustedLangevin/LpDrift.lean",
         "UnadjustedLangevin/Recurrence.lean", "UnadjustedLangevin/Convergence.lean",
         "UnadjustedLangevin/HilbertDalalyan.lean", "UnadjustedLangevin/InitialCoupling.lean",
         "UnadjustedLangevin/L2Convergence.lean"]
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|private|protected)\s+)*(theorem|lemma|def|abbrev|structure)\s+([\w'.]+)")
TEX = re.compile(r"\\\[(.*?)\\\]|\\\((.*?)\\\)", re.S)
TOKEN = re.compile(r'(--.*$|"(?:[^"\\]|\\.)*"|\b(?:theorem|lemma|def|abbrev|structure|where|by|have|let|fun|variable|namespace|end|noncomputable|section|import|open|scoped|with|induction|calc|match|if|then|else|in|show|of|at|using|exact|apply|refine|simp|simp_all|simp_rw|simpa|rw|rwa|ring|ring_nf|linarith|nlinarith|positivity|norm_num|module|abel|fun_prop|unfold|dsimp|change|obtain|filter_upwards|constructor|intro|rcases|field_simp|convert|rfl)\b|ℝ≥0∞|ℝ≥0|ℝ|ℕ|Type\*)')
TACTICS = set("exact apply refine simp simp_all simp_rw simpa rw rwa ring ring_nf linarith nlinarith positivity norm_num module abel fun_prop unfold dsimp change obtain filter_upwards constructor intro rcases field_simp convert rfl".split())


def slug(value):
    return re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")


def mask_comments(lines):
    depth, masked = 0, []
    for line in lines:
        result, i = [], 0
        while i < len(line):
            if line[i:i+2] == "/-":
                depth += 1; result.append("  "); i += 2
            elif depth and line[i:i+2] == "-/":
                depth -= 1; result.append("  "); i += 2
            elif depth:
                result.append(" "); i += 1
            elif line[i:i+2] == "--":
                break
            else:
                result.append(line[i]); i += 1
        masked.append("".join(result))
    return masked


def declarations(lines):
    code = mask_comments(lines)
    starts = [(i+1, m[1], m[2]) for i, line in enumerate(code) if (m := DECL.match(line))]
    result = {}
    for index, (start, kind, name) in enumerate(starts):
        end = starts[index+1][0]-1 if index+1 < len(starts) else len(lines)
        for j in range(start, end):
            if lines[j].startswith(("/--", "/-!", "end ", "omit ", "variable ", "open ", "set_option ")):
                end = j; break
        while end > start and not lines[end-1].strip():
            end -= 1
        marker = body = None
        for n in range(start, end+1):
            line = code[n-1]
            if ":=" in line or re.search(r"\bwhere\s*$", line):
                marker = n
                suffix = line.split(":=", 1)[-1].strip() if ":=" in line else ""
                body = n+1 if suffix in ("", "by") else n
                break
            if line.lstrip().startswith("|"):
                marker, body = n-1, n; break
        if marker is None:
            raise ValueError(f"Cannot locate body of {name} at {start}")
        result[name] = dict(name=name, kind=kind, start=start, end=end, marker=marker, body_start=body)
    return result


def load_document():
    sections = [section for name in NOTES for section in json.loads((HERE/name).read_text())["sections"]]
    sections.sort(key=lambda s: ORDER.index(s["file"]))
    sources = {s["file"]: (ROOT/s["file"]).read_text() for s in sections}
    parsed = {p: declarations(source.splitlines()) for p, source in sources.items()}
    seen = set()
    for section in sections:
        path = section["file"]
        code = mask_comments(sources[path].splitlines())
        if not section.get("setup_note", "").strip():
            raise ValueError(f"Missing beginner explanation of module context: {path}")
        for item in section["declarations"]:
            key = (path, item["name"])
            if key in seen:
                raise ValueError(f"Repeated declaration: {key}")
            seen.add(key)
            if not item.get("statement_note", "").strip():
                raise ValueError(f"Missing beginner explanation of formal statement: {key}")
            decl = parsed[path][item["name"]]
            item["source"] = decl
            covered, previous = set(), decl["start"]-1
            for step in item["steps"]:
                a, b = step["start"], step["end"]
                if not step.get("note", "").strip():
                    raise ValueError(f"Missing beginner explanation of source lines: {key} {a}:{b}")
                for n in range(a,b+1):
                    if code[n-1].strip() and f"Line {n}." not in step["note"]:
                        raise ValueError(f"Missing individual line explanation: {key}, line {n}")
                if not decl["start"] <= a <= b <= decl["end"] or a <= previous:
                    raise ValueError(f"Invalid step {key} {a}:{b}; declaration {decl['start']}:{decl['end']}")
                previous = b
                covered.update(range(a,b+1))
            expected = {n for n in range(decl["body_start"],decl["end"]+1) if code[n-1].strip()}
            if missing := expected-covered:
                raise ValueError(f"Unexplained proof lines {key}: {sorted(missing)}")
            if extra := {n for n in covered if code[n-1].strip()}-expected:
                raise ValueError(f"Statement lines inside proof steps {key}: {sorted(extra)}")
            if not item["statement"] or not item["steps"]:
                raise ValueError(f"Missing mathematical statement or proof: {key}")
    if missing := {(p,n) for p,ds in parsed.items() for n in ds}-seen:
        raise ValueError(f"Declarations missing: {sorted(missing)}")
    if set(sources) != set(ORDER):
        raise ValueError("Missing or unexpected proof modules")
    for p in ["UnadjustedLangevin/CanonicalULA.lean", "UnadjustedLangevin.lean",
              "UnadjustedLangevin/Check.lean", "lakefile.toml", "lean-toolchain", "lake-manifest.json"]:
        sources[p] = (ROOT/p).read_text()
    # The annotated chapters cover the original analytic coupling proof.
    # Include every local import needed by the updated library and its audit
    # in the complete-source appendix as well, including the new foundations.
    visited = set()
    def include_local_imports(path):
        if path in visited:
            return
        visited.add(path)
        source = sources[path]
        for name in re.findall(r'^import ([\w.]+)\s*$', source, re.M):
            dependency = name.replace('.', '/') + '.lean'
            if not (ROOT/dependency).is_file():
                continue
            if dependency not in sources:
                sources[dependency] = (ROOT/dependency).read_text()
            include_local_imports(dependency)
    for path in list(sources):
        if path.endswith('.lean'):
            include_local_imports(path)
    return sections, sources


def render_mathematics(texts):
    formulas = sorted({(m[1] is not None, html.unescape(m[1] or m[2])) for text in texts for m in TEX.finditer(text)})
    js = "const fs=require('fs'),k=require(process.argv[1]);process.stdout.write(JSON.stringify(JSON.parse(fs.readFileSync(0,'utf8')).map(([displayMode,t])=>{try{return k.renderToString(t,{displayMode,throwOnError:true,strict:'ignore',output:'htmlAndMathml',trust:false})}catch(e){console.error(JSON.stringify(t)+'\\n'+e.message);process.exit(1)}})));"
    result = subprocess.run(["node","-e",js,str(VENDOR/"katex.min.js")], input=json.dumps(formulas), text=True, capture_output=True)
    if result.returncode:
        raise ValueError("Mathematics rendering failed:\n"+result.stderr)
    rendered = dict(zip(formulas,json.loads(result.stdout)))
    return lambda text: TEX.sub(lambda m: rendered[(m[1] is not None,html.unescape(m[1] or m[2]))],text)


def katex_css():
    def embed(m):
        data = base64.b64encode((VENDOR/m[1]).read_bytes()).decode()
        return 'src:url(data:font/woff2;base64,'+data+') format("woff2")'
    return re.sub(r'src:url\((fonts/[^)]+\.woff2)\)[^}]+',embed,(VENDOR/"katex.min.css").read_text())


def highlight(line):
    result, previous = [], 0
    for m in TOKEN.finditer(line):
        result.append(html.escape(line[previous:m.start()]))
        word = m.group()
        kind = "comment" if word.startswith("--") else "string" if word.startswith('"') else "tactic" if word in TACTICS else "type" if word.startswith(("ℝ","ℕ","Type")) else "keyword"
        result.append(f'<span class="tok-{kind}">{html.escape(word)}</span>')
        previous = m.end()
    return "".join(result)+html.escape(line[previous:])


def code_block(path,start,end,sources,identifier="",role="excerpt"):
    lines = sources[path].splitlines()
    attr = f' id="{identifier}"' if identifier else ""
    output = [f'<span class="lean-line"><span class="line-number" aria-hidden="true">{n}</span><span class="line-text">{highlight(lines[n-1])}</span></span>' for n in range(start,end+1)]
    actions = ('<div class="code-label"><button class="copy-code" type="button" '
               'data-copy-next>Copy Lean</button></div>') if role == "excerpt" else ""
    return actions + f'<pre class="lean-code"{attr} data-source="{path}" data-start="{start}" data-end="{end}" data-role="{role}" aria-label="Lean source, lines {start} to {end}"><code>'+"".join(output)+'</code></pre>'


# Editor abbreviations verified against the installed Lean 4 extension.
SYMBOL_INPUT = [
    ("→ᵃ[", "\\r, Tab; \\^a, Tab; then [", "Affine-map arrow; the scalar type follows inside brackets."),
    ("ℝ≥0∞", "\\ennreal, Tab", "Extended nonnegative real numbers, including infinity."),
    ("ℝ≥0", "\\nnreal, Tab", "Nonnegative real numbers."),
    ("ℝ", "\\R, Tab", "Real numbers. The R is uppercase."),
    ("ℕ", "\\N, Tab", "Natural numbers. The N is uppercase."),
    ("→", "\\r, Tab", "Function arrow, or implication between propositions. ASCII -> also works for the ordinary arrow."),
    ("↦", "\\mapsto, Tab", "The function-defining arrow after fun. ASCII => also works."),
    ("∘", "\\circ, Tab", "Function composition."),
    ("•", "\\smul, Tab", "Scalar multiplication of a vector."),
    ("∀ᵐ", "\\forall, Tab; \\^m, Tab", "Almost every outcome, with respect to the stated measure."),
    ("∀ᶠ", "\\forall, Tab; \\^f, Tab", "Eventually with respect to a filter, for example all sufficiently large indices."),
    ("=ᵐ", "= then \\^m, Tab", "Equality almost everywhere."),
    ("∀", "\\forall, Tab", "For every possible value of the following variable."),
    ("∃", "\\exists, Tab", "There exists a value satisfying the following condition."),
    ("≤", "\\le, Tab", "Less than or equal to."),
    ("≥", "\\ge, Tab", "Greater than or equal to."),
    ("≠", "\\ne, Tab", "Not equal to."),
    ("∈", "\\in, Tab", "Membership in a set."),
    ("∧", "\\and, Tab", "Both propositions hold."),
    ("←", "\\l, Tab", "Reversed direction when used before a rewrite rule."),
    ("⊢", "\\vdash, Tab", "The current target, including at the end of a tactic's location list."),
    ("⟨", "\\langle, Tab", "Opening constructor bracket for a package of witnesses or proofs."),
    ("⟩", "\\rangle, Tab", "Closing constructor bracket."),
    ("‖", "\\||, Tab", "A norm delimiter. Enter one on each side of the expression."),
    ("∫", "\\integral, Tab", "Integral. Beware: \\int produces ℤ, the integer type."),
    ("∞", "\\infty, Tab", "Infinity."),
    ("⨅", "\\infi, Tab", "Indexed infimum."),
    ("𝓝", "\\nhds, Tab", "The neighborhood filter used to state a limit."),
    ("⊤", "\\top, Tab", "The greatest element. In ℝ≥0∞ this is infinity."),
    ("∑", "\\sum, Tab", "A finite sum over the displayed index set."),
    ("∂", "\\partial, Tab", "Introduces the integration measure in the integral expressions used here."),
    ("×", "\\times, Tab", "Product type: an ordered pair with a component of each type."),
    ("μ", "\\mu, Tab", "A Greek letter used here as an ordinary variable name, commonly for a measure."),
    ("ν", "\\nu, Tab", "A Greek letter used as an ordinary variable name, commonly for a measure."),
    ("π", "\\pi, Tab", "An ordinary variable name for the target measure in these proofs, not the circle constant here."),
    ("Ω", "\\Omega, Tab", "An ordinary type-variable name for the outcome space; uppercase Omega."),
    ("ω", "\\omega, Tab", "An ordinary variable name for an outcome; lowercase omega."),
    ("γ", "\\gamma, Tab", "An ordinary variable name, often for a joint measure here."),
    ("ε", "\\epsilon, Tab", "An ordinary variable name, often an accuracy parameter."),
    ("₀", "\\_0, Tab", "A subscript character in an identifier, not a separate indexing operation."),
    ("₁", "\\_1, Tab", "A subscript character in an identifier."),
    ("₂", "\\_2, Tab", "A subscript character in an identifier."),
    ("·", "\\., Tab", "Proof bullet that focuses a subgoal."),
]


def symbol_help(source):
    entries = [(symbol, keys, meaning) for symbol, keys, meaning in SYMBOL_INPUT if symbol in source]
    if not entries:
        return ""
    rows = ''.join(f'<tr><td><code>{html.escape(symbol)}</code></td><td><code>{html.escape(keys)}</code></td><td>{html.escape(meaning)}</td></tr>' for symbol,keys,meaning in entries)
    return '<details class="symbol-help"><summary>How to type the symbols in these lines</summary><p>These are Lean editor input sequences, not text to paste literally into the proof. Type the backslash abbreviation, then press Tab to accept the Unicode character.</p><table class="typing-table"><thead><tr><th>Symbol</th><th>Keystrokes</th><th>Meaning</th></tr></thead><tbody>'+rows+'</tbody></table><p>For the decorated affine-map arrow and ASCII alternatives, see the <a href="#lean-unicode">full typing guide</a>.</p></details>'


def lean_note(content, source, math, summary, kind="proof", start=None, end=None):
    attrs = f' data-note-kind="{kind}"'
    if start is not None:
        attrs += f' data-note-start="{start}" data-note-end="{end}"'
    concepts = [("have", "lean-have", "have"), ("let", "lean-let", "let"),
                (":=", "lean-assignment", ":="), ("simpa", "lean-simpa", "simpa"),
                ("simp", "lean-simp", "simp lists"), ("→ᵃ", "lean-affine-map", "affine maps"),
                ("rw", "lean-rewrite", "rewriting")]
    links = [f'<a href="#{anchor}">{html.escape(label)}</a>' for token,anchor,label in concepts if token in source]
    links.extend(['<a href="#lean-types">types and proofs</a>', '<a href="#lean-application">function application</a>'])
    basics = '<p class="note-navigation">Basic syntax: '+" · ".join(links)+'.</p>'
    return f'<details class="lean-note"{attrs}><summary>{summary}</summary><div class="note-body">'+math(content)+basics+symbol_help(source)+'</div></details>'


def write_entry_points():
    """Keep old fragment URLs usable without exposing unrendered templates."""
    for name,target in ENTRY_POINTS.items():
        url = html.escape(target,quote=True)
        page = ('<!doctype html>\n<html lang="en"><head><meta charset="utf-8">'
                '<meta name="viewport" content="width=device-width, initial-scale=1">'
                '<meta name="robots" content="noindex, nofollow, noarchive">'
                '<title>Open the Langevin proof document</title>'
                f'<meta http-equiv="refresh" content="0;url={url}">'
                '<style>body{max-width:42rem;margin:4rem auto;padding:0 1.25rem;font:18px/1.7 Georgia,serif}a{color:#38604c}</style>'
                '</head><body><p>The proof document is ready.</p>'
                f'<p><a href="{url}">Open the fully rendered Langevin proof document</a>.</p>'
                '</body></html>\n')
        (HERE/name).write_text(page)


INTRO = r"""
<p class="eyebrow">A mathematical proof with its formal counterpart</p>
<h1>The unadjusted<br><em>Langevin algorithm</em></h1>
<p class="subtitle">Dalalyan’s coupling argument, constructed in order.</p>
<p>The main theorem is stated first. The rest of this document constructs its proof from supporting lemmas, with the mathematical argument and exact Lean source together.</p>
"""
READING_NOTE = r"""
<p class="notation">In deterministic lemmas, \(\|\cdot\|\) is the ambient norm. For random vectors, \(\|Z\|_2=(\mathbb E\|Z\|^2)^{1/2}\). The formal potential is named <code>f</code> or <code>U</code>; a general drift is named <code>g</code>. Scalar multiplication is <code>•</code>, and <code>∀ᵐ</code> means “almost everywhere”. Constants typed <code>ℝ≥0</code> carry their nonnegativity.</p>
<p class="reading-note">Read straight down after the main theorem. Every proof step has its exact Lean lines alongside it. A complete declaration follows every proof, initially unfolded. All complete modules are included at the end. Open Lean notes for beginner explanations, or select a line-range label to link to that step.</p>
"""
CLOSING = r"""
<div class="closing"><h2>What the estimate establishes</h2>
<p>For the small-step regime, \(b/(1-q)=1.65(L/m)\sqrt{hd}\). For the large-step regime, \(b/(1-q)=1.65Lh\sqrt{hd}/(2-Lh)\). With fixed positive \(h\), the upper envelope tends to this bias bound; no convergence to the exact target law at fixed step is asserted.</p>
<p>The shared proof first bounds the error for one initial coupling. <code>ProductReference.lean</code> realizes each coupling on its own explicit product probability space, proves a common output law, and passes to the infimum. This gives the actual initial distance \(W_2(\operatorname{Law}(X_0),\pi)\).</p>
<p><a href="#module-unadjustedlangevin-canonicalula-lean"><code>CanonicalULA.lean</code></a> assembles the unconditional theorem. The supporting modules construct Gaussian innovations and the Brownian integral solution, normalize Gibbs measure, prove Gibbs stationarity and score moments, and identify the algorithm law. The reference records in the analytic chapter expose these proved intermediate facts; they are not extra assumptions of the canonical endpoint.</p>
<p>The exact rational coefficient is checked by the lemma \((7/6)\sqrt2\le33/20\).</p></div>
"""


def build():
    sections,sources = load_document()
    guide = (TEMPLATES/"beginner_guide.html.inc").read_text()
    main_statement = (TEMPLATES/"main_theorem.html.inc").read_text()
    texts = [INTRO,CLOSING,guide,main_statement,READING_NOTE]
    for s in sections:
        texts.extend([s["intro"],s.get("setup_note","")])
        for d in s["declarations"]:
            texts.extend([d["statement"],d.get("statement_note","")])
            for step in d["steps"]:
                texts.extend([step["prose"],step.get("note","")])
    math = render_mathematics(texts)
    path = "UnadjustedLangevin/CanonicalULA.lean"
    main_declarations = declarations(sources[path].splitlines())
    main_names = ["dalalyan", "dalalyan_large_step"]
    if missing := set(main_names)-set(main_declarations):
        raise ValueError(f"Missing canonical theorem statements: {sorted(missing)}")
    main_sources = []
    for name in main_names:
        d = main_declarations[name]
        target = "module-"+slug(path)
        main_sources.append(f'<p><code>ULA.Hilbert.{name}</code></p>'+code_block(path,d["start"],d["marker"],sources)+
                            f'<p><a href="#{target}">Continue to the complete checked source</a>.</p>')
    formal_main = '<details class="main-formal"><summary>Exact Lean statements of the canonical results</summary><p>The source headers are reproduced exactly. The shared proof is explained line by line below, and the complete canonical construction is included in the source appendix.</p>'+''.join(main_sources)+'</details>'
    main_overview = math(main_statement).replace('<!--FORMAL_MAIN_STATEMENTS-->',formal_main)
    toc,chapters,decl_count,step_count = [],[],0,0
    for number,s in enumerate(sections,1):
        path,sid = s["file"],"section-"+s["id"]
        toc.append(f'<li><a href="#{sid}">{html.escape(s["title"])}</a></li>')
        articles = []
        for item in s["declarations"]:
            decl_count += 1
            d = item["source"]
            did = "decl-"+slug(path.removesuffix(".lean"))+"-"+item["name"]
            mid,fid = "module-"+slug(path),did+"-full-code"
            label = "Definition" if d["kind"] in ("def","abbrev","structure") else "Theorem" if item["name"].startswith("dalalyan_") and "integral_reference" in item["name"] else "Lemma"
            first = item["steps"][0]["start"]
            se = max(d["start"],min(d["marker"],first-1)) if first>d["start"] else d["marker"]
            formal = code_block(path,d["start"],se,sources)
            statement_note = lean_note(item.get("statement_note",""),'\n'.join(sources[path].splitlines()[d["start"]-1:se]),math,"Lean note · read the statement", "statement",d["start"],se)
            rows = []
            for index,step in enumerate(item["steps"],1):
                step_count += 1
                a,b = step["start"],step["end"]
                rid = f'{did}-step-{index}'
                note = lean_note(step.get("note",""),'\n'.join(sources[path].splitlines()[a-1:b]),math,"Lean note · every line explained", "proof",a,b)
                rows.append(f'<div class="proof-pair" id="{rid}"><div class="math-text">{math(step["prose"])}</div><div class="pair-code"><div class="code-label"><a href="#{rid}" aria-label="Link to proof step {index}, lines {a} to {b}">Lean · {a}–{b}</a></div>'+code_block(path,a,b,sources)+'</div>'+note+'</div>')
            full = code_block(path,d["start"],d["end"],sources,fid,"full-proof")
            articles.append(f'<article class="declaration" id="{did}" data-file="{path}" data-name="{item["name"]}"><h3><span class="declaration-title">{label} {decl_count}.</span> {html.escape(item["title"])}<a class="permalink" href="#{did}" aria-label="Link to {html.escape(item["title"])}">§</a><span class="formal-name">{item["name"]}</span></h3><div class="proof-pair statement"><div class="math-text">{math(item["statement"])}</div><div class="pair-code"><div class="code-label">Formal statement · {d["start"]}–{se}</div>{formal}</div>{statement_note}</div><span class="proof-label">'+("Construction." if label=="Definition" else "Proof.")+"</span>"+"".join(rows)+f'<div class="proof-end" aria-label="End of proof">□</div><details class="full-proof" open><summary>Complete Lean '+("definition" if label=="Definition" else "proof")+f' · {item["name"]}</summary><div class="full-actions"><a class="source-link" href="#{mid}">{path} · {d["start"]}–{d["end"]}</a><button class="copy-code" data-code="{fid}" type="button">Copy Lean</button></div>{full}<p class="full-context">Exact declaration. Imports, namespaces, and ambient variables appear in the <a href="#{mid}">complete module</a>.</p></details></article>')
        setup_note = lean_note(s.get("setup_note",""),'',math,"Lean note · imports and surrounding context", "setup")
        chapters.append(f'<section class="chapter" id="{sid}" data-number="{number}" data-title="{html.escape(s["title"],quote=True)}"><h2><span class="chapter-number">§ {number}</span>{html.escape(s["title"])}</h2><div class="chapter-intro">{math(s["intro"])}</div><p class="source-caption">Source: <a href="#module-{slug(path)}">{path}</a></p>{setup_note}'+"".join(articles)+'</section>')
    modules = []
    for path,source in sources.items():
        mid = "module-"+slug(path)
        cid = mid+"-code"
        digest = hashlib.sha256(source.encode()).hexdigest()
        modules.append(f'<details id="{mid}" data-sha256="{digest}"><summary>{path}</summary><div class="module-actions"><button class="copy-code" type="button" data-code="{cid}">Copy file</button><button type="button" data-download="{path}">Save file</button></div>'+code_block(path,1,len(source.splitlines()),sources,cid,"module")+'</details>')
    appendix = '<section class="chapter appendix" id="complete-sources" data-number="A" data-title="Complete sources"><h2><span class="chapter-number">Appendix</span>Complete Lean sources</h2><p>These are the unabridged modules used above, followed by the library import, kernel audit, and pinned build configuration. Every file is embedded in this document.</p><p>From the repository root, run <code>lake build</code>, then <code>lake env lean UnadjustedLangevin/Check.lean</code>. The audit lists the logical axioms used by the final results.</p>'+"".join(modules)+'</section>'
    embedded = json.dumps(sources,ensure_ascii=False).replace("<","\\u003c").replace("\u2028","\\u2028").replace("\u2029","\\u2029")
    manifest = dict(format=2,declarations=decl_count,steps=step_count,sources={p:hashlib.sha256(v.encode()).hexdigest() for p,v in sources.items()})
    page = '<!doctype html>\n<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><meta name="robots" content="noindex, nofollow, noarchive"><title>The unadjusted Langevin algorithm — a proof with Lean</title><meta name="description" content="A sequential mathematical proof with exact Lean source beside every step."><style>'+katex_css()+'\n'+(HERE/"document.css").read_text()+'</style></head><body>'
    page += '<header class="running-head"><div class="running-title"><a href="../../../index.html">Project home</a> / <a href="../index.html">ULA overview</a> / <a href="#main-theorem">Main theorem</a> / <span id="current-section">A sequential proof</span></div><div class="controls"><label><span>Read</span><select id="reading-mode" aria-label="Reading mode"><option value="paired">Mathematics + Lean</option><option value="math">Mathematics only</option></select></label><button type="button" id="toggle-notes" aria-expanded="false">Open Lean notes</button><button type="button" id="toggle-full" aria-expanded="true">Fold full proofs</button><button type="button" id="print-document">Print</button></div><div class="progress" id="reading-progress" aria-hidden="true"></div></header>'
    page += '<main id="top"><header class="title-page">'+math(INTRO)+main_overview+math(READING_NOTE)+math(guide)+'<details class="contents" open><summary>Contents</summary><p><a href="#main-theorem">Main theorem and proof roadmap</a></p><ol>'+"".join(toc)+'<li><a href="#complete-sources">Complete sources</a></li></ol></details></header>'+"".join(chapters)+math(CLOSING)+appendix+'</main><div class="status" id="status" role="status" aria-live="polite"></div>'
    page += '<script type="application/json" id="lean-sources">'+embedded+'</script><script type="application/json" id="source-manifest">'+json.dumps(manifest,ensure_ascii=False)+'</script><script>'+(HERE/"document.js").read_text()+'</script></body></html>\n'
    OUT.parent.mkdir(parents=True,exist_ok=True)
    OUT.write_text(page)
    write_entry_points()
    print(f"Built {OUT}: {len(sections)} sections, {decl_count} declarations, {step_count} proof steps, {len(page.encode()):,} bytes")


if __name__ == "__main__":
    build()
