#!/usr/bin/env python3
"""Generate a local, source-matched tutorial with no network dependencies."""
from __future__ import annotations

import hashlib
import html
import json
import re
import shutil
from pathlib import Path
from capture_goals import lesson_steps, step_ranges

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SITE = HERE / "site"
DECL = re.compile(r"^(?:theorem|lemma|def)\s+([\w']+)")
TOKEN = re.compile(r"(--.*$|/--.*$|\b(?:import|namespace|end|def|theorem|lemma|Prop|by|unfold|intro|have|change|apply|calc|rw|at|exact|using|simpa|only|fun|ring|norm_num|linarith|by_contra)\b|ℝ|∀|→|↦|:=|≤|<|\+|\*|=)")


def tex(value, display=True):
    tag = "div" if display else "span"
    return f'<{tag} class="math" data-tex="{html.escape(value, quote=True)}" data-display="{str(display).lower()}">{html.escape(value)}</{tag}>'


def prose(value):
    if isinstance(value, list):
        return ''.join('<p>' + prose(item) + '</p>' for item in value)
    value = str(value or "")
    value = re.sub(r"`([^`]+)`", lambda m: '<code>' + html.escape(m[1]) + '</code>', value)
    return re.sub(r"\\\[(.*?)\\\]|\\\((.*?)\\\)", lambda m: tex((m[1] or m[2]).strip(), m[1] is not None), value, flags=re.S)


def highlighted(value):
    result, previous = [], 0
    for match in TOKEN.finditer(value):
        result.append(html.escape(value[previous:match.start()]))
        word = match[0]
        kind = "comment" if word.startswith(("--", "/--")) else "symbol" if word in {"ℝ", "∀", "→", "↦", ":=", "≤", "<", "+", "*", "="} else "keyword"
        result.append(f'<span class="token-{kind}">{html.escape(word)}</span>')
        previous = match.end()
    result.append(html.escape(value[previous:]))
    return ''.join(result)


def declaration(lines, name):
    start = next(i for i, line in enumerate(lines) if (match := DECL.match(line)) and match[1] == name)
    end = next((i for i in range(start + 1, len(lines)) if lines[i].startswith(("/--", "theorem ", "lemma ", "def ", "end "))), len(lines))
    while end > start and not lines[end - 1].strip():
        end -= 1
    return start + 1, end


def source_card(path, lines, start, end, identifier="", full=False):
    rows = ''.join(f'<span class="code-line" data-line="{i}"'
        + (f' id="source-{Path(path).stem.lower()}-L{i}"' if full else '')
        + f'><span class="line-number" aria-hidden="true">{i}</span>{highlighted(lines[i - 1])}</span>'
        for i in range(start, end + 1))
    return (f'<div class="source-card" data-file="{path}" data-start="{start}" data-end="{end}">'
        f'<div class="source-heading"><span>{html.escape(path)}</span>'
        '<button class="copy-source" type="button">Copy</button></div>'
        f'<pre class="source-code" tabindex="0" aria-label="Lean source lines {start} to {end}"><code>{rows}</code></pre>'
        f'<div class="source-caption">Exact source · lines {start}–{end}'
        + (f'<a href="sources/{path}" download>Download this file</a>' if full else f'<a class="open-source" data-file="{path}" data-line="{start}" href="#source-{Path(path).stem.lower()}-L{start}">Open complete file ↗</a>')
        + '</div></div>')


DECLARATION_GUIDE = [
    ("ℝ", "The type of real numbers. A type describes what sort of object a name denotes; x : ℝ declares a real number x."),
    ("theorem", "Introduces a named mathematical statement together with its proof. A theorem name is an identifier chosen by its author."),
    ("def", "Introduces a definition. Here, a definition ending in Prop names a mathematical property rather than a numerical value."),
    ("(f : ℝ → ℝ)", "A parameter named f with type ℝ → ℝ: a function from real numbers to real numbers. The colon separates a name from its type."),
    ("(hf : IsConvex f)", "A parameter named hf whose type is the proposition that f is convex. Supplying hf supplies a proof of that proposition."),
    ("( … )", "Parentheses group an expression or enclose a named parameter with its type. In (x y : ℝ), both x and y have the type ℝ."),
    ("f x", "Function application uses spaces. Read f x as f(x). The application binds more tightly than arithmetic: a * f x means a · f(x)."),
    ("∀", "For every. A proof of ∀ x, P x can be used at any particular x; intro names an arbitrary x while proving it."),
    (",", "In ∀ x, P x, the comma ends the bound variables and begins the statement about them. In a rewrite list such as [hab, one_mul], it separates two entries."),
    ("→", "Between types, this is a function type. Between propositions, P → Q means that a proof of P can be used to construct a proof of Q."),
    (": Prop", "The defined expression is a proposition: a statement that may be proved. A proof is a term with that proposition as its type."),
    (":= by", "After the declaration's final colon comes its conclusion. := supplies its value or proof, and by starts a sequence of proof commands."),
    ("fun x ↦", "Defines a function by its output at x. For example, fun x ↦ s * x + c is the function x ↦ sx + c."),
    ("* and +", "Ordinary multiplication and addition of real numbers. Parentheses determine grouping. Equality =, inequality ≤, and strict inequality < are mathematical propositions."),
    ("⊢", "The goal marker in Lean's proof-state display. The proposition after it remains to be proved from the named facts and data above it."),
    ("import", "Makes definitions and proved facts from another Lean module available. Dots in the module name correspond to directories in its file path."),
    ("namespace", "Groups declaration names. Inside namespace ConvexityTutorial, a theorem called convex_midpoint has the full name ConvexityTutorial.convex_midpoint."),
    ("/-- … -/", "A documentation comment attached to the following declaration. It is explanatory text, not a proof command. -- begins a comment that ends with its line."),
]


def main():
    notes = json.loads((HERE / "lesson_notes.json").read_text())
    states_path = HERE / "proof_states.json"
    states = json.loads(states_path.read_text())
    ranges_hash = hashlib.sha256(json.dumps(step_ranges(lesson_steps(notes)), ensure_ascii=False, sort_keys=True).encode()).hexdigest()
    assert states["capture"]["stepRangesHash"] == ranges_hash, "Source mappings changed; recapture the Lean proof states before building."
    files = ["ConvexityTutorial.lean"] + ["ConvexityTutorial/" + name for name in
        ("Definitions.lean", "Basic.lean", "Minimizers.lean", "Subgradients.lean", "Check.lean")]
    sources = {path: (ROOT / path).read_text().splitlines() for path in files}
    SITE.mkdir(exist_ok=True)
    (SITE / "sources").mkdir(exist_ok=True)
    vendor = SITE / "assets/vendor/katex"
    donor = ROOT / "UnadjustedLangevin/exposition/dist/assets/vendor/katex"
    vendor.mkdir(parents=True, exist_ok=True)
    for name in ("katex.min.js", "katex.min.css", "LICENSE"):
        shutil.copyfile(donor / name, vendor / name)
    shutil.copytree(donor / "fonts", vendor / "fonts", dirs_exist_ok=True)
    hashes = {}
    for path in files:
        destination = SITE / "sources" / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / path, destination)
        hashes[path] = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
    for path, captured_hash in states["sourceHashes"].items():
        assert hashes[path] == captured_hash, f"Source changed; recapture proof states for {path}"
    lessons = []
    for item in notes["lessons"]:
        path = item["file"]
        if not path.startswith("ConvexityTutorial/"):
            path = "ConvexityTutorial/" + path
        start, end = declaration(sources[path], item["theorem"])
        steps = []
        for index, step in enumerate(item["steps"], 1):
            step = {**step, "number": index}
            assert start <= step["start"] <= step["end"] <= end, (item["id"], step)
            step["verifiedState"] = states.get("steps", {}).get(step["id"])
            assert step["verifiedState"] and step["verifiedState"]["verified"], f"Missing checked Lean state: {step['id']}"
            steps.append(step)
        lessons.append({**item, "file": path, "start": start, "end": end, "steps": steps})
    nav = ''.join(f'<a class="lesson-link" href="#lesson-{item["id"]}" data-lesson="{item["id"]}">'
        f'<span>{i:02}</span><span>{html.escape(item["title"])}'
        + ('<small class="optional-label">Optional</small>' if item.get("optional") else '')
        + '</span></a>' for i, item in enumerate(lessons, 1))
    sections = []
    for i, item in enumerate(lessons, 1):
        identifier = item["id"]
        explanation = ''.join(f'<section class="math-step" data-step="{step["id"]}" id="step-{step["id"]}">'
            f'<button class="step-choice" type="button" data-step="{step["id"]}" aria-pressed="false">'
            f'<span>{index}</span>{html.escape(step["title"])}</button>'
            + (tex(step["math"]) if step.get("math") else '')
            + '<div class="step-prose">' + prose(step.get("explanation", "")) + '</div></section>'
            for index, step in enumerate(item["steps"], 1))
        sections.append(f'<section class="lesson" id="lesson-{identifier}" data-lesson="{identifier}">'
            f'<header class="lesson-header"><p class="eyebrow">{"Optional proof" if item.get("optional") else "Proof"} {i:02} · {html.escape(item["file"])}</p>'
            f'<h2>{html.escape(item["title"])}</h2><div class="purpose">{prose(item.get("why", ""))}</div></header>'
            '<div class="theorem-statement"><span class="small-label">Mathematical statement</span>'
            + tex(item["statementMath"]) + '</div>'
            '<div class="proof-layout"><article class="mathematical-proof"><h3>Mathematical proof</h3>'
            + explanation + '</article><div class="lean-proof"><h3>Lean proof</h3>'
            + source_card(item["file"], sources[item["file"]], item["start"], item["end"])
            + ('<details class="statement-notation"><summary>Read every piece of the theorem statement</summary>'
               '<div class="statement-token-panel"></div></details>' if item.get("statementTokens") and item["theorem"] != "IsConvex" else '')
            + '<div class="code-explanation" aria-live="polite"></div></div></div>'
            '<section class="goal-panel" aria-label="Lean proof state"><div class="goal-title">'
            '<h3>Lean’s proof state</h3><span>Output captured from Lean for these exact source files</span></div>'
            '<div class="goal-layout"><div><h4>Before these commands</h4><pre class="goal-before"></pre></div>'
            '<div><h4>After these commands</h4><pre class="goal-after"></pre></div></div>'
            '<p class="goal-key"><code>name : type</code> records available data or a proved fact. '
            '<code>⊢</code> marks the statement still to be proved. These lines are Lean’s report, not additional code to type.</p></section>'
            '<nav class="step-navigation" aria-label="Proof steps"><button class="step-prev" type="button">← Previous</button>'
            '<span class="step-position" aria-live="polite"></span><button class="step-next" type="button">Next →</button></nav>'
            '</section>')
    full_sources = ''.join(f'<section class="file-source" data-file="{path}"><h3>{html.escape(path)}</h3>'
        + source_card(path, lines, 1, len(lines), full=True) + '</section>' for path, lines in sources.items())
    guide = ''.join(f'<dt><code>{html.escape(token)}</code></dt><dd>{prose(description)}</dd>' for token, description in DECLARATION_GUIDE)
    setup = notes.get("setup", [])
    setup_html = ''
    if setup:
        setup_html = '<details class="setup-guide"><summary>File setup and code conventions</summary>'
        for entry in setup:
            if isinstance(entry, str):
                setup_html += '<p>' + prose(entry) + '</p>'
            else:
                setup_html += '<h3>' + html.escape(entry.get("title", entry.get("token", "Setup"))) + '</h3>'
                setup_html += '<div>' + prose(entry.get("explanation", entry.get("description", ""))) + '</div>'
                if entry.get("tokens"):
                    setup_html += '<dl class="setup-tokens">' + ''.join('<dt><code>' + html.escape(token["token"]) + '</code></dt><dd>' + prose(token["explanation"]) + '</dd>' for token in entry["tokens"]) + '</dl>'
        setup_html += '</details>'
    payload = {"lessons": lessons, "sourceHashes": hashes, "stateSourceHashes": states.get("sourceHashes", {}),
               "declarationGuide": DECLARATION_GUIDE}
    encoded = json.dumps(payload, ensure_ascii=False).replace("<", "\\u003c").replace(">", "\\u003e").replace("&", "\\u0026")
    page = ('<!doctype html><html lang="en"><head><meta charset="utf-8">'
        '<meta name="viewport" content="width=device-width,initial-scale=1">'
        '<title>Convexity in Lean · short proofs for optimization</title>'
        '<meta name="description" content="Learn Lean from its first syntax conventions through short convexity proofs, with exact source and genuine proof states.">'
        '<link rel="icon" type="image/svg+xml" href="assets/favicon.svg">'
        '<link rel="stylesheet" href="assets/vendor/katex/katex.min.css"><link rel="stylesheet" href="assets/tutorial.css">'
        '<script defer src="assets/vendor/katex/katex.min.js"></script><script defer src="assets/tutorial.js"></script></head><body>'
        '<a class="skip-link" href="#tutorial">Skip to tutorial</a>'
        '<aside class="sidebar"><a class="site-name" href="#tutorial">CONVEXITY / LEAN</a>'
        '<p class="track-label">Short proofs for optimization</p><nav aria-label="Lesson sequence">' + nav + '</nav>'
        '<button id="show-files" type="button">Source files</button><a class="project-readme" href="../README.md">About this tutorial ↗</a></aside>'
        '<main id="tutorial"><header class="page-header"><h1>Convexity in Lean</h1>'
        '<p>Rigorous elementary proofs, with the proof language explained from the beginning.</p>'
        '<div class="header-actions"><button id="resume-reading" type="button" hidden>Resume reading</button>'
        '<button id="show-notation" type="button" aria-expanded="false" aria-controls="notation-guide">Read Lean notation</button></div></header>'
        '<section id="notation-guide" hidden><h2>Reading a Lean declaration</h2><dl>' + guide + '</dl>' + setup_html + '</section>'
        '<div class="reading-guide"><strong>How to read.</strong> Select one mathematical step to outline the corresponding code. '
        'The explanation below the code unpacks its syntax, and the proof state shows exactly what changed.</div>'
        '<noscript><p>All lessons and source files are readable below. Enable JavaScript for step selection and captured proof-state displays.</p></noscript>'
        + ''.join(sections)
        + '<section id="source-browser" hidden><div class="source-browser-heading"><h2>Complete source files</h2>'
        '<button id="return-to-proof" type="button">← Return to the proof</button></div>'
        '<p>These are the same files checked by Lean, with their original line numbers. '
        'The Mathlib equivalence theorems in Definitions.lean connect the introductory predicates to the library definitions.</p>'
        + full_sources + '</section>'
        '<footer><p>Kernel-checked source · Lean 4 / Mathlib · all mathematics rendered locally with KaTeX.</p>'
        '<p><a href="source-manifest.json">Source manifest</a> · <a href="../README.md">Build and verification instructions</a></p></footer></main>'
        '<div id="reader-status" class="sr-only" role="status" aria-live="polite"></div>'
        '<script type="application/json" id="tutorial-data">' + encoded + '</script></body></html>')
    (SITE / "index.html").write_text(page)
    (SITE / "source-manifest.json").write_text(json.dumps({"files": hashes, "lessons": [{"id": item["id"], "file": item["file"], "start": item["start"], "end": item["end"]} for item in lessons]}, indent=2) + '\n')
    print(f'Built {SITE / "index.html"}: {len(lessons)} lessons, {sum(len(item["steps"]) for item in lessons)} explained steps')


if __name__ == "__main__":
    main()
