#!/usr/bin/env python3
"""Verify the generated convexity tutorial against its sources and Lean captures.

This checks source correspondence, annotation coverage, capture provenance,
links, and KaTeX syntax. It does not infer Lean goal states from HTML. The states
must match a successful capture_goals.py output for the current source and
step-boundary hashes. Current explanatory text is checked separately. Use
--recapture to independently rerun that Lean capture in
temporary files and compare its actual goal reports with the displayed data.
"""

from __future__ import annotations

import argparse
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from urllib.parse import unquote, urlsplit

from capture_goals import lesson_steps, step_ranges
from build_page import DECLARATION_GUIDE, prose

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SITE = HERE / "site"
IDENTIFIER = re.compile(r"^[A-Za-z][A-Za-z0-9_-]*$")
TEX = re.compile(r"\\\[([\s\S]*?)\\\]|\\\(([\s\S]*?)\\\)")
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link",
        "meta", "param", "source", "track", "wbr"}
DECLARATION_SYNTAX = {"theorem", "lemma", "def", "import", "namespace", "end",
    "∀", "→", "↦", ":", ":=", ":= by", ": Prop", "Prop", "ℝ", "()", "( )",
    "function application", "application", "parentheses", "implicit arguments"}


class Node:
    def __init__(self, tag="document", attrs=None, parent=None):
        self.tag, self.attrs, self.parent = tag, dict(attrs or []), parent
        self.content = []

    def has_class(self, name):
        return name in self.attrs.get("class", "").split()

    def text(self, excluded_class=None):
        if excluded_class and self.has_class(excluded_class):
            return ""
        return "".join(item.text(excluded_class) if isinstance(item, Node) else item
                       for item in self.content)

    def descendants(self):
        for item in self.content:
            if isinstance(item, Node):
                yield item
                yield from item.descendants()


class Document(HTMLParser):
    def __init__(self, text):
        super().__init__(convert_charrefs=True)
        self.root = Node()
        self.stack = [self.root]
        self.feed(text)
        self.close()
        self.nodes = list(self.root.descendants())

    def handle_starttag(self, tag, attrs):
        node = Node(tag, attrs, self.stack[-1])
        self.stack[-1].content.append(node)
        if tag not in VOID:
            self.stack.append(node)

    def handle_startendtag(self, tag, attrs):
        self.stack[-1].content.append(Node(tag, attrs, self.stack[-1]))

    def handle_endtag(self, tag):
        for index in range(len(self.stack) - 1, 0, -1):
            if self.stack[index].tag == tag:
                self.stack = self.stack[:index]
                return

    def handle_data(self, text):
        self.stack[-1].content.append(text)


class Verification:
    def __init__(self):
        self.errors, self.precision, self.counts = [], [], {}

    def require(self, condition, message):
        if not condition:
            self.errors.append(message)
        return bool(condition)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def step_hash(notes):
    return hashlib.sha256(json.dumps(step_ranges(lesson_steps(notes)),
                                    ensure_ascii=False, sort_keys=True).encode()).hexdigest()


def repository_file(value):
    path = Path(value)
    if path.is_absolute() or ".." in path.parts:
        raise ValueError(f"Source path must be repository-relative: {value!r}")
    return ROOT / path


def ancestor(node, class_name):
    while node:
        if node.has_class(class_name):
            return node
        node = node.parent
    return None


def read_json(path, report):
    if not report.require(path.is_file(), f"Missing required file: {path}"):
        return None
    try:
        return json.loads(path.read_text())
    except (ValueError, OSError) as error:
        report.errors.append(f"Cannot read JSON {path}: {error}")
        return None


def source_checks(data, document, report):
    sources = {}
    hashes = data.get("sourceHashes", {})
    report.require(isinstance(hashes, dict) and bool(hashes), "Missing sourceHashes")
    for relative, expected in hashes.items():
        try:
            path = repository_file(relative)
        except ValueError as error:
            report.errors.append(str(error))
            continue
        if not report.require(path.is_file(), f"Missing Lean source: {relative}"):
            continue
        report.require(digest(path) == expected, f"Stale page source hash: {relative}")
        copy = SITE / "sources" / relative
        report.require(copy.is_file() and copy.read_bytes() == path.read_bytes(),
                       f"Downloaded source differs from repository: {relative}")
        sources[relative] = path.read_text().splitlines()
    cards = [node for node in document.nodes if node.has_class("source-card")]
    for card in cards:
        relative = card.attrs.get("data-file")
        label = f"Source card {relative}"
        if not report.require(relative in sources, f"{label}: unknown file"):
            continue
        try:
            start, end = int(card.attrs["data-start"]), int(card.attrs["data-end"])
        except (KeyError, ValueError):
            report.errors.append(f"{label}: invalid data-start/data-end")
            continue
        lines = sources[relative]
        if not report.require(1 <= start <= end <= len(lines), f"{label}: invalid range {start}–{end}"):
            continue
        displayed = [node for node in card.descendants() if node.has_class("code-line")]
        report.require(len(displayed) == end - start + 1, f"{label}: wrong displayed line count")
        for number, line in zip(range(start, end + 1), displayed):
            report.require(line.attrs.get("data-line") == str(number),
                           f"{label}: data-line does not match line {number}")
            numbers = [node for node in line.descendants() if node.has_class("line-number")]
            report.require(len(numbers) == 1 and numbers[0].text() == str(number),
                           f"{label}: incorrect visible number for line {number}")
            report.require(line.text("line-number") == lines[number - 1],
                           f"{label}: displayed text differs at source line {number}")
    for relative, lines in sources.items():
        report.require(any(card.attrs.get("data-file") == relative
                           and card.attrs.get("data-start") == "1"
                           and card.attrs.get("data-end") == str(len(lines)) for card in cards),
                       f"Complete source card missing: {relative}")
    report.counts.update(sourceFiles=len(sources), sourceCards=len(cards))
    return sources


def token_present(token, source):
    if token.isidentifier():
        return re.search(r"(?<![\w'])" + re.escape(token) + r"(?![\w'])", source) is not None
    return token in source


def annotation_checks(data, notes, states, sources, document, report):
    lessons = data.get("lessons", [])
    report.require(isinstance(lessons, list) and bool(lessons), "No tutorial lessons")
    lesson_ids, step_ids, expected_capture_ids = set(), set(), set()
    original = {item["id"]: item for item in notes.get("lessons", [])}
    captured = states.get("steps", {})
    for lesson in lessons:
        identifier = lesson.get("id", "")
        report.require(isinstance(identifier, str) and IDENTIFIER.fullmatch(identifier),
                       f"Invalid lesson ID: {identifier!r}")
        report.require(identifier not in lesson_ids, f"Duplicate lesson ID: {identifier}")
        for prerequisite in lesson.get("prerequisites", []):
            target = prerequisite if isinstance(prerequisite, str) else prerequisite.get("id", prerequisite.get("lesson"))
            report.require(target in lesson_ids,
                           f"{identifier}: prerequisite {target!r} is not a previous lesson")
        lesson_ids.add(identifier)
        report.require(identifier in original, f"{identifier}: not in current lesson_notes.json")
        for key, value in original.get(identifier, {}).items():
            if key == "steps":
                continue
            if key == "file" and not value.startswith("ConvexityTutorial/"):
                value = "ConvexityTutorial/" + value
            report.require(lesson.get(key) == value, f"{identifier}: stale lesson annotation field {key}")
        relative = lesson.get("file")
        if not report.require(relative in sources, f"{identifier}: unknown source file {relative}"):
            continue
        lines = sources[relative]
        start, end = lesson.get("start"), lesson.get("end")
        if not report.require(type(start) is int and type(end) is int
                              and 1 <= start <= end <= len(lines), f"{identifier}: invalid declaration range"):
            continue
        first = lines[start - 1]
        name = lesson.get("theorem")
        report.require(re.match(r"^(?:theorem|lemma|def)\s+" + re.escape(str(name)) + r"\b", first),
                       f"{identifier}: declaration range does not start at {name}")
        cards = [node for node in document.nodes if node.has_class("source-card")
                 and ancestor(node, "lesson")
                 and ancestor(node, "lesson").attrs.get("data-lesson") == identifier]
        report.require(len(cards) == 1 and cards[0].attrs.get("data-file") == relative
                       and cards[0].attrs.get("data-start") == str(start)
                       and cards[0].attrs.get("data-end") == str(end),
                       f"{identifier}: lesson source card disagrees with its metadata")
        block = "\n".join(lines[start - 1:end])
        proof_start = next((number for number in range(start, end + 1)
                            if ":= by" in lines[number - 1]), None)
        body = set()
        if proof_start:
            if lines[proof_start - 1].split(":= by", 1)[1].strip():
                body.add(proof_start)
            body.update(number for number in range(proof_start + 1, end + 1)
                        if lines[number - 1].strip()
                        and not lines[number - 1].lstrip().startswith(("--", "/-", "-/")))
        coverage = set()
        original_steps = {item["id"]: item for item in original.get(identifier, {}).get("steps", [])}
        for step in lesson.get("steps", []):
            sid = step.get("id", "")
            report.require(isinstance(sid, str) and IDENTIFIER.fullmatch(sid), f"Invalid step ID: {sid!r}")
            report.require(sid not in step_ids, f"Duplicate step ID: {sid}")
            step_ids.add(sid)
            expected_capture_ids.add(sid)
            low, high = step.get("start"), step.get("end")
            if not report.require(type(low) is int and type(high) is int
                                  and start <= low <= high <= end, f"{sid}: range is outside its declaration"):
                continue
            raw_step = original_steps.get(sid)
            report.require(raw_step is not None, f"{sid}: absent from current annotation source")
            if raw_step:
                for key, value in raw_step.items():
                    report.require(step.get(key) == value, f"{sid}: stale annotation field {key}")
            kind = step.get("kind", step.get("type", "tactic"))
            if kind != "declaration":
                coverage.update(range(low, high + 1))
            state = step.get("verifiedState")
            if not report.require(isinstance(state, dict), f"{sid}: no captured Lean state"):
                continue
            report.require(state == captured.get(sid), f"{sid}: displayed state differs from proof_states.json")
            report.require(state.get("verified") is True, f"{sid}: capture not verified")
            report.require(state.get("file") == relative and state.get("start") == low
                           and state.get("end") == high and state.get("kind") == kind,
                           f"{sid}: capture source range/kind mismatch")
            if kind == "declaration":
                report.require(not (set(range(low, high + 1)) & body),
                               f"{sid}: a declaration step covers actual tactic commands")
                report.require(state.get("declaration") == "\n".join(lines[low - 1:high]),
                               f"{sid}: captured declaration text differs from source")
                for phase in ("before", "after"):
                    value = state.get(phase)
                    report.require(isinstance(value, dict) and value.get("kind") == "declaration"
                                   and "raw" not in value,
                                   f"{sid}: declaration has fictional tactic-state output")
            else:
                for phase in ("before", "after"):
                    value = state.get(phase)
                    report.require(isinstance(value, dict) and isinstance(value.get("raw"), str),
                                   f"{sid}: {phase} must contain raw Lean output")
                    if isinstance(value, dict) and isinstance(value.get("raw"), str):
                        report.require(value.get("noGoals") == (value["raw"] == ""),
                                       f"{sid}: {phase} noGoals disagrees with Lean output")
                        report.require(type(value.get("traceLine")) is int and value["traceLine"] > 0,
                                       f"{sid}: {phase} lacks a trace source position")
            code = "\n".join(lines[low - 1:high])
            context_names = {entry.get("name") for entry in step.get("context", []) if isinstance(entry, dict)}
            for entry in step.get("tokens", []):
                token = entry.get("token", "") if isinstance(entry, dict) else entry
                if not report.require(isinstance(token, str) and token, f"{sid}: empty code token"):
                    continue
                if token_present(token, code):
                    continue
                generic = token in DECLARATION_SYNTAX or (isinstance(entry, dict) and entry.get("kind") in {"syntax", "generic", "context", "declaration"})
                if generic or token in context_names or token_present(token, block):
                    report.precision.append(f"{sid}: token {token!r} is contextual/declaration syntax, absent from selected lines {low}–{high}")
                else:
                    report.errors.append(f"{sid}: token {token!r} occurs neither in its selected code nor its declaration/context")
        missing = sorted(body - coverage)
        report.require(not missing, f"{identifier}: unannotated proof-command lines {missing}")
    report.require(lesson_ids == set(original), "Generated lesson set differs from current notes")
    report.require(expected_capture_ids == set(captured), "Captured-step set differs from displayed-step set")
    report.require(data.get("declarationGuide") == [list(item) for item in DECLARATION_GUIDE],
                   "Displayed declaration guide differs from the generator's current guide")
    report.counts.update(lessons=len(lessons), explainedSteps=len(step_ids))


def displayed_annotation_checks(data, document, report):
    def children_with_class(node, name):
        return [item for item in node.descendants() if item.has_class(name)]

    def same_prose(element, value, label):
        expected = Document(prose(value))
        report.require(element.text() == expected.root.text(), f"{label}: displayed explanation differs from its metadata")
        expected_math = [(node.attrs["data-tex"], node.attrs.get("data-display"))
                         for node in expected.nodes if "data-tex" in node.attrs]
        actual_math = [(node.attrs["data-tex"], node.attrs.get("data-display"))
                       for node in element.descendants() if "data-tex" in node.attrs]
        report.require(actual_math == expected_math, f"{label}: displayed inline/display TeX differs from its metadata")

    for lesson in data.get("lessons", []):
        identifier = lesson["id"]
        sections = [node for node in document.nodes if node.has_class("lesson")
                    and node.attrs.get("data-lesson") == identifier]
        if not report.require(len(sections) == 1, f"{identifier}: missing/duplicate rendered lesson"):
            continue
        section = sections[0]
        purpose = children_with_class(section, "purpose")
        if report.require(len(purpose) == 1, f"{identifier}: missing purpose text"):
            same_prose(purpose[0], lesson.get("why", ""), identifier + ".why")
        statements = children_with_class(section, "theorem-statement")
        if report.require(len(statements) == 1, f"{identifier}: missing theorem statement"):
            math = [node for node in statements[0].descendants() if "data-tex" in node.attrs]
            report.require(len(math) == 1 and math[0].attrs.get("data-tex") == lesson.get("statementMath")
                           and math[0].attrs.get("data-display") == "true",
                           f"{identifier}: displayed theorem mathematics differs from its metadata")
        for step in lesson.get("steps", []):
            sid = step["id"]
            nodes = [node for node in section.descendants() if node.has_class("math-step")
                     and node.attrs.get("data-step") == sid]
            if not report.require(len(nodes) == 1, f"{sid}: missing/duplicate rendered mathematical step"):
                continue
            direct_math = [node for node in nodes[0].content if isinstance(node, Node)
                           and "data-tex" in node.attrs]
            expected = [step["math"]] if step.get("math") else []
            report.require([node.attrs["data-tex"] for node in direct_math] == expected,
                           f"{sid}: displayed step mathematics differs from its metadata")
            explanations = children_with_class(nodes[0], "step-prose")
            if report.require(len(explanations) == 1, f"{sid}: missing mathematical explanation"):
                same_prose(explanations[0], step.get("explanation", ""), sid)


def capture_checks(data, states, notes_path, report):
    capture = states.get("capture", {})
    report.require(capture.get("method") == "Lean trace_state in checked temporary copies",
                   "Proof states lack the genuine Lean capture-method record")
    report.require(capture.get("originalSourcesEdited") is False,
                   "Goal capture must leave the original sources unchanged")
    report.require(isinstance(capture.get("leanVersion"), str) and bool(capture["leanVersion"]),
                   "Goal capture lacks the checked Lean version")
    notes = json.loads(notes_path.read_text())
    report.require(capture.get("stepRangesHash") == step_hash(notes),
                   "Goal capture was generated for different lesson step boundaries")
    state_hashes = states.get("sourceHashes", {})
    report.require(data.get("stateSourceHashes") == state_hashes,
                   "Displayed capture hashes differ from proof_states.json")
    selected_files = {lesson["file"] for lesson in data.get("lessons", [])}
    report.require(selected_files <= set(state_hashes), "Goal capture lacks hashes for selected tutorial sources")
    for relative, expected in state_hashes.items():
        try:
            path = repository_file(relative)
        except ValueError as error:
            report.errors.append(str(error))
            continue
        report.require(path.is_file() and digest(path) == expected,
                       f"Goal capture is stale for source: {relative}")
        report.require(data.get("sourceHashes", {}).get(relative) == expected,
                       f"Goal capture/page source hash mismatch: {relative}")


def link_checks(document, page_path, report):
    ids = [node.attrs["id"] for node in document.nodes if "id" in node.attrs]
    report.require(len(ids) == len(set(ids)), "Duplicate HTML IDs")
    css = set()
    references = 0
    for node in document.nodes:
        for attribute in ("href", "src"):
            value = node.attrs.get(attribute)
            if not value:
                continue
            parsed = urlsplit(value)
            if parsed.scheme or parsed.netloc:
                continue
            references += 1
            target = (page_path.parent / unquote(parsed.path)).resolve() if parsed.path else page_path.resolve()
            if not report.require(target.is_file(), f"Broken local {attribute}: {value}"):
                continue
            if target.suffix == ".css":
                css.add(target)
            if parsed.fragment:
                if target == page_path.resolve():
                    report.require(unquote(parsed.fragment) in ids, f"Missing page anchor: {value}")
                elif target.suffix in {".html", ".htm"}:
                    other = Document(target.read_text())
                    other_ids = {item.attrs.get("id") for item in other.nodes}
                    report.require(unquote(parsed.fragment) in other_ids, f"Missing local HTML anchor: {value}")
    checked_css, font_references = set(), 0
    while css - checked_css:
        path = (css - checked_css).pop()
        checked_css.add(path)
        for value in re.findall(r"url\(\s*['\"]?([^)'\"]+)['\"]?\s*\)", path.read_text()):
            parsed = urlsplit(value.strip())
            if parsed.scheme or parsed.netloc:
                continue
            target = (path.parent / unquote(parsed.path)).resolve()
            report.require(target.is_file(), f"Broken stylesheet asset: {path.name} → {value}")
            font_references += target.suffix in {".woff", ".woff2", ".ttf", ".otf"}
            if target.suffix == ".css":
                css.add(target)
    report.require(font_references > 0, "No vendored KaTeX font references were checked")
    report.counts.update(localReferences=references, stylesheets=len(checked_css), fontReferences=font_references)


def math_checks(data, notes, document, node_command, report):
    expressions = []
    for index, element in enumerate(document.nodes):
        if "data-tex" in element.attrs:
            expressions.append({"label": f"DOM element {index}", "tex": element.attrs["data-tex"],
                                "display": element.attrs.get("data-display") == "true"})
    def walk(value, path):
        if isinstance(value, dict):
            for key, item in value.items():
                child = path + "." + key
                if isinstance(item, str) and (key.lower().endswith("math") or key == "tex"):
                    if item:
                        expressions.append({"label": child, "tex": item, "display": True})
                else:
                    walk(item, child)
        elif isinstance(value, list):
            for index, item in enumerate(value):
                walk(item, path + f"[{index}]")
        elif isinstance(value, str):
            for match in TEX.finditer(value):
                display = match.group(1) is not None
                expressions.append({"label": path, "tex": match.group(1) if display else match.group(2),
                                    "display": display})
    walk(data, "tutorial-data")
    walk(notes, "lesson_notes")
    vendor = SITE / "assets/vendor/katex/katex.min.js"
    if not report.require(vendor.is_file(), "Vendored KaTeX JavaScript is missing"):
        return
    script = r"""
const fs = require('node:fs');
const katex = require(process.argv[1]);
const inputs = JSON.parse(fs.readFileSync(0, 'utf8'));
const errors = [];
for (const input of inputs) {
  try { katex.renderToString(input.tex, {displayMode: input.display, throwOnError: true, strict: 'error'}); }
  catch (error) { errors.push({label: input.label, error: error.message, tex: input.tex}); }
}
process.stdout.write(JSON.stringify({count: inputs.length, errors}));
"""
    try:
        result = subprocess.run([node_command, "-e", script, str(vendor)],
                                input=json.dumps(expressions), text=True, capture_output=True,
                                timeout=60, check=True)
        output = json.loads(result.stdout)
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        report.errors.append(f"Cannot validate TeX with local KaTeX/Node: {error}")
        return
    for error in output["errors"]:
        report.errors.append(f"Invalid TeX at {error['label']}: {error['error']}; expression {error['tex']!r}")
    report.counts["texExpressions"] = output["count"]


def recapture_check(states, notes_path, report):
    with tempfile.TemporaryDirectory(prefix="convexity-verify-") as temporary:
        target = Path(temporary) / "fresh_states.json"
        command = [sys.executable, str(HERE / "capture_goals.py"), "--notes", str(notes_path),
                   "--output", str(target), "--timeout", "120"]
        try:
            result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True,
                                    timeout=600, check=True)
            fresh = json.loads(target.read_text())
        except (OSError, subprocess.SubprocessError, ValueError) as error:
            details = getattr(error, "stdout", "") or ""
            report.errors.append(f"Fresh genuine Lean capture failed: {error}\n{details}")
            return
        report.require(fresh.get("steps") == states.get("steps"),
                       "Fresh Lean goal reports differ from the displayed capture")
        report.require(fresh.get("sourceHashes") == states.get("sourceHashes"),
                       "Fresh Lean capture source hashes differ")
        report.require(fresh.get("capture", {}).get("stepRangesHash") == states.get("capture", {}).get("stepRangesHash"),
                       "Fresh Lean capture step-boundary hash differs")
        report.counts["freshLeanCapture"] = True
        print(result.stdout.strip())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--page", type=Path, default=SITE / "index.html")
    parser.add_argument("--node", default="node", help="Node executable for the vendored KaTeX parser")
    parser.add_argument("--recapture", action="store_true", help="Rerun checked temporary Lean proofs and compare their actual states")
    parser.add_argument("--strict-tokens", action="store_true", help="Treat contextual token precision reports as failures")
    args = parser.parse_args()
    report = Verification()
    notes_path = HERE / "lesson_notes.json"
    notes = read_json(notes_path, report)
    states = read_json(HERE / "proof_states.json", report)
    if not report.require(args.page.is_file(), f"Generated page is missing: {args.page}") or notes is None or states is None:
        for error in report.errors:
            print("ERROR:", error, file=sys.stderr)
        return 1
    document = Document(args.page.read_text())
    payloads = [node for node in document.nodes if node.attrs.get("id") == "tutorial-data"]
    if not report.require(len(payloads) == 1, "Expected exactly one #tutorial-data JSON payload"):
        for error in report.errors:
            print("ERROR:", error, file=sys.stderr)
        return 1
    try:
        data = json.loads(payloads[0].text())
    except ValueError as error:
        print(f"ERROR: Invalid #tutorial-data JSON: {error}", file=sys.stderr)
        return 1
    sources = source_checks(data, document, report)
    annotation_checks(data, notes, states, sources, document, report)
    displayed_annotation_checks(data, document, report)
    capture_checks(data, states, notes_path, report)
    link_checks(document, args.page, report)
    math_checks(data, notes, document, args.node, report)
    if args.recapture and not report.errors:
        recapture_check(states, notes_path, report)
    for issue in report.precision:
        print("TOKEN PRECISION:", issue)
    if args.strict_tokens:
        report.errors.extend(report.precision)
    for error in report.errors:
        print("ERROR:", error, file=sys.stderr)
    if report.errors:
        print(f"Verification failed: {len(report.errors)} errors.", file=sys.stderr)
        return 1
    print("Verified tutorial:", json.dumps(report.counts, sort_keys=True))
    print("Goal states match the genuine capture output and its current source/step-boundary hashes."
          + (" Fresh Lean capture also matched." if args.recapture else " This static check does not regenerate those states; use --recapture to do so."))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
