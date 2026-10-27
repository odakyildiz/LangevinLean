#!/usr/bin/env python3
"""Reject unrendered mathematical notation in the project's visible web prose."""
from __future__ import annotations

from collections import Counter
import html
import json
import os
from pathlib import Path
import re

from math_notation import RAW_MATH, VisibleProse

ROOT = Path(__file__).resolve().parents[1]
ARCHIVES = [
    "UnadjustedLangevin/exposition/dist/index.html",
    "UnadjustedLangevin/exposition/main_theorem.html",
    "UnadjustedLangevin/exposition/beginner_guide.html",
    "UnadjustedLangevin/LSI/exposition/proof.html",
    "IPLA/exposition/proof.html",
    "IPLA/LSI/exposition/proof.html",
    "ProximalLangevin/exposition/proof.html",
]


def notation_issues(value):
    parser = VisibleProse()
    parser.feed(value)
    issues = []
    for passage in parser.passages:
        for match in RAW_MATH.finditer(passage):
            prefix = passage[max(0, match.start() - 20):match.start()]
            if re.fullmatch(r"C[0-4]", match[0]) and re.search(
                    r"(?:assumption|condition|premise|label)\s*\(?\s*$", prefix, re.I):
                continue
            context = " ".join(passage[max(0, match.start() - 65):match.end() + 100].split())
            issues.append(context)
    return list(dict.fromkeys(issues))


def markdown_notation_issues(value):
    value = re.sub(r"```.*?```|~~~.*?~~~", "", value, flags=re.S)
    value = re.sub(r"\$\$.*?\$\$|\$[^$\n]*\$|\\\[.*?\\\]|\\\(.*?\\\)", "", value, flags=re.S)
    value = re.sub(chr(96) + "[^" + chr(96) + "]*" + chr(96), "", value)
    value = re.sub(r"\]\([^)]*\)", "]", value)
    return notation_issues(html.escape(value))


def markdown_paths():
    excluded = {".git", ".lake", ".venv", "node_modules", "papers", "vendor"}
    for directory, children, files in os.walk(ROOT):
        children[:] = sorted(child for child in children if child not in excluded)
        for name in sorted(files):
            if name.endswith(".md"):
                yield Path(directory, name)


def verify():
    coverage = json.loads((ROOT / "docs/coverage.json").read_text())
    pages = sorted({path for path in coverage["outputs"] if path.endswith(".html")} | set(ARCHIVES))
    problems = {}
    for page in pages:
        issues = notation_issues((ROOT / page).read_text())
        if issues:
            problems[page] = issues
    markdown = list(markdown_paths())
    for path in markdown:
        issues = markdown_notation_issues(path.read_text())
        if issues:
            problems[str(path.relative_to(ROOT))] = issues
    if problems:
        destination = Path("/tmp/langevin-math-notation-issues.json")
        destination.write_text(json.dumps(problems, indent=2, ensure_ascii=False) + "\n")
        counts = Counter({page: len(issues) for page, issues in problems.items()})
        print(f"Unrendered mathematical notation: {sum(counts.values())} passages in {len(counts)} files.")
        for page, count in counts.most_common(25):
            print(f"{page}: {count}: {problems[page][0]}")
        raise SystemExit(f"Full notation audit: {destination}")
    print(f"Checked mathematical notation in {len(pages)} generated and archived pages and {len(markdown)} Markdown documents.")


if __name__ == "__main__":
    verify()
