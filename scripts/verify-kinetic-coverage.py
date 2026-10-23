#!/usr/bin/env python3
"""Check source correspondence separately from completion of paper proofs.

The default checks source hashes, complete result/label inventories, actual
Lean references, and absence of proof holes. --require-complete additionally
requires all paper-level stochastic endpoints to be supplied. Passing a Lean
build or this integrity check alone never sets the completion flag.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "docs"))
from build_site import declarations, HELPERS

KINDS = "theorem|proposition|lemma|cor|assumption|remark|algorithm"
ENVIRONMENT = re.compile(r"\\begin\{(" + KINDS + r")\}(.*?)\\end\{\1\}", re.S)


def uncomment(tex):
    return re.sub(r"(?<!\\)%[^\n]*", "", tex)


def verify(require_complete=False):
    incomplete = []
    for lib in ("KineticLangevin", "KIPLMC"):
        audit = json.loads((ROOT / lib / "exposition/reference_audit.json").read_text())
        source = {}
        for entry in audit["source"]["files"]:
            file = ROOT / entry["path"]
            assert file.is_file(), f"Missing reference input: {file}"
            raw = file.read_bytes()
            assert hashlib.sha256(raw).hexdigest() == entry["sha256"], f"Source changed: {file}"
            source[entry["path"]] = raw.decode()

        expected = Counter()
        for path, tex in source.items():
            for match in re.finditer(r"\\label\{([^}]+)\}", uncomment(tex)):
                expected[(path, match[1])] += 1
        recorded = Counter((entry["source_file"], entry["label"]) for entry in audit["source_labels"])
        assert recorded == expected, f"Incomplete source label inventory: {lib}: {expected-recorded}, {recorded-expected}"

        counts = Counter()
        statements = Counter()
        for path, tex in source.items():
            for match in ENVIRONMENT.finditer(uncomment(tex)):
                counts[match[1]] += 1
                statements[(path, match[1], match[2].strip())] += 1
        assert counts == Counter(audit["counts"]), f"Incorrect source result counts: {lib}"
        recorded_statements = Counter((entry["source_file"], entry["kind"],
                                       entry["source_statement_tex"].strip())
                                      for entry in audit["results"])
        assert statements == recorded_statements, f"Altered or missing source statements: {lib}"

        for entry in audit["source_labels"]:
            lines = source[entry["source_file"]].splitlines()
            line = lines[entry["source_line"]-1]
            assert "\\label{" + entry["label"] + "}" in line, f"Stale source line: {entry}"
        for result in audit["results"]:
            lines = source[result["source_file"]].splitlines()
            start, end = result["source_start"], result["source_end"]
            assert 1 <= start <= end <= len(lines), f"Invalid statement range: {result['id']}"
            assert "\\begin{" + result["kind"] + "}" in lines[start-1], f"Stale statement start: {result['id']}"
            assert "\\end{" + result["kind"] + "}" in lines[end-1], f"Stale statement end: {result['id']}"
        for check in audit["checks"]:
            for path in check["lean_files"]:
                assert (ROOT / path).is_file(), f"Nonexistent Lean correspondence: {lib}: {path}"

        for file in (ROOT / lib).rglob("*.lean"):
            masked = "\n".join(HELPERS.mask_comments(file.read_text().splitlines()))
            assert not re.search(r"\b(sorry|admit|sorryAx)\b|^\s*axiom\b", masked, re.M), f"Proof hole: {file}"
        missing = []
        labels = {entry["label"] for entry in audit["source_labels"]}
        result_ids = {entry["id"] for entry in audit["results"]}
        for endpoint in audit["required_endpoints"]:
            if endpoint.get("source_label"):
                assert endpoint["source_label"] in labels, f"Unknown source label: {lib}: {endpoint}"
            else:
                assert endpoint.get("source_result") in result_ids, f"Unknown source result: {lib}: {endpoint}"
            path, name = endpoint["file"], endpoint["declaration"]
            if path and name:
                assert name in declarations((ROOT / path).read_text()), f"Missing endpoint declaration: {lib}: {name}"
            if endpoint["status"] != "proved" or not path or not name:
                missing.append(endpoint["id"])
        assert audit["formalization_complete"] == (not missing), f"Incorrect completion flag: {lib}"
        print(f"{lib}: source correspondence verified; paper-level proofs " +
              ("COMPLETE" if not missing else "INCOMPLETE (" + ", ".join(missing) + ")"))
        incomplete.extend(f"{lib}: {name}" for name in missing)
    if require_complete and incomplete:
        raise SystemExit("Full formalization is not complete:\n" + "\n".join(incomplete))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    verify(parser.parse_args().require_complete)
