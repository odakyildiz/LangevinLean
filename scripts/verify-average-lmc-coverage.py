#!/usr/bin/env python3
"""Verify Average LMC correspondence without confusing compilation and coverage.

The default verifies exact source statements, their full inventory, checked
declaration references, and absence of proof holes. --require-complete rejects
both unproved endpoints and a refuted source result. --require-resolved checks
the revised review scope: proved main statements and linked, checked
counterexamples to false source statements.
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

KINDS = "theorem|proposition|lemma|remark|corollary|condition|defin"
ENVIRONMENT = re.compile(r"\\begin\{(" + KINDS + r")\}(.*?)\\end\{\1\}", re.S)


def verify(require_complete=False, require_resolved=False):
    audit = json.loads((ROOT / "AverageLMC/exposition/reference_audit.json").read_text())
    sources = {}
    for entry in audit["source"]["files"]:
        raw = (ROOT / entry["path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == entry["sha256"], "Manuscript changed"
        sources[entry["path"]] = re.sub(r"(?<!\\)%[^\n]*", "", raw.decode())
    expected_labels = Counter((path, m[1], tex[:m.start()].count("\n") + 1)
                              for path, tex in sources.items()
                              for m in re.finditer(r"\\label\{([^}]+)\}", tex))
    recorded_labels = Counter((entry["source_file"], entry["label"], entry["source_line"])
                              for entry in audit["source_labels"])
    assert expected_labels == recorded_labels, "Missing or stale source label inventory"
    expected = Counter((path, m[1], m[2].strip(), tex[:m.start()].count("\n") + 1,
                        tex[:m.end()].count("\n") + 1)
                       for path, tex in sources.items() for m in ENVIRONMENT.finditer(tex))
    recorded = Counter((entry["source_file"], entry["kind"], entry["source_statement_tex"],
                        entry["source_start"], entry["source_end"])
                       for entry in audit["results"])
    assert expected == recorded, "Missing, altered or stale manuscript result"
    assert Counter(entry["kind"] for entry in audit["results"]) == Counter(audit["counts"])
    parsed = {}
    for path in sorted((ROOT / "AverageLMC").rglob("*.lean")):
        relative = path.relative_to(ROOT).as_posix()
        source = path.read_text()
        masked = "\n".join(HELPERS.mask_comments(source.splitlines()))
        assert not re.search(r"\b(sorry|admit|sorryAx)\b|^\s*axiom\b", masked, re.M), \
            f"Proof hole: {relative}"
        parsed[relative] = declarations(source)
    for entry in audit["checks"]:
        for path in entry["lean_files"]:
            assert path in parsed, f"Missing source correspondence: {path}"
    certificates = {
        "AverageLMC/GradientStep.lean": ["gradient_step", "gradient_descent"],
        "AverageLMC/Recurrence.lean": ["constant_step_normalized"],
        "AverageLMC/Complexity.lean": ["variable_step_accuracy"],
        "AverageLMC/GLMObstruction.lean": ["counterexamplePotential_hessian_lipschitz_lower",
                                           "counterexampleComponent_derivative_bound"],
        "AverageLMC/GaussianObstruction.lean": ["stdGaussian_cube_bound_fails"],
        "AverageLMC/GLMCounterexample.lean": ["no_uniform_glmHessian_bound"],
    }
    for path, names in certificates.items():
        for name in names:
            assert name in parsed[path], f"Missing certificate: {path}:{name}"
    unfinished_results = []
    for result in audit["results"]:
        if result["kind"] == "remark":
            continue  # The source's discussion of proof limitations is informational.
        proofs = result.get("proofs", [])
        for proof in proofs:
            assert proof["declaration"] in parsed[proof["file"]], \
                f"Missing result proof correspondence: {result['id']}"
        for proof in result.get("counterexamples", []):
            assert proof["declaration"] in parsed[proof["file"]], \
                f"Missing counterexample certificate: {result['id']}"
        if result["status"] != "proved" or not proofs:
            unfinished_results.append(result["id"])
    labels = {entry["label"] for entry in audit["source_labels"]}
    missing = []
    for endpoint in audit["required_endpoints"]:
        assert endpoint["source_label"] in labels
        path, name = endpoint["file"], endpoint["declaration"]
        if path and name:
            assert name in parsed[path]
        if endpoint["status"] != "proved" or not path or not name:
            missing.append(endpoint["id"])
    refuted = [entry["id"] for entry in audit["results"] if entry["status"] == "refuted"]
    complete = not missing and not unfinished_results and not refuted
    assert audit["formalization_complete"] == complete, "Incorrect completion flag"
    from average_content import AVERAGE_PAGES
    scope = audit["review_scope"]
    by_id = {result["id"]: result for result in audit["results"]}
    unresolved = []
    for identifier in scope["results"]:
        result = by_id[identifier]
        proved = result["status"] == "proved" and result.get("proofs")
        counterexample = (result["status"] == "refuted" and result.get("counterexamples")
                          and result.get("counterexample_page") in AVERAGE_PAGES)
        if not (proved or counterexample):
            unresolved.append(identifier)
    for page in scope["counterexample_pages"]:
        assert page in AVERAGE_PAGES, f"Missing separate counterexample page: {page}"
        references = [ref for section in AVERAGE_PAGES[page]["sections"]
                      for ref in section.get("references", [])]
        assert references, f"Counterexample page has no checked certificate: {page}"
        for ref in references:
            assert ref["name"] in parsed[ref["file"]], f"Missing page certificate: {page}"
    resolved = not unresolved
    assert scope["complete"] == resolved, "Incorrect review-scope completion flag"
    print(f"AverageLMC: {sum(audit['counts'].values())} exact source results and "
          f"{len(recorded_labels)} labels verified; checked certificates present.")
    print("Full-paper formalization: " + ("COMPLETE" if complete else "INCOMPLETE"))
    print("Main-theorem and counterexample review scope: " + ("COMPLETE" if resolved else "INCOMPLETE"))
    if refuted:
        print("Refuted source results: " + ", ".join(refuted))
    if require_complete and not complete:
        raise SystemExit("Exact full-paper coverage cannot pass. Open/refuted results: " +
                         ", ".join(unfinished_results) + "; endpoints: " + ", ".join(missing))
    if require_resolved and not resolved:
        raise SystemExit("Main-theorem review scope is unfinished: " + ", ".join(unresolved))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--require-resolved", action="store_true")
    args = parser.parse_args()
    verify(args.require_complete, args.require_resolved)
