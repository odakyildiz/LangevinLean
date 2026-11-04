#!/usr/bin/env python3
"""Check source correspondence and compile the original-assumption paper endpoints."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "docs"))
from build_site import HELPERS, declarations

ENVIRONMENT = re.compile(r"\\begin\{(theorem|corollary|assumption)\}(.*?)\\end\{\1\}", re.S)


SOURCE_ENDPOINTS = {
    "paper-bias": ("eq:w2-bias", "bias_bound"),
    "paper-convergence": ("eq:w2-convergence", "convergence_bound"),
    "paper-complexity": ("eq:complexity_bound", "accuracy_bound"),
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ENDPOINT_FILE = "WassersteinMixing/Theorem.lean"


def completion_state(audit):
    """A complete claim requires actual source endpoints and their compiled audit."""
    results = [item for item in audit["results"] if item["kind"] != "assumption"]
    pending = [item["id"] for item in audit["pending_foundations"] if item["status"] != "proved"]
    unfinished = [item["id"] for item in results
                  if item["status"] != "proved" or not item.get("proofs")]
    endpoints = {item["id"]: item for item in audit["required_endpoints"]}
    missing = []
    for ident, (label, name) in SOURCE_ENDPOINTS.items():
        item = endpoints.get(ident, {})
        if (item.get("status") != "proved" or item.get("file") != ENDPOINT_FILE
                or item.get("source_label") != label or item.get("declaration") != name):
            missing.append(ident)
    compiled = audit.get("compiled_source_audit", {})
    if (compiled.get("status") != "proved"
            or set(compiled.get("declarations", [])) != {name for _, name in SOURCE_ENDPOINTS.values()}
            or set(compiled.get("axioms", [])) != ALLOWED_AXIOMS):
        missing.append("compiled-original-assumption-client")
    return not (pending or unfinished or missing), pending, unfinished, missing


def source_client():
    """Lean clients expose any hidden section hypotheses on the final endpoints."""
    return r"""import WassersteinMixing.Theorem
open MeasureTheory
open WassersteinMixing
noncomputable section
example (P : Parameters) (V : E P.dimension → ℝ) (hA : HessianAssumptions P V) :
    ULA.wasserstein2Real (ULA.gibbsMeasure V)
      (invariantLaw P V hA.toPotentialAssumptions) ≤
      6 * P.step * Real.sqrt (P.condition * P.beta * P.dimension) :=
  bias_bound P V hA
example (P : Parameters) (V : E P.dimension → ℝ) (hA : HessianAssumptions P V)
    (μ : Measure (E P.dimension)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E P.dimension → E P.dimension) 2 μ) (n : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≤
      P.contraction ^ n * ULA.wasserstein2Real μ
        (invariantLaw P V hA.toPotentialAssumptions) +
      6 * P.step * Real.sqrt (P.condition * P.beta * P.dimension) :=
  convergence_bound P V hA μ hμ n
example (P : Parameters) (V : E P.dimension → ℝ) (hA : HessianAssumptions P V)
    (μ : Measure (E P.dimension)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E P.dimension → E P.dimension) 2 μ)
    (ε : ℝ) (hε : 0 < ε)
    (hstep : P.step = paperStep P.beta P.dimension ε) (n : ℕ)
    (hn : iterationPrefactor P.alpha P.beta P.dimension ε *
      Real.log (1 + 2 * Real.sqrt P.alpha * ULA.wasserstein2Real μ
        (invariantLaw P V hA.toPotentialAssumptions) / ε) ≤ (n : ℝ)) :
    Real.sqrt P.alpha *
      ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≤ ε :=
  accuracy_bound P V hA μ hμ ε hε hstep n hn
#print axioms WassersteinMixing.bias_bound
#print axioms WassersteinMixing.convergence_bound
#print axioms WassersteinMixing.accuracy_bound
"""


def compiled_source_audit():
    """Compile the final module and an independent original-assumption client."""
    build = subprocess.run(["lake", "build", "WassersteinMixing.Theorem"], cwd=ROOT,
                           text=True, capture_output=True)
    assert build.returncode == 0, "Final theorem build failed:\n" + build.stdout + build.stderr
    with tempfile.TemporaryDirectory(prefix="wasserstein-source-client-") as temp:
        client = Path(temp) / "SourceClient.lean"
        client.write_text(source_client())
        result = subprocess.run(["lake", "env", "lean", str(client)], cwd=ROOT,
                                text=True, capture_output=True)
    output = result.stdout + result.stderr
    log = Path(tempfile.gettempdir()) / "wasserstein-mixing-source-client.log"
    log.write_text(output)
    assert result.returncode == 0, "Original-assumption endpoint client failed:\n" + output
    found = dict(re.findall(r"'WassersteinMixing\.(\w+)' depends on axioms:\s*\[(.*?)\]", output, re.S))
    for _, name in SOURCE_ENDPOINTS.values():
        assert name in found, f"Missing compiled axiom audit: {name}"
        axioms = {item.strip() for item in found[name].split(",") if item.strip()}
        assert axioms <= ALLOWED_AXIOMS, f"Unapproved axioms in {name}: {axioms - ALLOWED_AXIOMS}"
    print("Compiled source-shaped clients and all three endpoint axiom audits passed.")
    print(f"Axiom audit log: {log}")


def verify(require_complete=False):
    path = ROOT / "WassersteinMixing/exposition/reference_audit.json"
    audit = json.loads(path.read_text())
    sources = {}
    for entry in audit["source"]["files"]:
        raw = (ROOT / entry["path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == entry["sha256"], "Manuscript changed"
        sources[entry["path"]] = re.sub(r"(?<!\\)%[^\n]*", "", raw.decode())
    expected_labels = Counter((name, match[1], text[:match.start()].count("\n") + 1)
                              for name, text in sources.items()
                              for match in re.finditer(r"\\label\{([^}]+)\}", text))
    recorded_labels = Counter((entry["source_file"], entry["label"], entry["source_line"])
                              for entry in audit["source_labels"])
    assert expected_labels == recorded_labels, "Missing or altered source labels"
    expected = Counter((name, match[1], match[2].strip(),
                        text[:match.start()].count("\n") + 1,
                        text[:match.end()].count("\n") + 1)
                       for name, text in sources.items() for match in ENVIRONMENT.finditer(text))
    recorded = Counter((entry["source_file"], entry["kind"], entry["source_statement_tex"],
                        entry["source_start"], entry["source_end"])
                       for entry in audit["results"])
    assert expected == recorded, "Missing, altered or stale source statement"
    assert Counter(entry["kind"] for entry in audit["results"]) == Counter(audit["counts"])
    assert {entry["printed_label"] for entry in audit["results"]} == {
        "Assumption 1.1", "Theorem 1", "Corollary 1.1", "Assumption 2.1"}
    parsed = {}
    files = sorted((ROOT / "WassersteinMixing").rglob("*.lean")) + [ROOT / "WassersteinMixing.lean"]
    for file in files:
        source = file.read_text()
        masked = "\n".join(HELPERS.mask_comments(source.splitlines()))
        assert not re.search(r"\b(?:sorry|admit|sorryAx)\b|^\s*axiom\b", masked, re.M), \
            f"Proof hole or added axiom: {file}"
        parsed[file.relative_to(ROOT).as_posix()] = declarations(source)

    def reference(record):
        file, name = record["file"], record["declaration"]
        assert file in parsed and name in parsed[file], f"Missing proof: {file}:{name}"

    for result in audit["results"]:
        for proof in result.get("proofs", []):
            reference(proof)
    labels = {item["label"] for item in audit["source_labels"]}
    for endpoint in audit["required_endpoints"]:
        assert endpoint["source_label"] in labels, "Invented source label"
        if endpoint.get("status") == "proved" and endpoint.get("file") and endpoint.get("declaration"):
            reference(endpoint)
    core = audit["checked_core"]
    assert core and len({item["id"] for item in core}) == len(core), "Empty or repeated checked core"
    for item in core:
        reference(item)
        assert item["status"] == "proved", "Unproved item in checked core"
    scope = audit["review_scope"]
    assert set(scope["results"]) == {item["id"] for item in core}, "Incorrect review scope"
    assert scope["complete"] is True, "Recorded proof scope is not completely checked"
    complete, pending, unfinished, missing = completion_state(audit)
    assert audit["formalization_complete"] == complete, "Misleading source completion flag"
    print(f"Checked {len(recorded)} exact source environments, {len(expected_labels)} labels, "
          f"{len(core)} core certificates and {len(files)} Lean modules; no proof holes.")
    print("Original paper coverage: " + ("COMPLETE" if complete else "INCOMPLETE"))
    if pending:
        print("Pending proof obligations: " + ", ".join(pending))
    if complete:
        compiled_source_audit()
    if require_complete and not complete:
        raise SystemExit("Full source theorem coverage is not certified: "
                         + ", ".join(pending + unfinished + missing))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true",
                        help="Require exact original-assumption endpoints and compiled axiom audits")
    verify(parser.parse_args().require_complete)
