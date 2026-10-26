#!/usr/bin/env python3
"""Verify source correspondence and generated latent-diffusion statements.

Default checks are syntactic/documentary, not a proof of complete source coverage.
--lean additionally builds, checks displayed declarations and audits logical axioms.
--require-source-complete fails while source results retain unresolved bridges.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "docs"))
from build_latent_diffusion import source_inventory  # noqa: E402
from build_site import HELPERS  # noqa: E402


def require(condition, message):
    if not condition:
        raise ValueError(message)


def run(command, *, capture=False):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=capture)
    if result.returncode:
        if capture:
            print(result.stdout, end="")
            print(result.stderr, end="", file=sys.stderr)
        raise ValueError("Command failed: " + " ".join(map(str, command)))
    return result.stdout if capture else ""


def declaration_refs(value):
    if isinstance(value, dict):
        if "file" in value and "name" in value:
            yield value
        for child in value.values():
            yield from declaration_refs(child)
    elif isinstance(value, list):
        for child in value:
            yield from declaration_refs(child)


def tex_environments(path, assumptions=False):
    source = (ROOT / path).read_text()
    # Mask comments without changing character positions or line numbers.
    masked = re.sub(r"(?<!\\)%[^\n]*", lambda m: " " * len(m[0]), source)
    pattern = (r"\\begin\{restatable\}(?:\[[^\]]*\])?\{assumption_app\}"
               r".*?\\end\{restatable\}" if assumptions else
               r"\\begin\{(theorem|proposition|lemma|corollary)\}.*?\\end\{\1\}")
    for match in re.finditer(pattern, masked, re.S):
        yield (path, source.count("\n", 0, match.start()) + 1,
               source.count("\n", 0, match.end()) + 1,
               source[match.start():match.end()])


def verify(lean=False, require_complete=False):
    sources, parsed = source_inventory()
    for path, source in sources.items():
        masked = "\n".join(HELPERS.mask_comments(source.splitlines()))
        require(not re.search(r"\b(sorry|admit|sorryAx)\b", masked),
                "Incomplete proof or explicit sorry axiom: " + path)
        require(not re.search(r"^\s*(?:unsafe\s+)?axiom\s", masked, re.M),
                "Custom axiom declaration: " + path)

    inventory = json.loads((ROOT / "LatentDiffusion/exposition/source_inventory.json").read_text())
    require(set(inventory["modules"]) == set(sources), "Generated module inventory is stale")
    for path, source in sources.items():
        record = inventory["modules"][path]
        require(record["source_sha256"] == hashlib.sha256(source.encode()).hexdigest(),
                "Generated Lean hash is stale: " + path)
        require(set(record["declarations"]) == set(parsed[path]),
                "Generated declaration inventory is stale: " + path)
    for panel in inventory["panels"]:
        for path, name, *_ in panel["refs"]:
            require(path in parsed and name in parsed[path],
                    f"Missing statement-panel declaration: {path}:{name}")

    audit = json.loads((ROOT / "LatentDiffusion/exposition/reference_audit.json").read_text())
    require(set(audit["source"]["source_hashes"]) >= {
        "papers/Latent_diffusion/main_aistats.tex",
        "papers/Latent_diffusion/supp_aistats.tex",
        "papers/Latent_diffusion/includes/includes.tex"}, "Missing manuscript source hashes")
    for path, digest in audit["source"]["source_hashes"].items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest,
                "Manuscript hash changed: " + path)
    paper_paths = ["papers/Latent_diffusion/main_aistats.tex",
                   "papers/Latent_diffusion/supp_aistats.tex"]
    actual_results = {item for path in paper_paths for item in tex_environments(path)}
    actual_assumptions = {item for path in paper_paths for item in tex_environments(path, True)}
    require(len(actual_results) == 19, "Expected 19 source result environments")
    require(len(actual_assumptions) == 4, "Expected 4 displayed source assumptions")
    require(sum(r[0] == paper_paths[0] for r in actual_results) == 3 and
            audit["counts"]["main_results"] == 3 and
            audit["counts"]["supplementary_results"] == 16, "Incorrect main/supplement result split")
    require(audit["counts"]["numbered_results"] == 19 and
            audit["counts"]["displayed_source_assumptions"] == 4, "Incorrect audit counts")
    for key, actual in [("results", actual_results), ("assumptions", actual_assumptions)]:
        records = audit[key]
        recorded = {(r["source"], r["start_line"], r["end_line"], r["exact_tex"]) for r in records}
        require(len(records) == len(actual) and recorded == actual,
                "Source environment coverage/text differs for " + key)
        require(len({r["id"] for r in records}) == len(records), "Duplicate source IDs: " + key)
    mappings = list(declaration_refs(audit))
    for ref in mappings:
        path, name = ref["file"], ref["name"]
        require(path in parsed and name in parsed[path], f"Missing audit declaration: {path}:{name}")
        if "namespace" in ref:
            require(parsed[path][name]["lean_name"] == ref["namespace"] + "." + name,
                    f"Incorrect declaration namespace: {path}:{name}")

    # The generator independently checks complete headers, source snippets,
    # locally rendered mathematics, links, and the statement-only landing page.
    run([sys.executable, "docs/build_latent_diffusion.py", "--check"])
    run([sys.executable, "docs/test_latent_diffusion_landing.py"])

    if lean:
        run(["lake", "build", "LatentDiffusion"], capture=True)
        check = ROOT / "LatentDiffusion/Check.lean"
        if check.is_file():
            run(["lake", "env", "lean", str(check.relative_to(ROOT))], capture=True)
        run(["lake", "env", "lean", "LatentDiffusion/exposition/statement_checks.lean"], capture=True)
        names = sorted({decl["lean_name"] for module, decls in parsed.items() for decl in decls.values()
                        if decl["kind"] in ("theorem", "lemma") and not re.search(
                            r"\bprivate\s", sources[module].splitlines()[decl["start"] - 1])})
        # Audit all public theorems, including their private transitive dependencies.
        with tempfile.TemporaryDirectory(prefix="latent-axioms-") as directory:
            path = Path(directory) / "Audit.lean"
            path.write_text("import LatentDiffusion\n" +
                            "\n".join("#print axioms " + name for name in names) + "\n")
            output = run(["lake", "env", "lean", str(path)], capture=True)
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        for name in names:
            match = re.search(r"'" + re.escape(name) +
                              r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",
                              output, re.S)
            require(match is not None, "Missing logical axiom report: " + name)
            axioms = {a.strip() for a in (match[1] or "").split(",") if a.strip()}
            require(axioms <= allowed, f"Unexpected logical axioms for {name}: {axioms - allowed}")
        print(f"Lean checked {len(names)} theorem axiom reports; only standard logical axioms occur.")

    incomplete = [r["id"] for r in audit["results"]
                  if r.get("original_statement_fully_reconstructed") is not True]
    print(f"Checked {len(sources)} Lean source files, 19 result environments, 4 assumptions, "
          f"and {len(mappings)} declaration mappings.")
    print(f"Source reconstruction remains incomplete for {len(incomplete)} source results; "
          "this verification is not a source-completeness certificate.")
    if require_complete:
        open_bridges = [key for key, record in audit.get("formal_results", {}).items()
                        if record.get("unproved")]
        require(not incomplete and not open_bridges,
                "Source-complete mode failed: unresolved or corrected source claims: " +
                ", ".join(incomplete) + "; open analytic bridges: " + ", ".join(open_bridges))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", action="store_true", help="build and check Lean plus transitive axioms")
    parser.add_argument("--require-source-complete", action="store_true",
                        help="fail unless every source statement is recorded as fully reconstructed")
    args = parser.parse_args()
    try:
        verify(args.lean, args.require_source_complete)
    except (ValueError, KeyError, FileNotFoundError) as error:
        print("Latent-diffusion verification failed: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
