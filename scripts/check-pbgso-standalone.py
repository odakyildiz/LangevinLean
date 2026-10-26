#!/usr/bin/env python3
"""Check final PBGSO endpoints, or export and check Mathlib-only single files.

Uses only the standard library, the installed pinned Lean toolchain, and
already prepared local Mathlib dependencies. It never fetches dependencies.
Reader-facing repository entry files state the complete theorem contracts and
prove them by applying the checked library. --output copies the complete
transitive local proof sources into one Mathlib-only file per entry. Each
export begins with an exact contract preview before its long proof appendix.
--output ... --check excludes this project's compiled modules from LEAN_PATH
and compiles each exported file in a fresh directory.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ENTRY = ROOT / "standalone" / "PBGSO"
ENTRIES = {"new-a": "NewA.lean", "new-b": "NewB.lean", "paper": "PaperTheorems.lean"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TOOLCHAIN = (ROOT / "lean-toolchain").read_text().strip()
MODULE = re.compile(r"[A-Za-z_][\w'.]*\Z")


def code_only(source: str) -> str:
    """Erase nested block and line comments, preserving line positions."""
    out, i, depth, string = [], 0, 0, False
    while i < len(source):
        pair = source[i:i + 2]
        if not string and pair == "/-":
            depth += 1; out.extend("  "); i += 2
        elif depth and pair == "-/":
            depth -= 1; out.extend("  "); i += 2
        elif depth:
            out.append("\n" if source[i] == "\n" else " "); i += 1
        elif not string and pair == "--":
            end = source.find("\n", i)
            if end < 0:
                out.extend(" " * (len(source) - i)); break
            out.extend(" " * (end - i)); i = end
        else:
            char = source[i]
            if char == '"':
                backslashes, j = 0, i - 1
                while j >= 0 and source[j] == "\\":
                    backslashes += 1; j -= 1
                if backslashes % 2 == 0:
                    string = not string
            out.append(char); i += 1
    if depth:
        raise ValueError("Unterminated Lean block comment")
    return "".join(out)


def imports(source: str) -> list[str]:
    result = []
    for line in code_only(source).splitlines():
        match = re.fullmatch(r"\s*(?:public\s+)?import\s+(.+?)\s*", line)
        if match:
            names = match[1].split()
            if not all(MODULE.fullmatch(name) for name in names):
                raise ValueError(f"Unsupported import syntax: {line}")
            result.extend(names)
    return result


def without_imports(source: str) -> str:
    lines = source.splitlines(keepends=True)
    erased = code_only(source).splitlines()
    return "".join(line for line, code in zip(lines, erased)
                   if not re.match(r"\s*(?:public\s+)?import\s+", code))


def validate_reader_entry(entry: Path) -> None:
    """A check-only list of imported names is not a readable theorem contract."""
    required = {
        "NewA.lean": {"theorem_new_a", "step_and_discretization_bound"},
        "NewB.lean": {"theorem_new_b", "step_and_discretization_bound"},
        "PaperTheorems.lean": {"theorem1_stationary_product", "theorem2_constant_diffusion",
                               "theorem2_linear_growth", "theorem3_particle_interaction",
                               "theorem4_parameter_constant", "theorem4_parameter_linear_growth"},
    }
    names = set(re.findall(r"^theorem\s+([\w.]+)\b", code_only(entry.read_text()), re.M))
    missing = required[entry.name] - names
    if missing:
        raise ValueError(f"Missing actual reader-facing theorem declarations in {entry.name}: {sorted(missing)}")


def local_closure(entry: Path) -> tuple[list[tuple[Path, str]], list[str]]:
    ordered, external, seen, active = [], [], set(), set()

    def visit(name: str) -> None:
        if name in active:
            raise ValueError(f"Import cycle at {name}")
        if name in seen:
            return
        seen.add(name)
        path = ROOT / (name.replace(".", "/") + ".lean")
        if not path.is_file():
            if name != "Mathlib" and not name.startswith("Mathlib."):
                raise ValueError(f"Non-Mathlib external dependency: {name}")
            external.append(name); return
        active.add(name)
        source = path.read_text()
        for dependency in imports(source):
            visit(dependency)
        active.remove(name)
        ordered.append((path, source))

    for name in imports(entry.read_text()):
        visit(name)
    return ordered, external


def export(entry: Path, destination: Path) -> dict:
    sources, external = local_closure(entry)
    entry_source = entry.read_text()
    contracts = without_imports(entry_source)
    contract_code = code_only(contracts)
    if not re.search(r"^theorem\s+", contract_code, re.M):
        raise ValueError(f"No inspectable theorem declaration in {entry.name}")
    if re.search(r"\b(?:sorry|admit|sorryAx|axiom)\b", contract_code):
        raise ValueError(f"Placeholder or new axiom in {entry.name}")
    chunks = ["\n".join("import " + name for name in external), f'''
/-!
# PBGSO standalone proof export: {entry.name}

Generated by scripts/check-pbgso-standalone.py from the current exact sources.
All local definitions, assumptions and proofs are copied below. Only Mathlib
is imported; the original LangevinLean checkout and its compiled modules are
not needed. No theorem is renamed or strengthened by this export.

Use Lean {TOOLCHAIN} and Mathlib v4.35.0-rc3 with its prepared dependencies:
  lake env lean {entry.name}

The reader-facing contracts are previewed FIRST, before the proof appendix.
Their actual Lean declarations are compiled after their dependencies at the
end of this file; the preview is copied exactly from the checked entry file.
#print axioms audits the complete kernel dependencies of those declarations.
The supplied analytic assumptions remain hypotheses; this file does not
assert that they hold for arbitrary models. Source module boundaries are
preserved by explicit sections.
-/
/-
================ READER-FACING THEOREM CONTRACTS ================
This preview is an exact copy of the repository entry (except imports).
Lean dependency order puts its compiled declarations after the proof appendix.

{contracts}
================ END READER-FACING CONTRACTS ====================
-/

/-! # Complete checked proof appendix -/
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 2000000
set_option linter.style.header false
set_option linter.unusedSectionVars false
''']
    hashes = {}
    for path, source in sources:
        relative = path.relative_to(ROOT).as_posix()
        body = without_imports(source)
        code = code_only(body)
        opens = len(re.findall(r"^\s*(?:noncomputable\s+)?section(?:\s+[\w.]+)?\s*$", code, re.M))
        namespaces = len(re.findall(r"^\s*namespace\s+[\w.]+\s*$", code, re.M))
        ends = len(re.findall(r"^\s*end(?:\s+[\w.]+)?\s*$", code, re.M))
        pending = opens + namespaces - ends
        if pending < 0:
            raise ValueError(f"Scope count failure in {relative}")
        if re.search(r"\b(?:sorry|admit|sorryAx|axiom)\b", code):
            raise ValueError(f"Placeholder or new axiom in {relative}")
        chunks.extend([f"\n/-! ## Included source: {relative} -/\nsection\n", body,
                       "\n" + "end\n" * pending + "end\n"])
        hashes[relative] = hashlib.sha256(source.encode()).hexdigest()
    chunks.extend(["\n/-! # Compiled reader-facing theorem declarations -/\n", contracts])
    text = "\n".join(chunks)
    if any(name != "Mathlib" and not name.startswith("Mathlib.") for name in imports(text)):
        raise ValueError("Export retained a local import")
    destination.write_text(text)
    return {"file": destination.name, "sha256": hashlib.sha256(text.encode()).hexdigest(),
            "local_source_count": len(sources), "source_sha256": hashes,
            "external_imports": external, "endpoint_entry": entry.relative_to(ROOT).as_posix(),
            "endpoint_sha256": hashlib.sha256(entry_source.encode()).hexdigest(),
            "reader_contract_preview": True}


def lake_command() -> list[str]:
    elan = shutil.which("elan")
    if elan:
        return [elan, "run", TOOLCHAIN, "lake"]
    lake = shutil.which("lake")
    if not lake:
        raise ValueError("Install the pinned Lean toolchain before running this offline check")
    return [lake]


def lean_environment(isolated: bool) -> tuple[str, dict]:
    # Preflight local packages. No update, download, cache-get or package-install
    # command is invoked, and `elan run` omits --install, so no toolchain is downloaded.
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = ROOT / manifest.get("packagesDir", ".lake/packages")
    absent = [p["name"] for p in manifest["packages"] if not (packages / p["name"]).is_dir()]
    if absent:
        raise ValueError("Prepared offline dependencies missing: " + ", ".join(absent))
    lake = lake_command()
    lean_path = subprocess.check_output(lake + ["env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    prefix = subprocess.check_output(lake + ["env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip()
    lean = str(Path(prefix) / "bin" / "lean")
    env = os.environ.copy()
    local = (ROOT / ".lake/build/lib/lean").resolve()
    paths = []
    for value in lean_path.split(os.pathsep):
        path = Path(value)
        resolved = (ROOT / path).resolve() if not path.is_absolute() else path.resolve()
        if isolated and (resolved == local or resolved == ROOT):
            continue
        paths.append(str(resolved))
    env["LEAN_PATH"] = os.pathsep.join(paths)
    if isolated and str(local) in env["LEAN_PATH"].split(os.pathsep):
        raise ValueError("Original project oleans remain in the isolated path")
    return lean, env


def check(entry: Path, *, isolated: bool, log: Path | None) -> dict:
    lean, env = lean_environment(isolated)
    expected = re.findall(r"^#print axioms ([\w.]+)\s*$", code_only(entry.read_text()), re.M)
    print(f"Checking {'isolated Mathlib-only export' if isolated else 'repository endpoint'}: {entry.name}", flush=True)
    with tempfile.TemporaryDirectory(prefix="pbgso-standalone-") as temporary:
        target = Path(temporary) / entry.name if isolated else entry
        if isolated:
            shutil.copyfile(entry, target)
        completed = subprocess.run([lean, str(target)], cwd=temporary if isolated else ROOT,
                                   env=env, text=True, capture_output=True)
        output = (completed.stdout + completed.stderr).replace(str(target), entry.name)
    if log:
        log.write_text(output)
    records = re.findall(r"'([\w.]+)' depends on axioms: \[([^\]]*)\]", output)
    audits = {name: [x.strip() for x in group.split(",") if x.strip()] for name, group in records}
    for name in re.findall(r"'([\w.]+)' does not depend on any axioms", output):
        audits[name] = []
    missing = [name for name in expected if name not in audits]
    unexpected = sorted({a for values in audits.values() for a in values} - ALLOWED_AXIOMS)
    report = {"exit_code": completed.returncode, "isolated_from_project_oleans": isolated,
              "axiom_audit": audits, "missing_axiom_audits": missing,
              "unexpected_axioms": unexpected, "lean_toolchain": TOOLCHAIN}
    if completed.returncode or missing or unexpected:
        print(output[-20000:], file=sys.stderr)
        raise ValueError(f"Check failed for {entry.name}: exit={completed.returncode}, missing={missing}, axioms={unexpected}")
    print(f"PASS {entry.name}: {len(expected)} endpoint axiom audits; only standard logical axioms", flush=True)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--endpoint", choices=["all", *ENTRIES], default="all")
    parser.add_argument("--output", type=Path, help="New/empty directory for complete Mathlib-only exports")
    parser.add_argument("--check", action="store_true", help="Compile selected entry files or isolated exports and audit axioms")
    args = parser.parse_args()
    selected = list(ENTRIES) if args.endpoint == "all" else [args.endpoint]
    if not args.output and not args.check:
        parser.error("Choose --check for repository checks, --output for export, or both")
    try:
        output = args.output.resolve() if args.output else None
        if output:
            if output == ROOT or output.is_relative_to(ROOT / "PBGSO"):
                raise ValueError("Export outside PBGSO/; use a new directory such as /tmp/pbgso-standalone")
            if output.exists() and any(output.iterdir()):
                raise ValueError("Output must be new or empty; existing exports are never overwritten")
            output.mkdir(parents=True, exist_ok=True)
        report = {"schema_version": 1, "lean_toolchain": TOOLCHAIN, "endpoints": {}}
        for key in selected:
            entry = ENTRY / ENTRIES[key]
            validate_reader_entry(entry)
            if output:
                target = output / entry.name
                item = export(entry, target)
                print(f"Exported {target}: {item['local_source_count']} local modules", flush=True)
            else:
                target, item = entry, {"endpoint_entry": entry.relative_to(ROOT).as_posix()}
            if args.check:
                item["verification"] = check(target, isolated=bool(output), log=(output / (entry.stem + ".check.txt")) if output else None)
            report["endpoints"][key] = item
            if output:
                (output / "manifest.json").write_text(json.dumps(report, indent=2) + "\n")
        if output:
            (output / "lean-toolchain").write_text(TOOLCHAIN + "\n")
            (output / "README.md").write_text(
                "# PBGSO Mathlib-only standalone exports\n\n"
                "Each .lean file begins with an exact, human-readable preview of its assumptions and theorem statements, "
                "followed by every local definition and proof in its endpoint's transitive closure. "
                "The same actual theorem declarations are compiled after the proof appendix, as required by Lean dependency order. "
                "Only Mathlib is imported. Copy a file into a project with the pinned Lean/Mathlib v4.35.0-rc3 and run "
                "`lake env lean NewA.lean` (or NewB.lean / PaperTheorems.lean). No original checkout or local PBGSO oleans are needed.\n\n"
                "manifest.json records exact source hashes and any isolated compilation/axiom audit; .check.txt files contain full diagnostics. "
                "An exported file is not claimed checked unless its verification exit_code is zero. Analytic assumptions remain in the original theorem types.\n")
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"PBGSO standalone check: {error}\n")


if __name__ == "__main__":
    main()
