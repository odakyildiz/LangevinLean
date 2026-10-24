#!/usr/bin/env python3
"""Compile one complete mathematical proof per main-page method, or check PDFs.

Run docs/build_site.py first. Only its declared docs/latex/**/FullProof.tex
exports are compiled. The individual module LaTeX files remain separate source
downloads. Paper manuscripts and private documents are never inputs.
Compilation needs XeLaTeX (default) or LuaLaTeX; --check needs only Python.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
LATEX = ROOT / "docs/latex"
PDF = ROOT / "docs/pdf"
MANIFEST = PDF / "manifest.json"
FLAGS = ["-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error",
         "-file-line-error", "-jobname=proof"]
RECIPE = {"passes": 3, "source_date_epoch": 1577836800, "flags": FLAGS}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def json_digest(value) -> str:
    return digest(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())


def builder_hash() -> str:
    return digest(Path(__file__).read_bytes())


def build_hash(engine_hash: str) -> str:
    return json_digest({"engine_sha256": engine_hash, "recipe": RECIPE,
                        "builder_sha256": builder_hash()})


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def exported_sources() -> dict[str, str]:
    """Check only the consolidated documents declared by the site generator."""
    coverage = json.loads((ROOT / "docs/coverage.json").read_text())
    expected = {name: value for name, value in coverage["outputs"].items()
                if name.startswith("docs/latex/") and name.endswith("/FullProof.tex")}
    if not expected:
        raise ValueError("No complete-method LaTeX exports in docs/coverage.json; "
                         "run docs/build_site.py")
    found = {relative(path) for path in LATEX.rglob("FullProof.tex")}
    if set(expected) != found:
        missing, extra = sorted(set(expected) - found), sorted(found - set(expected))
        raise ValueError(f"Complete-proof LaTeX inventory mismatch: missing {missing}; extra {extra}. "
                         "Run docs/build_site.py and remove stale exports")
    for name, expected_hash in expected.items():
        path = ROOT / name
        parts = PurePosixPath(name).parts
        if ".." in parts or path.is_symlink() or not path.resolve().is_relative_to(LATEX.resolve()):
            raise ValueError(f"Unsafe LaTeX export: {name}")
        if digest(path.read_bytes()) != expected_hash:
            raise ValueError(f"Stale generated source: {name}; run docs/build_site.py")
    return dict(sorted(expected.items()))


def pdf_path(source: str) -> str:
    return "docs/pdf/" + source.removeprefix("docs/latex/").removesuffix(".tex") + ".pdf"


def load_manifest() -> dict:
    if not MANIFEST.exists():
        return {}
    result = json.loads(MANIFEST.read_text())
    if not isinstance(result, dict) or result.get("format") != 1:
        raise ValueError("Unsupported docs/pdf/manifest.json; rebuild the PDFs")
    return result


def validate_pdf(path: Path, expected_hash: str) -> bool:
    if not path.is_file() or path.is_symlink():
        return False
    content = path.read_bytes()
    return (content.startswith(b"%PDF-") and b"%%EOF" in content[-1024:]
            and digest(content) == expected_hash)


def fresh(source: str, source_hash: str, record: dict, engine_hash: str, cache_hash: str) -> bool:
    return (isinstance(record, dict)
            and record.get("source_sha256") == source_hash
            and record.get("pdf") == pdf_path(source)
            and record.get("engine_sha256") == engine_hash
            and record.get("build_sha256") == cache_hash
            and isinstance(record.get("pages"), int) and record["pages"] > 0
            and validate_pdf(ROOT / pdf_path(source), record.get("pdf_sha256", "")))


def verify(sources: dict[str, str] | None = None, manifest: dict | None = None) -> None:
    sources = exported_sources() if sources is None else sources
    manifest = load_manifest() if manifest is None else manifest
    engine = manifest.get("engine", {})
    if (manifest.get("recipe") != RECIPE or not engine
            or manifest.get("engine_sha256") != json_digest(engine)
            or manifest.get("builder_sha256") != builder_hash()
            or manifest.get("build_sha256") != build_hash(manifest.get("engine_sha256", ""))):
        raise ValueError("Missing or stale PDF build manifest; run docs/build_pdfs.py")
    records = manifest.get("documents", {})
    if set(records) != set(sources):
        raise ValueError("PDF manifest does not cover the current complete-method LaTeX exports; rebuild PDFs")
    expected_pdfs = {pdf_path(source) for source in sources}
    actual_pdfs = {relative(path) for path in PDF.rglob("*.pdf")}
    if actual_pdfs != expected_pdfs:
        raise ValueError(f"PDF inventory mismatch: missing {sorted(expected_pdfs - actual_pdfs)}; "
                         f"extra {sorted(actual_pdfs - expected_pdfs)}")
    stale = [name for name, source_hash in sources.items()
             if not fresh(name, source_hash, records.get(name), manifest["engine_sha256"],
                          manifest["build_sha256"])]
    if stale:
        raise ValueError("Missing, modified or stale PDFs:\n" + "\n".join(stale))
    print(f"Checked {len(sources)} complete-method proof PDFs and their source/content hashes.")


def engine_details(name: str) -> tuple[str, dict, str]:
    executable = shutil.which(name)
    if not executable:
        raise ValueError(f"{name} is not installed. Install a TeX distribution, or use --check "
                         "to verify the committed PDFs without TeX")
    version = subprocess.check_output([executable, "--version"], text=True, timeout=20).strip()
    engine = {"name": name, "version": version,
              "binary_sha256": digest(Path(executable).resolve().read_bytes())}
    return executable, engine, json_digest(engine)


def diagnostic(output: str) -> str:
    lines = output.splitlines()
    for i, line in enumerate(lines):
        if ("Missing character:" in line or "FATAL ERROR" in line or "Error:" in line
                or line.startswith("!")
                or re.match(r"(?:\./)?proof\.tex:\d+:", line)):
            return "\n".join(lines[max(0, i - 1):i + 6])
    return "\n".join(lines[-12:])


def compile_one(source: str, source_hash: str, engine: str, engine_hash: str,
                cache_hash: str, timeout: int, scratch_root: Path,
                diagnostics_root: Path | None = None) -> dict:
    with tempfile.TemporaryDirectory(prefix="proof-", dir=scratch_root) as directory:
        scratch = Path(directory)
        content = (ROOT / source).read_bytes()
        if digest(content) != source_hash:
            raise ValueError(f"{source}: source changed during compilation; rebuild the site first")
        # Default PDF identifiers may include the random scratch directory. Use
        # a source-derived identifier and suppress optional LuaTeX path metadata.
        identifier = source_hash[:32]
        trailer = f"[<{identifier}><{identifier}>]"
        if Path(engine).name == "lualatex":
            prefix = "\\pdfvariable suppressoptionalinfo 3\\relax\n\\pdfvariable trailerid{" + trailer + "}\n"
        else:
            prefix = "\\AtBeginDocument{\\special{pdf:trailerid " + trailer + "}}\n"
        document = b"\\begin{document}"
        if content.count(document) != 1:
            raise ValueError(f"{source}: expected one standalone document")
        content = content.replace(document, prefix.encode() + document, 1)
        (scratch / "proof.tex").write_bytes(content)
        cache = scratch_root / "tex-cache"
        cache.mkdir(exist_ok=True)
        env = os.environ.copy()
        env.update({"SOURCE_DATE_EPOCH": str(RECIPE["source_date_epoch"]),
                    "FORCE_SOURCE_DATE": "1", "TZ": "UTC",
                    "TEXMFCACHE": str(cache), "TEXMFVAR": str(cache),
                    "openout_any": "p", "openin_any": "p"})
        # A copied, standalone export is the sole project input. All engine logs,
        # auxiliaries and intermediate PDFs remain in this temporary directory.
        for pass_number in range(1, RECIPE["passes"] + 1):
            try:
                run = subprocess.run([engine, *FLAGS, "proof.tex"], cwd=scratch,
                                     env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                     text=True, errors="replace", timeout=timeout)
            except subprocess.TimeoutExpired as error:
                raise ValueError(f"{source}: TeX pass {pass_number} exceeded {timeout}s") from error
            log = (scratch / "proof.log").read_text(errors="replace") if (scratch / "proof.log").exists() else ""
            if diagnostics_root is not None:
                saved_log = diagnostics_root / Path(source.removeprefix('docs/latex/')).with_suffix('.log')
                saved_log.parent.mkdir(parents=True, exist_ok=True)
                saved_log.write_text(log)
            if run.returncode or "Missing character:" in log or "Missing character:" in run.stdout:
                raise ValueError(f"{source}: TeX pass {pass_number} failed\n"
                                 + diagnostic(run.stdout + "\n" + log))
        temporary_pdf = scratch / "proof.pdf"
        if not temporary_pdf.is_file():
            raise ValueError(f"{source}: TeX completed without a PDF")
        content = temporary_pdf.read_bytes()
        content_hash = digest(content)
        if not validate_pdf(temporary_pdf, content_hash):
            raise ValueError(f"{source}: TeX produced an invalid PDF")
        info = subprocess.run(["pdfinfo", str(temporary_pdf)], stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, text=True, timeout=20)
        page_match = re.search(r"^Pages:\s+(\d+)", info.stdout, flags=re.M)
        if info.returncode or not page_match or int(page_match[1]) < 1:
            raise ValueError(f"{source}: PDF page count validation failed\n" + info.stdout[-1000:])
        destination = ROOT / pdf_path(source)
        if not destination.resolve().is_relative_to(PDF.resolve()):
            raise ValueError(f"Unsafe PDF output path: {destination}")
        destination.parent.mkdir(parents=True, exist_ok=True)
        # Replace only a completed, validated artifact; failed builds keep the
        # previous PDF so readers never receive a partial TeX output.
        with tempfile.NamedTemporaryFile(dir=destination.parent, prefix=".pdf-", delete=False) as saved:
            saved.write(content)
            temporary = Path(saved.name)
        temporary.replace(destination)
        return {"pdf": pdf_path(source), "source_sha256": source_hash,
                "pdf_sha256": content_hash, "engine_sha256": engine_hash,
                "build_sha256": cache_hash,
                "pages": int(page_match[1])}


def build(sources: dict[str, str], old_manifest: dict, args) -> None:
    executable, engine, engine_hash = engine_details(args.engine)
    if not shutil.which("pdfinfo"):
        raise ValueError("pdfinfo is required to validate compiled page counts; install Poppler")
    cache_hash = build_hash(engine_hash)
    old_records = old_manifest.get("documents", {})
    records = {name: old_records[name] for name in sources if name in old_records}
    pending_sources = [(name, source_hash) for name, source_hash in sources.items()
                       if not fresh(name, source_hash, records.get(name), engine_hash, cache_hash)]
    cached = len(sources) - len(pending_sources)
    print(f"Complete-method PDFs: {cached} current; compiling {len(pending_sources)} with "
          f"{args.engine}, at most {args.jobs} jobs.", flush=True)
    failures, completed = [], 0
    with tempfile.TemporaryDirectory(prefix="langevin-proof-pdfs-") as scratch_directory:
        scratch_root = Path(scratch_directory)
        if scratch_root.resolve().is_relative_to(ROOT):
            raise ValueError("TeX scratch space must be outside the repository; unset TMPDIR")
        iterator = iter(pending_sources)
        with ThreadPoolExecutor(max_workers=args.jobs) as workers:
            running = {}

            def submit_next():
                item = next(iterator, None)
                if item:
                    name, source_hash = item
                    future = workers.submit(compile_one, name, source_hash, executable,
                                            engine_hash, cache_hash, args.timeout, scratch_root,
                                            args.diagnostics_dir)
                    running[future] = name

            for _ in range(args.jobs):
                submit_next()
            while running:
                done, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in done:
                    name = running.pop(future)
                    try:
                        records[name] = future.result()
                        completed += 1
                        if completed % 20 == 0 or completed == len(pending_sources):
                            print(f"Compiled {completed}/{len(pending_sources)} proof PDFs.", flush=True)
                    except (OSError, ValueError) as error:
                        failures.append(str(error))
                    # Stop dispatching new work after a failure. Validated PDFs
                    # already built are recorded and reused on the next run.
                    if not failures:
                        submit_next()
    manifest = {"format": 1, "recipe": RECIPE, "engine": engine,
                "engine_sha256": engine_hash, "builder_sha256": builder_hash(),
                "build_sha256": cache_hash, "documents": dict(sorted(records.items()))}
    PDF.mkdir(parents=True, exist_ok=True)
    content = json.dumps(manifest, indent=2, ensure_ascii=False) + "\n"
    if not MANIFEST.exists() or MANIFEST.read_text() != content:
        MANIFEST.write_text(content)
    if failures:
        raise ValueError("\n\n".join(failures) + "\nFix the exported source and rebuild; "
                         "completed PDFs will be reused.")
    verify(sources, manifest)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Verify PDFs and hashes without invoking TeX")
    parser.add_argument("--engine", choices=("lualatex", "xelatex"), default="xelatex")
    parser.add_argument("--jobs", type=int, default=min(4, os.cpu_count() or 1), help="Parallel TeX jobs (1–4)")
    parser.add_argument("--timeout", type=int, default=180, help="Seconds allowed per TeX pass (default: 180)")
    parser.add_argument("--diagnostics-dir", type=Path,
                        help="Save final TeX logs outside the repository for layout review")
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4 or args.timeout < 1:
        parser.error("--jobs must be 1–4 and --timeout must be positive")
    if args.diagnostics_dir is not None:
        args.diagnostics_dir = args.diagnostics_dir.resolve()
        if args.diagnostics_dir.is_relative_to(ROOT):
            parser.error("--diagnostics-dir must be outside the repository")
    try:
        sources, manifest = exported_sources(), load_manifest()
        if args.check:
            verify(sources, manifest)
        else:
            build(sources, manifest, args)
    except (OSError, ValueError, KeyError, subprocess.SubprocessError) as error:
        print(f"PDF build: {error}", file=sys.stderr)
        raise SystemExit(1) from error


if __name__ == "__main__":
    main()
