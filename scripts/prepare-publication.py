#!/usr/bin/env python3
"""Export a committed review snapshot without the main-only paper sources.

This command creates files in a new directory. It never updates a Git branch,
pushes a commit, or publishes a website. Publication still requires the owner's
approval. Run the local checks before committing the snapshot to export.
"""
from __future__ import annotations

import argparse
from pathlib import Path, PurePosixPath
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_ROOTS = {"papers", ".git", ".lake", ".github"}


def allowed(name: str) -> bool:
    path = PurePosixPath(name)
    return bool(path.parts) and path.parts[0] not in EXCLUDED_ROOTS


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path, help="A new output directory")
    parser.add_argument("--ref", default="HEAD", help="Committed snapshot (default: HEAD)")
    args = parser.parse_args()
    destination = args.destination.resolve()
    if destination == ROOT or destination.is_relative_to(ROOT):
        parser.error("Use a new destination outside the source checkout")
    if destination.exists():
        parser.error("The destination must not exist; existing files are never replaced")
    revision = subprocess.check_output(
        ["git", "rev-parse", "--verify", args.ref + "^{commit}"], cwd=ROOT, text=True
    ).strip()
    with tempfile.TemporaryFile() as archive:
        subprocess.run(["git", "archive", revision], cwd=ROOT, stdout=archive, check=True)
        archive.seek(0)
        with tarfile.open(fileobj=archive, mode="r:") as snapshot:
            members = [member for member in snapshot.getmembers() if allowed(member.name)]
            # Only ordinary files/directories are expected in this static source
            # repository. Reject links so they cannot reintroduce paper sources.
            if any(not (member.isfile() or member.isdir()) for member in members):
                parser.error("The snapshot contains links or special files; inspect it manually")
            if any(PurePosixPath(member.name).is_absolute() or ".." in
                   PurePosixPath(member.name).parts for member in members):
                parser.error("The snapshot contains an unsafe path")
            destination.mkdir(parents=True)
            snapshot.extractall(destination, members=members)
    assert not (destination / "papers").exists()
    (destination / ".nojekyll").touch()
    (destination / "robots.txt").write_text("User-agent: *\nAllow: /\n")
    (destination / "PUBLISHING.md").write_text(
        "# GitHub Pages review snapshot\n\n"
        f"Source commit: `{revision}`.\n\n"
        "The main-only `papers/` directory is excluded. This export has not been "
        "published. Run the local proof and documentation checks before export, "
        "and obtain the repository owner's approval before updating `gh-pages`.\n"
    )
    print(f"Prepared {revision} in {destination}; papers/ excluded; nothing published.")


if __name__ == "__main__":
    main()
