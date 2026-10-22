#!/usr/bin/env python3
"""Build the IPLA entropy page with the shared offline proof-page renderer."""
from __future__ import annotations

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OUT = HERE / "proof.html"
SPEC = importlib.util.spec_from_file_location(
    "entropy_proof_page", ROOT / "UnadjustedLangevin/LSI/exposition/build_document.py")
RENDERER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RENDERER)
RENDERER.HERE, RENDERER.LSI, RENDERER.OUT = HERE, HERE.parent, OUT
load_inputs = RENDERER.load_inputs
build = RENDERER.build

if __name__ == "__main__":
    build()
