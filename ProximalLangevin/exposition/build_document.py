#!/usr/bin/env python3
"""Build the proximal algorithms page using the shared offline proof renderer."""
from __future__ import annotations

import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = HERE / "index.html"
SPEC = importlib.util.spec_from_file_location(
    "proximal_proof_page", ROOT / "UnadjustedLangevin/LSI/exposition/build_document.py")
RENDERER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(RENDERER)
RENDERER.HERE, RENDERER.LSI, RENDERER.OUT = HERE, HERE.parent, OUT
load_inputs = RENDERER.load_inputs
build = RENDERER.build

if __name__ == "__main__":
    build()
