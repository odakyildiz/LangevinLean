#!/usr/bin/env python3
"""Check source correspondence, formula rendering, links and offline assets."""
from __future__ import annotations

import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "proximal_page_verifier", ROOT / "UnadjustedLangevin/LSI/exposition/verify_document.py")
VERIFIER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFIER)

if __name__ == "__main__":
    VERIFIER.verify()
