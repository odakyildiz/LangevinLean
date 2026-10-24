#!/usr/bin/env bash
# Run the complete proof and exposition checks locally before publishing.
set -euo pipefail

script_directory="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$script_directory/.."

printf '\nBuilding all Lean libraries\n'
lake build

for audit in \
  UnadjustedLangevin/Check.lean \
  IPLA/Check.lean \
  ProximalLangevin/Check.lean \
  UnadjustedLangevin/LSI/Check.lean \
  IPLA/LSI/Check.lean \
  KineticLangevin/Check.lean \
  KIPLMC/Check.lean
do
  printf '\nAuditing %s\n' "$audit"
  lake env lean "$audit"
done

printf '\nChecking kinetic paper correspondence and reporting full-proof coverage\n'
python3 -B scripts/verify-kinetic-coverage.py --require-complete

for verifier in \
  UnadjustedLangevin/exposition/verify_document.py \
  UnadjustedLangevin/LSI/exposition/verify_document.py \
  IPLA/LSI/exposition/verify_document.py \
  ProximalLangevin/exposition/verify_document.py
do
  printf '\nChecking %s\n' "$verifier"
  python3 -B "$verifier"
done

printf '\nChecking the complete module proof atlas\n'
python3 -B docs/build_site.py --check
python3 -B docs/test_paper_prose.py
python3 -B docs/verify_exposition.py
python3 -B docs/verify_site.py

printf '\nChecking the isolated Mathlib-only IPLA standalone\n'
python3 -B IPLA/verify.py
printf '\nAll local checks passed.\n'
