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
  KIPLMC/Check.lean \
  PBGSO/Check.lean \
  LatentDiffusion/Check.lean \
  AverageLMC/Check.lean
do
  printf '\nAuditing %s\n' "$audit"
  lake env lean "$audit"
done

printf '\nChecking kinetic paper correspondence and reporting full-proof coverage\n'
python3 -B scripts/verify-kinetic-coverage.py --require-complete

printf '\nChecking PBGSO theorem statements, assumptions and source correspondence\n'
python3 -B scripts/verify-pbgso.py --require-complete
python3 -B docs/test_pbgso_landing.py
python3 -B docs/test_pbgso_headers.py
python3 -B scripts/check-pbgso-standalone.py --check

for verifier in \
  UnadjustedLangevin/exposition/verify_document.py \
  UnadjustedLangevin/LSI/exposition/verify_document.py \
  IPLA/LSI/exposition/verify_document.py \
  ProximalLangevin/exposition/verify_document.py
do
  printf '\nChecking %s\n' "$verifier"
  python3 -B "$verifier"
done

printf '\nChecking latent-diffusion statements and source fidelity\n'
python3 -B scripts/verify-latent-diffusion.py
lake env lean LatentDiffusion/exposition/statement_checks.lean

printf '\nChecking average-smoothness main sampling theorems\n'
python3 -B scripts/verify-average-lmc-coverage.py --require-resolved

printf '\nChecking the complete module proof atlas\n'
python3 -B docs/build_site.py --check
python3 -B docs/test_paper_prose.py
python3 -B docs/test_math_notation.py
python3 -B docs/test_atlas_headers.py
python3 -B docs/test_extra_assumptions.py
python3 -B docs/verify_exposition.py
python3 -B docs/verify_report_citations.py --self-test
python3 -B docs/verify_report_citations.py
python3 -B docs/verify_site.py
python3 -B docs/verify_math_notation.py

printf '\nChecking the isolated Mathlib-only IPLA standalone\n'
python3 -B IPLA/verify.py
printf '\nAll local checks passed.\n'
