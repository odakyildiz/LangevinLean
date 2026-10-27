# Average-smoothness sampling proofs and source audit

The [standard proof overview](index.html) pairs each main mathematical statement with its exact Lean header and links the complete module proofs. The source is the repository's `Arxiv_version_May_26.tex`, *Improved Guarantees for Langevin Monte Carlo with Average Smoothness*. Its exact hash, all 12 numbered statements and all 78 labels appear in [`reference_audit.json`](reference_audit.json).

The main review scope consists of Theorem 1 (average-smoothness LMC), Proposition 1 (decreasing steps), Theorem 2 with source label `th:3` (Laplacian-smooth LMC), and Theorem 3 together with Proposition 3 (SGLD). Their laws are the actual independent Gaussian and finite-index recursions. Their analytic estimates, moments and recurrences are derived from the source hypotheses.

The Laplacian argument constructs a weighted Dynkin identity through actual Gaussian Euler steps and their uniform $L^2$ limit. Compact $C^2$ score approximations keep the potential's source $C^3$ regularity. Stationarity transfers their approximation errors without a dimension loss, and bounded radial clipping allows every square-integrable initial coupling error.

The source inventory also records auxiliary statements whose full standalone generality is outside the main review scope. In particular, the broader Gaussian perturbation and two pathwise comparison inequalities remain outside this scope rather than being labelled proved using stronger main-theorem hypotheses.

Use `python3 scripts/verify-average-lmc-coverage.py --require-resolved` for the main sampling theorem review gate. Literal full-paper coverage is reported separately and is not claimed. Review is on `main` only; this work does not publish or update `gh-pages`.
