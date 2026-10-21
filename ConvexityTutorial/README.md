# Convexity in Lean: short proofs for optimization

This is the introductory learning track for this repository. The decision recorded
on 14 October 2026 is to keep the unadjusted Langevin development as an advanced
reference and learn Lean first through small convexity proofs. Mathematical maturity
is assumed; Lean syntax and proof conventions are introduced explicitly.

Open [the tutorial webpage](site/index.html). It pairs each mathematical proof
step with exact source lines, explains the syntax in those lines, and displays
the available assumptions and the current Lean goal. The early results concern
real-valued functions of one real variable so the proof language can be learned
before generalized spaces and analytic machinery.

## Source files

- `Definitions.lean` spells out convexity, strict convexity, a global minimizer,
  and a supporting line. It also connects the educational convexity predicates
  to Mathlib's definitions.
- `Basic.lean` proves elementary examples and closure properties of convex functions.
- `Minimizers.lean` proves convexity of the minimizer set and uniqueness under
  strict convexity.
- `Subgradients.lean` proves the zero-support optimality certificate and monotonicity
  of supporting slopes without requiring calculus.

All proofs use the actual definitions and Lean's kernel; there are no `sorry`
placeholders or additional axioms. The complete source files remain accessible
from the webpage. Step explanations concern the displayed proof, rather than
an alternative implementation.

## Build

From the repository root:

```sh
lake build ConvexityTutorial
lake env lean ConvexityTutorial/Check.lean
python3 ConvexityTutorial/capture_goals.py
python3 ConvexityTutorial/build_page.py
python3 ConvexityTutorial/verify_page.py
```

The tutorial webpage runs locally, including its KaTeX renderer and fonts.
The generator extracts source excerpts and the verifier checks exact source
correspondence, lesson coverage, links, and mathematical rendering. Genuine Lean
proof states are collected by `capture_goals.py` from checked temporary copies
of the source. The original proof files are not modified. Re-run the capture
after changing Lean source or step boundaries; the builder rejects stale states.
For an independent comparison against fresh Lean output, run the verifier with
`--recapture`.
