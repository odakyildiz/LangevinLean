GRADIENT DESCENT: COMPLETE LEAN FORMALIZATION

From the Research directory:
  lake build GradientDescent
  lake env lean GradientDescent/Check.lean

Import GradientDescent to use the full library.
Main theorem: GradientDescent.gradient_descent_converges

Assumptions:
  H is a complete real inner-product space (a real Hilbert space).
  f : H -> Real is Frechet differentiable everywhere.
  StrongConvexOn Set.univ m f, with m > 0.
  LipschitzWith L (gradient f), with L : NNReal and L > 0.
  The constant step satisfies 0 < alpha < 2 / L.

Algorithm:
  x[0] = x0
  x[n+1] = x[n] - alpha * gradient f (x[n])

Conclusions:
  There is a unique global minimizer z; gradient f z = 0.
  x[n] tends to z in norm; f(x[n]) tends to f(z).
  rho = max(0, 1 - m * alpha * (2 - L * alpha)) lies in [0,1).
  0 <= f(x[n]) - f(z) <= rho^n * (f(x0) - f(z)).
  ||x[n] - z||^2 <= (2/m) * rho^n * (f(x0) - f(z)).
  If m <= L, rate_eq removes the maximum in rho.

The minimizer is constructed using an auxiliary small step and Banach's
fixed-point theorem. That construction places no extra restriction on alpha.
All assumptions and endpoint counterexamples are checked in Lean.

Files:
  StrongConvexity.lean   Tangent bounds, monotonicity, lower gap, PL bound.
  Step.lean              Auxiliary Euler-step contraction bounds.
  Minimizer.lean         Existence and uniqueness without assuming attainment.
  Smooth.lean            Quadratic upper bound from gradient Lipschitzness.
  Rates.lean             Iteration, geometric bounds, and limits.
  Convergence.lean       Actual descent, rate, and combined convergence theorem.
  Sharpness.lean         Checked quadratic counterexamples at alpha=0 and 2/L.
  Check.lean             Prints kernel axiom dependencies of major results.
  exposition/GradientDescent.tex   Editable standalone exposition source.
  exposition/GradientDescent.pdf   Step-by-step Lean code and matching mathematics.
  exposition/build_exposition.py  Extracts exact source blocks into the tutorial.
  exposition/source_manifest.json Source hashes and the included line ranges.

The 49-page walkthrough contains 113 exact code listings, with original Lean
source line numbers. Every proof block is followed by its matching inequalities,
derivations, and explanations of the goals and tactics. Each code/explanation
pair stays on the same page. The opening dictionary explains recurring Lean
syntax; the walkthrough covers every supporting proof and endpoint example.

Toolchain: Lean 4.35.0-rc3; mathlib v4.35.0-rc3 (see root lock files).
The axiom audit should list only propext, Classical.choice, and Quot.sound.
No proof placeholders or additional mathematical axioms are used.

To regenerate the PDF with a local TeX installation:
  python3 GradientDescent/exposition/build_exposition.py
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory=GradientDescent/exposition \
    GradientDescent/exposition/GradientDescent.tex
Run this command twice to resolve cross-references.
The annotations_*.json and *.texpart files supply the explanatory text.
Update their source ranges if Lean line numbers move before regenerating.
