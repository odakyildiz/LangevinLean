import WassersteinMixing.RealizedComparison
import WassersteinMixing.CurvatureAssumptions

set_option linter.style.header false

/-! # The source Wasserstein mixing results from the original assumptions

The only potential input is the manuscript's twice continuously differentiable
potential with its two Hessian bounds. The stationary diffusion, reversible
semigroup, Poisson corrector, synchronous comparison, Gaussian ULA invariant
law, and transport geometry are all constructed in the imported proofs.
-/

noncomputable section
open MeasureTheory

namespace WassersteinMixing

/-- Theorem 1: the exact source bias bound for the constructed invariant law of
ordinary independent-Gaussian ULA, from precisely the original Hessian bounds. -/
theorem bias_bound (P : Parameters) (V : E P.dimension → ℝ)
    (hA : HessianAssumptions P V) :
    ULA.wasserstein2Real (ULA.gibbsMeasure V)
      (invariantLaw P V hA.toPotentialAssumptions) ≤
        6 * P.step * Real.sqrt (P.condition * P.beta * P.dimension) := by
  exact bias_from_comparison hA.toPotentialAssumptions
    (actualULAComparison P V hA.toPotentialAssumptions)

/-- Corollary 1.1: the exact finite-time source estimate for the actual Gaussian
ULA laws, with only the source's finite-second-moment initial distribution. -/
theorem convergence_bound (P : Parameters) (V : E P.dimension → ℝ)
    (hA : HessianAssumptions P V) (μ : Measure (E P.dimension)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E P.dimension → E P.dimension) 2 μ) (n : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≤
      P.contraction ^ n * ULA.wasserstein2Real μ
        (invariantLaw P V hA.toPotentialAssumptions) +
          6 * P.step * Real.sqrt (P.condition * P.beta * P.dimension) := by
  exact convergence_from_comparison hA.toPotentialAssumptions
    (actualULAComparison P V hA.toPotentialAssumptions) μ hμ n

/-- Corollary 1.1: the literal scale-invariant accuracy and iteration complexity.
The positive dimension required by the displayed step formula is derived
internally from that formula and the algorithm's positive step. -/
theorem accuracy_bound (P : Parameters) (V : E P.dimension → ℝ)
    (hA : HessianAssumptions P V) (μ : Measure (E P.dimension)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : E P.dimension → E P.dimension) 2 μ) (ε : ℝ) (hε : 0 < ε)
    (hstep : P.step = paperStep P.beta P.dimension ε) (n : ℕ)
    (hn : iterationPrefactor P.alpha P.beta P.dimension ε *
      Real.log (1 + 2 * Real.sqrt P.alpha *
        ULA.wasserstein2Real μ (invariantLaw P V hA.toPotentialAssumptions) / ε) ≤ (n : ℝ)) :
    Real.sqrt P.alpha *
      ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≤ ε := by
  exact accuracy_from_comparison hA.toPotentialAssumptions
    (actualULAComparison P V hA.toPotentialAssumptions) μ hμ ε hε hstep n hn

end WassersteinMixing
