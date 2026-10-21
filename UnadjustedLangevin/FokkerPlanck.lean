import UnadjustedLangevin.Generator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-! # The weak Fokker–Planck equation and the remaining stationarity bridge

The constant Gibbs curve satisfies the integrated weak Fokker–Planck equation
for every compactly supported `C²` test function. Normalization, all spatial
integrability, the finite second moment, and the generator identity are derived
from strong convexity and Lipschitz continuity of the gradient.

`WeakFokkerPlanckUnique` is deliberately an explicit, separate analytic
proposition. The final theorem in this file is conditional on that proposition
and on the actual diffusion laws satisfying the weak equation. Neither is
claimed to follow merely from the definition of an integral-equation solution.
Thus this file does not replace Gibbs invariance with an equivalent hidden
assumption, nor does it claim that generator integration alone proves it.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- Probability-valued weak solutions of the Langevin Fokker–Planck equation
on a finite interval. The moment and integrability conditions are included
explicitly, so all integrals in the equation have their ordinary meaning. -/
structure IsWeakFokkerPlanckSolution (U : H → ℝ) (ρ : ℝ → Measure H)
    (T : ℝ) : Prop where
  probability : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (ρ t)
  secondMoment : ∀ t ∈ Icc 0 T, Integrable (fun x : H ↦ ‖x‖ ^ 2) (ρ t)
  testIntegrable : ∀ (φ : H → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
    ∀ t ∈ Icc 0 T, Integrable φ (ρ t)
  testContinuous : ∀ (φ : H → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
    ContinuousOn (fun t ↦ ∫ x, φ x ∂ρ t) (Icc 0 T)
  generatorIntegrable : ∀ (φ : H → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
    ∀ t ∈ Icc 0 T, Integrable (langevinGenerator U φ) (ρ t)
  timeIntegrable : ∀ (φ : H → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
    IntervalIntegrable (fun s ↦ ∫ x, langevinGenerator U φ x ∂ρ s) volume 0 T
  equation : ∀ (φ : H → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
    ∀ t ∈ Icc 0 T,
      (∫ x, φ x ∂ρ t) = (∫ x, φ x ∂ρ 0) +
        ∫ s in 0..t, ∫ x, langevinGenerator U φ x ∂ρ s

/-- The constant Gibbs curve is a weak Fokker–Planck solution. Every condition
is proved from the potential assumptions; no stationary diffusion is assumed. -/
theorem constant_gibbs_isWeakFokkerPlanckSolution
    (U : H → ℝ) (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (T : ℝ) :
    IsWeakFokkerPlanckSolution U (fun _ ↦ gibbsMeasure U) T := by
  constructor
  · intro t ht
    exact isProbabilityMeasure_gibbsMeasure U m hm hdiff hsc
  · intro t ht
    exact integrable_norm_sq_gibbsMeasure U m hm hdiff hsc
  · intro φ hφ hc t ht
    exact integrable_gibbs_of_continuous_hasCompactSupport U hdiff φ hφ.continuous hc
  · intro φ hφ hc
    exact continuousOn_const
  · intro φ hφ hc t ht
    exact integrable_langevinGenerator_gibbsMeasure U L hdiff hLip φ hφ hc
  · intro φ hφ hc
    simp only [integral_langevinGenerator_gibbs_eq_zero U L hdiff hLip φ hφ hc]
    exact intervalIntegrable_const
  · intro φ hφ hc t ht
    simp only [integral_langevinGenerator_gibbs_eq_zero U L hdiff hLip φ hφ hc,
      intervalIntegral.integral_zero, add_zero]

/-- The still separate analytic uniqueness assertion for the weak equation.
This is not declared as an axiom or an instance and is not proved in this file. -/
def WeakFokkerPlanckUnique (U : H → ℝ) (T : ℝ) : Prop :=
  ∀ (ρ η : ℝ → Measure H),
    IsWeakFokkerPlanckSolution U ρ T → IsWeakFokkerPlanckSolution U η T →
    ρ 0 = η 0 → ∀ t ∈ Icc 0 T, ρ t = η t

/-- Conditional stationarity bridge. To apply this to a constructed Langevin
process, one must separately prove the weak equation for its laws (the Dynkin
or Itô step) and uniqueness of the stated weak Fokker–Planck class. Both premises
are visible here. The constant Gibbs solution itself is proved internally. -/
theorem gibbs_stationary_of_weakFokkerPlanckUniqueness
    (U : H → ℝ) (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) (T : ℝ)
    (hunique : WeakFokkerPlanckUnique U T)
    (ρ : ℝ → Measure H) (hρ : IsWeakFokkerPlanckSolution U ρ T)
    (hρ0 : ρ 0 = gibbsMeasure U) :
    ∀ t ∈ Icc 0 T, ρ t = gibbsMeasure U := by
  exact hunique ρ (fun _ ↦ gibbsMeasure U) hρ
    (constant_gibbs_isWeakFokkerPlanckSolution U m L hm hdiff hsc hLip T) hρ0

end ULA
