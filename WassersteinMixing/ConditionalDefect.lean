import WassersteinMixing.LocalError
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # Conditional means of actual time-integrated defects

Conditional expectation is the genuine Hilbert orthogonal projection. It
commutes with the Bochner integral, and isometric stationary evaluation
commutes with the same integral on the target observable space.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory

namespace WassersteinMixing
variable {Ω R E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (Q : Measure Ω) {m : MeasurableSpace Ω} (hm : m ≤ mΩ)

/-- The conditional mean of a true time-integrated defect is the evaluated
integrated source whenever the pointwise Markov means identify that source. -/
theorem conditionalDefect_eq_evaluation_integral
    (eval : R →ₗᵢ[ℝ] Lp E 2 Q) (increment : ℝ → Lp E 2 Q) (source : ℝ → R)
    (h : ℝ) (hh : 0 ≤ h) (hi : IntervalIntegrable increment volume 0 h)
    (hmean : ∀ t ∈ Set.Icc 0 h,
      (condExpL2 E ℝ hm (increment t) : Lp E 2 Q) = eval (source t)) :
    (condExpL2 E ℝ hm (stationaryLocalDefect increment h) : Lp E 2 Q) =
      eval (∫ t in 0..h, source t) := by
  letI : MeasurableSpace Ω := mΩ
  let : Fact (m ≤ mΩ) := ⟨hm⟩
  let projection : Lp E 2 Q →L[ℝ] Lp E 2 Q := (lpMeas E ℝ m 2 Q).starProjection
  change projection (∫ t in 0..h, increment t) = _
  rw [← projection.intervalIntegral_comp_comm hi,
    ← eval.intervalIntegral_comp_comm source]
  apply intervalIntegral.integral_congr
  intro t ht
  exact hmean t (by simpa only [Set.uIcc_of_le hh] using ht)

end WassersteinMixing
