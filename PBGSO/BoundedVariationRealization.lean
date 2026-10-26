import PBGSO.PartitionFiniteVariation
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual L² drift primitives from bounded pathwise variation
The raw drift itself need not have an L² value at any time. Its genuine
primitive is in L² because the stopping-derived total variation is bounded.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace PBGSO.BoundedVariationRealization
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- A partial original drift primitive is controlled by its full variation. -/
theorem primitive_norm_le (T : ℝ≥0) (b : ℝ → E)
    (hb : IntervalIntegrable b volume 0 (T : ℝ)) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ‖∫ r in 0..t, b r‖ ≤ ∫ r in 0..(T : ℝ), ‖b r‖ := by
  apply (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
  apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (ae_of_all _ (fun _ => norm_nonneg _)) hb.norm

/-- Joint measurability of the original raw drift derives measurability
of every actual primitive, even when the drift is not spatially L². -/
theorem primitive_stronglyMeasurable (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    StronglyMeasurable (fun ω => ∫ r in 0..t, b r ω) := by
  simp only [intervalIntegral.integral_of_le ht.1]
  exact hb.integral_prod_left'

/-- Actual L² primitive from the original stopping-derived path variation. -/
theorem primitive_memLp (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (c : ℝ)
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ c)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    MemLp (fun ω => ∫ r in 0..t, b r ω) 2 Q := by
  apply MemLp.of_bound (primitive_stronglyMeasurable T b hb t ht).aestronglyMeasurable c
  filter_upwards [hpaths] with ω hω
  exact (primitive_norm_le T (fun r => b r ω) hω.1 t ht).trans hω.2

/-- The original path primitive as an actual L² variable on the horizon. -/
def primitiveLp (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (c : ℝ)
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ c) (t : ℝ) : Lp E 2 Q :=
  if ht : t ∈ Icc 0 (T : ℝ) then
    (primitive_memLp Q T b hb c hpaths t ht).toLp (fun ω => ∫ r in 0..t, b r ω)
  else 0

theorem primitiveLp_ae (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (c : ℝ)
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ c) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    primitiveLp Q T b hb c hpaths t =ᵐ[Q] (fun ω => ∫ r in 0..t, b r ω) := by
  simp only [primitiveLp, dite_eq_left ht]
  exact (primitive_memLp Q T b hb c hpaths t ht).coeFn_toLp

end PBGSO.BoundedVariationRealization
