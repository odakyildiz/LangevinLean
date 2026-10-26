import PBGSO.BoundedVariationState

/-! # Actual L² primitives under random square-integrable variation
A random L² budget is sufficient. No time-L¹(L²) drift, bounded state,
or final primitive membership is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace PBGSO.RandomVariationRealization
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

theorem primitive_memLp (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (B : Ω → ℝ) (hB : MemLp B 2 Q)
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ B ω)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    MemLp (fun ω => ∫ r in 0..t, b r ω) 2 Q := by
  apply hB.mono' (BoundedVariationRealization.primitive_stronglyMeasurable T b hb t ht).aestronglyMeasurable
  filter_upwards [hpaths] with ω hp
  exact (BoundedVariationRealization.primitive_norm_le T (fun r => b r ω) hp.1 t ht).trans hp.2

def primitiveLp (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (B : Ω → ℝ) (hB : MemLp B 2 Q)
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ B ω) (t : ℝ) : Lp E 2 Q :=
  if ht : t ∈ Icc 0 (T : ℝ) then
    (primitive_memLp Q T b hb B hB hpaths t ht).toLp (fun ω => ∫ r in 0..t, b r ω)
  else 0

theorem primitiveLp_ae (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (B : Ω → ℝ) (hB : MemLp B 2 Q)
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ B ω) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    primitiveLp Q T b hb B hB hpaths t =ᵐ[Q] (fun ω => ∫ r in 0..t, b r ω) := by
  simp only [primitiveLp, dite_eq_left ht]
  exact (primitive_memLp Q T b hb B hB hpaths t ht).coeFn_toLp

theorem state_memLp (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (B : Ω → ℝ) (hB : MemLp B 2 Q)
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ B ω)
    (x₀ x m : Ω → E) (hx₀ : MemLp x₀ 2 Q) (hm : MemLp m 2 Q)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ))
    (heq : x =ᵐ[Q] fun ω => x₀ ω + (∫ r in 0..t, b r ω) + m ω) : MemLp x 2 Q :=
  (memLp_congr_ae heq).mpr ((hx₀.add (primitive_memLp Q T b hb B hB hpaths t ht)).add hm)

end PBGSO.RandomVariationRealization
