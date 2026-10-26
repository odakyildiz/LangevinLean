import PBGSO.BoundedVariationRealization
import PBGSO.QuadraticMartingale

/-! # Actual stopped-state moments from pathwise drift variation
Initial L², actual noise L², and the original integral equation derive the
state's spatial L² value. No stopped-state moment or time-L¹(L²) drift is a premise.
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

/-- The original raw integral equation derives the actual state L² membership. -/
theorem state_memLp (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (c : ℝ)
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ c)
    (x₀ x m : Ω → E) (hx₀ : MemLp x₀ 2 Q) (hm : MemLp m 2 Q)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ))
    (heq : x =ᵐ[Q] fun ω => x₀ ω + (∫ r in 0..t, b r ω) + m ω) : MemLp x 2 Q :=
  (memLp_congr_ae heq).mpr ((hx₀.add (primitive_memLp Q T b hb c hpaths t ht)).add hm)

/-- A raw stopped state has the explicit moment bound from its original
variation cap and actual martingale noise, including unbounded P₂ initial data. -/
theorem state_moment_bound (T : ℝ≥0) (b : ℝ → Ω → E)
    (hb : StronglyMeasurable (Function.uncurry b)) (c : ℝ) (hc : 0 ≤ c)
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ c)
    (x₀ x m : Ω → E) (hx₀ : MemLp x₀ 2 Q) (hm : MemLp m 2 Q)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ))
    (heq : x =ᵐ[Q] fun ω => x₀ ω + (∫ r in 0..t, b r ω) + m ω) :
    (∫ ω, ‖x ω‖ ^ 2 ∂Q) ≤ 3 * (∫ ω, ‖x₀ ω‖ ^ 2 ∂Q) + 3 * c ^ 2 +
      3 * (∫ ω, ‖m ω‖ ^ 2 ∂Q) := by
  have hx := state_memLp Q T b hb c hpaths x₀ x m hx₀ hm t ht heq
  have hxi := (memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx
  have hzi := (memLp_two_iff_integrable_sq_norm hx₀.aestronglyMeasurable).mp hx₀
  have hmi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hbound : ∀ᵐ ω ∂Q, ‖x ω‖ ^ 2 ≤ 3 * ‖x₀ ω‖ ^ 2 + 3 * c ^ 2 + 3 * ‖m ω‖ ^ 2 := by
    filter_upwards [hpaths, heq] with ω hp he
    have hv := (primitive_norm_le T (fun r => b r ω) hp.1 t ht).trans hp.2
    have hn : ‖x ω‖ ≤ ‖x₀ ω‖ + c + ‖m ω‖ := by
      rw [he]
      exact (norm_add_le _ _).trans (by linarith [norm_add_le (x₀ ω) (∫ r in 0..t, b r ω)])
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖x₀ ω‖ + c + ‖m ω‖)).mpr hn
    nlinarith [sq_nonneg (‖x₀ ω‖ - c), sq_nonneg (‖x₀ ω‖ - ‖m ω‖), sq_nonneg (c - ‖m ω‖)]
  have hi := integral_mono_ae hxi
    (((hzi.const_mul 3).add (integrable_const (3 * c ^ 2))).add (hmi.const_mul 3)) hbound
  change (∫ ω, ‖x ω‖ ^ 2 ∂Q) ≤
    ∫ ω, (3 * ‖x₀ ω‖ ^ 2 + 3 * c ^ 2) + 3 * ‖m ω‖ ^ 2 ∂Q at hi
  have he₁ := integral_add ((hzi.const_mul 3).add (integrable_const (3 * c ^ 2))) (hmi.const_mul 3)
  have he₂ := integral_add (hzi.const_mul 3) (integrable_const (3 * c ^ 2))
  simp only [Pi.add_apply] at he₁ he₂
  rw [he₁, he₂] at hi
  simp only [integral_const_mul] at hi
  simpa using hi

end PBGSO.BoundedVariationRealization
