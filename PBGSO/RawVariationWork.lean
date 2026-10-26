import PBGSO.RawFiniteVariationEnergy

/-! # Original raw drift work on the time/sample product
The raw equation and actual martingale construct the domination required
for Fubini. No drift L² curve or final work-integrability claim is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace PBGSO.RawVariationWork
variable {Ω Z : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ℝ mΩ)

/-- The actual raw equation supplies a measurable square-integrable radius
for original drift work, from terminal noise L² and bounded path variation. -/
theorem exists_radius (T : ℝ≥0) (x b m : ℝ → Ω → Z)
    (h2x₀ : MemLp (x 0) 2 Q) (h2m : ∀ t, MemLp (m t) 2 Q)
    (hmart : Martingale m F Q) (c : ℝ) (hc : 0 ≤ c)
    (hxcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)))
    (hmcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => m t ω) (Icc 0 (T : ℝ)))
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ c ∧
      ∀ t ∈ Icc 0 (T : ℝ), x t ω = x 0 ω + (∫ r in 0..t, b r ω) + m t ω) :
    ∃ C : Ω → ℝ, Integrable (fun ω => C ω ^ 2) Q ∧
      ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)) ∧
        IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧ 0 ≤ C ω ∧
        (∀ t ∈ Icc 0 (T : ℝ), ‖x t ω‖ ≤ C ω) ∧
        (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ C ω := by
  obtain ⟨R, _, hR0, hR2, _, hRbound⟩ := DoobStrongL2.exists_continuous_radius Q F m
    hmart h2m (Icc 0 (T : ℝ)) ⟨0, le_rfl, T.coe_nonneg⟩ T (fun _ ht => ht.2) hmcont
  let C (ω : Ω) := ‖x 0 ω‖ + c + R ω
  have hC2 : MemLp C 2 Q := (h2x₀.norm.add (memLp_const c)).add hR2
  have hCi : Integrable (fun ω => C ω ^ 2) Q := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hC2.aestronglyMeasurable).mp hC2
  refine ⟨C, hCi, ?_⟩
  filter_upwards [hxcont, hpaths, hRbound] with ω hx hp hr
  have hC0 : 0 ≤ C ω := add_nonneg (add_nonneg (norm_nonneg _) hc) (hR0 ω)
  refine ⟨hx, hp.1, hC0, ?_, ?_⟩
  · intro t ht
    have hv := (BoundedVariationRealization.primitive_norm_le T (fun r => b r ω) hp.1 t ht).trans hp.2.1
    rw [hp.2.2 t ht]
    apply (norm_add_le _ _).trans
    dsimp [C]
    linarith [norm_add_le (x 0 ω) (∫ r in 0..t, b r ω), hr t ht]
  · exact hp.2.1.trans (by dsimp [C]; linarith [norm_nonneg (x 0 ω), hR0 ω])

/-- Absolute time/sample work integrability and actual Fubini are derived
from original raw localized equations, including non-L² drifts. -/
theorem integrable_and_swap (T : ℝ≥0) (B : Z →L[ℝ] Z →L[ℝ] ℝ) (x b m : ℝ → Ω → Z)
    (hxjoint : StronglyMeasurable (Function.uncurry x))
    (hbjoint : StronglyMeasurable (Function.uncurry b))
    (h2x₀ : MemLp (x 0) 2 Q) (h2m : ∀ t, MemLp (m t) 2 Q)
    (hmart : Martingale m F Q) (c : ℝ) (hc : 0 ≤ c)
    (hxcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)))
    (hmcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => m t ω) (Icc 0 (T : ℝ)))
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ c ∧
      ∀ t ∈ Icc 0 (T : ℝ), x t ω = x 0 ω + (∫ r in 0..t, b r ω) + m t ω) :
    Integrable (fun p : ℝ × Ω => B (x p.1 p.2) (b p.1 p.2))
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) ∧
      (∫ ω, (∫ r in 0..(T : ℝ), B (x r ω) (b r ω)) ∂Q) =
        ∫ r in 0..(T : ℝ), (∫ ω, B (x r ω) (b r ω) ∂Q) := by
  obtain ⟨C, hCi, hCp⟩ := exists_radius Q F T x b m h2x₀ h2m hmart c hc hxcont hmcont hpaths
  exact ⟨PathwiseDriftFubini.work_integrable Q T B x b C
    hxjoint.aestronglyMeasurable hbjoint.aestronglyMeasurable hCi hCp,
    PathwiseDriftFubini.integral_swap Q T B x b C
      hxjoint.aestronglyMeasurable hbjoint.aestronglyMeasurable hCi hCp⟩

end PBGSO.RawVariationWork
