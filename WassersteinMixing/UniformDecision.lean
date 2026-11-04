import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod

/-! # Actual uniform acceptance and rejection

An independent uniform decision realizes the weighted accepted/rejected law
exactly. This connects the common random MALA path to its reversible kernel.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory Set
open scoped unitInterval ENNReal

namespace WassersteinMixing

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- A concrete acceptance decision, with an independent point of the unit interval. -/
def uniformDecision (a : A → ℝ) (f g : A → B) (p : A × I) : B :=
  if (p.2 : ℝ) ≤ a p.1 then f p.1 else g p.1

theorem uniformDecision_measurable (a : A → ℝ) (f g : A → B)
    (ha : Measurable a) (hf : Measurable f) (hg : Measurable g) :
    Measurable (uniformDecision a f g) := by
  apply Measurable.ite
    (measurableSet_le (measurable_subtype_coe.comp measurable_snd) (ha.comp measurable_fst))
    (hf.comp measurable_fst) (hg.comp measurable_fst)

/-- Uniform randomization has exactly the existing accepted/rejected weighted law. -/
theorem uniformDecision_law (μ : Measure A) [SFinite μ]
    (a : A → ℝ) (f g : A → B)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x) (ha1 : ∀ x, a x ≤ 1)
    (hf : Measurable f) (hg : Measurable g) :
    (μ.prod (volume : Measure I)).map (uniformDecision a f g) =
      (μ.withDensity (fun x ↦ ENNReal.ofReal (a x))).map f +
        (μ.withDensity (fun x ↦ ENNReal.ofReal (1 - a x))).map g := by
  ext s hs
  rw [Measure.map_apply (uniformDecision_measurable a f g ha hf hg) hs,
    Measure.prod_apply ((uniformDecision_measurable a f g ha hf hg) hs),
    Measure.add_apply, Measure.map_apply hf hs, Measure.map_apply hg hs,
    withDensity_apply _ (hf hs), withDensity_apply _ (hg hs),
    ← lintegral_indicator (hf hs), ← lintegral_indicator (hg hs),
    ← lintegral_add_left]
  · apply lintegral_congr
    intro x
    let ax : I := ⟨a x, ha0 x, ha1 x⟩
    by_cases hfx : f x ∈ s <;> by_cases hgx : g x ∈ s
    · have heq : Prod.mk x ⁻¹' uniformDecision a f g ⁻¹' s = univ := by
        ext u
        simp only [mem_preimage, uniformDecision]
        split <;> simp_all
      rw [heq]
      simp only [measure_univ, indicator_of_mem (show x ∈ f ⁻¹' s from hfx),
        indicator_of_mem (show x ∈ g ⁻¹' s from hgx)]
      rw [← ENNReal.ofReal_add (ha0 x) (sub_nonneg.mpr (ha1 x))]
      simp
    · have heq : Prod.mk x ⁻¹' uniformDecision a f g ⁻¹' s = Iic ax := by
        ext u
        change (if (u : ℝ) ≤ a x then f x else g x) ∈ s ↔ (u : ℝ) ≤ a x
        split <;> simp_all
      rw [heq, unitInterval.volume_Iic]
      simp [ax, hfx, hgx]
    · have heq : Prod.mk x ⁻¹' uniformDecision a f g ⁻¹' s = Ioi ax := by
        ext u
        change (if (u : ℝ) ≤ a x then f x else g x) ∈ s ↔ a x < (u : ℝ)
        split <;> simp_all [not_le]
      rw [heq, unitInterval.volume_Ioi]
      simp [ax, hfx, hgx]
    · have heq : Prod.mk x ⁻¹' uniformDecision a f g ⁻¹' s = ∅ := by
        ext u
        simp only [mem_preimage, uniformDecision]
        split <;> simp_all
      rw [heq]
      simp [hfx, hgx]
  · exact (ha.ennreal_ofReal.indicator (hf hs))

end WassersteinMixing
