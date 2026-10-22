import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Regrouping independent random variables

The helpers in this file convert binary independence into finite-family
independence and regroup three independent blocks.  They are used when separating
the past and future coordinates of a Brownian innovation in a splitting step.
-/

open MeasureTheory ProbabilityTheory

namespace ProximalLangevin

/-- Two independent random variables form an independent family indexed by `Bool`.
The probability assumption supplies the empty-family identity. -/
theorem iIndepFun_bool_of_indepFun {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → E} (h : IndepFun X Y μ) :
    iIndepFun (fun b : Bool ↦ if b then Y else X) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hsets
  by_cases hf : false ∈ s
  · by_cases ht : true ∈ s
    · have hs : s = {false, true} := by ext b; cases b <;> simp_all
      subst s
      have hi : (⋂ i ∈ ({false, true} : Finset Bool),
          (if i then Y else X) ⁻¹' sets i) = X ⁻¹' sets false ∩ Y ⁻¹' sets true := by
        ext ω
        simp [Bool.forall_bool]
      rw [hi]
      simpa using h.measure_inter_preimage_eq_mul _ _
        (hsets false (by simp)) (hsets true (by simp))
    · have hs : s = {false} := by ext b; cases b <;> simp_all
      subst s
      simp
  · by_cases ht : true ∈ s
    · have hs : s = {true} := by ext b; cases b <;> simp_all
      subst s
      simp
    · have hs : s = ∅ := by ext b; cases b <;> simp_all
      subst s
      simp

/-- Regroup a jointly independent triple from `X | (Y,Z)` into `(X,Y) | Z`.
Independence of `Y` and `Z` is essential; pairwise independence alone is insufficient. -/
theorem indepFun_prodMk_left_of_indepFun {Ω A B C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → A} {Y : Ω → B} {Z : Ω → C}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXYZ : IndepFun X (fun ω ↦ (Y ω, Z ω)) μ) (hYZ : IndepFun Y Z μ) :
    IndepFun (fun ω ↦ (X ω, Y ω)) Z μ := by
  have hXY : IndepFun X Y μ := by
    simpa only [Function.comp_def, id_eq] using
      hXYZ.comp measurable_id measurable_fst
  rw [indepFun_iff_map_prod_eq_prod_map_map (hX.prodMk hY).aemeasurable hZ.aemeasurable]
  apply (MeasurableEquiv.prodAssoc : (A × B) × C ≃ᵐ A × B × C).map_measurableEquiv_injective
  rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, Measure.prodAssoc_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change μ.map (fun ω ↦ (X ω, Y ω, Z ω)) = _
  rw [hXYZ.map_prod_eq_prod_map_map hX.aemeasurable (hY.prodMk hZ).aemeasurable,
    hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable]

end ProximalLangevin
