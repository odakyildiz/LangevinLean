import AverageLMC.Assumptions

set_option linter.style.header false

/-!
# Exact normalization of the coordinate smoothness constants

The SGLD theorem defines its barred coordinate constant from the average
potential. These identities relate that literal supremum to the constant of
the full finite sum, rather than introducing a separate chosen bound.
-/

noncomputable section
open scoped NNReal BigOperators

namespace AverageLMC

theorem gradient_const_mul_potential {p : ℕ} (f : State p → ℝ)
    (hf : Differentiable ℝ f) (c : ℝ) (x : State p) :
    gradient (fun y ↦ c * f y) x = c • gradient f x := by
  simp only [gradient, fderiv_const_mul (hf x), map_smul]

theorem coordinateTaylorQuotient_const_mul {p : ℕ} (f : State p → ℝ)
    (hf : Differentiable ℝ f) (c : ℝ) (j : Fin p) (x : State p) (a : ℝ) :
    coordinateTaylorQuotient (fun y ↦ c * f y) j x a =
      c * coordinateTaylorQuotient f j x a := by
  unfold coordinateTaylorQuotient
  rw [gradient_const_mul_potential f hf c x]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

theorem coordinateTaylorQuotients_const_mul {p : ℕ} (f : State p → ℝ)
    (hf : Differentiable ℝ f) (c : ℝ) (j : Fin p) :
    coordinateTaylorQuotients (fun y ↦ c * f y) j =
      (fun q ↦ c * q) '' coordinateTaylorQuotients f j := by
  ext q
  constructor
  · rintro ⟨x, a, ha, rfl⟩
    exact ⟨coordinateTaylorQuotient f j x a, ⟨x, a, ha, rfl⟩,
      (coordinateTaylorQuotient_const_mul f hf c j x a).symm⟩
  · rintro ⟨q, ⟨x, a, ha, rfl⟩, rfl⟩
    exact ⟨x, a, ha, (coordinateTaylorQuotient_const_mul f hf c j x a).symm⟩

/-- Nonnegative rescaling commutes with each exact coordinate supremum. -/
theorem coordinateSmoothness_const_mul {p : ℕ} (f : State p → ℝ)
    (hf : Differentiable ℝ f) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (c : ℝ) (hc : 0 ≤ c) (j : Fin p) :
    coordinateSmoothness (fun y ↦ c * f y) j = c * coordinateSmoothness f j := by
  unfold coordinateSmoothness
  rw [coordinateTaylorQuotients_const_mul f hf c j]
  exact ((isLUB_csSup (coordinateTaylorQuotients_nonempty f j)
    (coordinateTaylorQuotients_bddAbove f M hf hLip j)).mul_left hc).csSup_eq
      ((coordinateTaylorQuotients_nonempty f j).image _)

/-- The literal average coordinate constant is homogeneous in the potential. -/
theorem averageSmoothness_const_mul {p : ℕ} (f : State p → ℝ)
    (hf : Differentiable ℝ f) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (c : ℝ) (hc : 0 ≤ c) :
    averageSmoothness (fun y ↦ c * f y) = c * averageSmoothness f := by
  unfold averageSmoothness
  simp_rw [coordinateSmoothness_const_mul f hf M hLip c hc]
  rw [← Finset.mul_sum]
  ring

/-- Exactly the barred smoothness constant in the manuscript's SGLD theorem. -/
theorem averageSmoothness_div_nat {p : ℕ} (f : State p → ℝ)
    (hf : Differentiable ℝ f) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (n : ℕ) :
    averageSmoothness (fun x ↦ f x / (n : ℝ)) = averageSmoothness f / n := by
  simpa only [div_eq_mul_inv, mul_comm] using
    averageSmoothness_const_mul f hf M hLip (n : ℝ)⁻¹ (by positivity)

end AverageLMC
