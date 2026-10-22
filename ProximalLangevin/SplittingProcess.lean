import ProximalLangevin.SplittingL2Energy

/-!
# Integral-equation estimates for synchronous splitting

The drift increment and the reference future cross term are bounded directly
from the actual integral equation. The Brownian orthogonality needed by the
latter is proved for the constructed reference in SplittingOrthogonality.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace
namespace ProximalLangevin

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A coarse local smooth-drift defect bound uses only the smooth part's own
Lipschitz constant and the total reference drift moment. -/
theorem splitting_localDefect_bound (a g : H → H) {L Lg : ℝ≥0}
    (ha : LipschitzWith L a) (_hg : LipschitzWith Lg g)
    (Y B : ℝ → H) (_hY : Continuous Y) (h : ℝ) (hh : 0 ≤ h)
    (G N : ℝ) (hG : 0 ≤ G) (hN : 0 ≤ N)
    (hbound : ∀ t ∈ Icc 0 h, ‖g (Y t)‖ ≤ G)
    (hnoise : ∀ t ∈ Icc 0 h, ‖B t‖ ≤ N * Real.sqrt t)
    (heq : ∀ t ∈ Icc 0 h, Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t) :
    ‖ULA.localDefect a Y h‖ ≤ (L : ℝ) * h * (G * h + N * Real.sqrt h) := by
  unfold ULA.localDefect
  have hb (t : ℝ) (ht : t ∈ uIoc 0 h) :
      ‖a (Y t) - a (Y 0)‖ ≤ (L : ℝ) * (G * h + N * Real.sqrt h) := by
    rw [uIoc_of_le hh] at ht
    have hi := ULA.integral_equation_increment_bound g Y B h G N hh hbound hnoise heq
      ⟨ht.1.le, ht.2⟩
    have ha' : ‖a (Y t) - a (Y 0)‖ ≤ (L : ℝ) * ‖Y t - Y 0‖ := by
      simpa only [dist_eq_norm_sub] using ha.dist_le_mul (Y t) (Y 0)
    have hs := Real.sqrt_le_sqrt ht.2
    have hhbound : t * G + N * Real.sqrt t ≤ G * h + N * Real.sqrt h := by
      nlinarith [mul_le_mul_of_nonneg_right ht.2 hG, mul_le_mul_of_nonneg_left hs hN]
    exact ha'.trans (mul_le_mul_of_nonneg_left (hi.trans hhbound) L.coe_nonneg)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  calc
    _ ≤ (L : ℝ) * (G * h + N * Real.sqrt h) * h := by
      simpa only [sub_zero, abs_of_nonneg hh] using hi
    _ = _ := by ring

omit [CompleteSpace H] in
/-- Future-noise orthogonality turns the reference increment cross term into
a drift integral of order `h-t`, rather than a Brownian norm of order `sqrt(h-t)`. -/
theorem reference_future_inner_le (g : H → H) {L : ℝ≥0}
    (hg : LipschitzWith L g) (Y B : ℝ → H) (hY : Continuous Y)
    (h t : ℝ) (ht : 0 ≤ t) (hth : t ≤ h)
    (G K : ℝ) (hG : 0 ≤ G) (_hK : 0 ≤ K)
    (hbound : ∀ s ∈ Icc 0 h, ‖g (Y s)‖ ≤ G)
    (heq : ∀ s ∈ Icc 0 h, Y s - Y 0 = -(∫ r in 0..s, g (Y r)) + B s)
    (b : H) (hb : ‖b‖ ≤ K) (horth : ⟪b, B h - B t⟫ = 0) :
    ⟪Y t - Y h, b⟫ ≤ (h - t) * G * K := by
  have hh : 0 ≤ h := ht.trans hth
  have hint (a c : ℝ) : IntervalIntegrable (fun s => g (Y s)) volume a c :=
    (hg.continuous.comp hY).intervalIntegrable _ _
  have hsplit : (∫ s in 0..h, g (Y s)) =
      (∫ s in 0..t, g (Y s)) + ∫ s in t..h, g (Y s) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t h)).symm
  have heh := heq h ⟨hh, le_rfl⟩
  have het := heq t ⟨ht, hth⟩
  have hid : Y t - Y h = (∫ s in t..h, g (Y s)) - (B h - B t) := by
    rw [hsplit] at heh
    rw [eq_add_of_sub_eq het, eq_add_of_sub_eq heh]
    module
  rw [real_inner_comm] at horth
  rw [hid, inner_sub_left, horth, sub_zero]
  have hnorm : ‖∫ s in t..h, g (Y s)‖ ≤ G * (h - t) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := h)
      (C := G) (f := fun s => g (Y s)) (fun s hs => ?_)
    · simpa only [abs_of_nonneg (sub_nonneg.mpr hth)] using hi
    · rw [uIoc_of_le hth] at hs
      exact hbound s ⟨ht.trans hs.1.le, hs.2⟩
  calc
    _ ≤ ‖∫ s in t..h, g (Y s)‖ * ‖b‖ := real_inner_le_norm _ _
    _ ≤ (G * (h - t)) * K := mul_le_mul hnorm hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

end ProximalLangevin
