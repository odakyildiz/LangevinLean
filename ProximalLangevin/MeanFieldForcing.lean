import UnadjustedLangevin.LangevinUniqueness

set_option linter.style.header false

/-! # Integral perturbations with an additional continuous input

The additional input may be Brownian and need not be differentiable. Subtracting
it first leaves a differentiable integral error. The resulting Grönwall bound
is then applied to the actual empirical forcing and parameter-noise bounds.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace ProximalLangevin

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Actual integral equations with common input, an additional continuous input,
and a uniformly controlled reference-force defect satisfy this finite-horizon
bound. Neither a derivative of the input nor an error recurrence is assumed. -/
theorem integral_forcing_perturbation
    (F : H → H) (L : ℝ≥0) (hF : LipschitzWith L F)
    (x : H) (B A G X Y : ℝ → H)
    (hA : Continuous A) (hG : Continuous G) (hX : Continuous X) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T) (C a : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hAbound : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ a)
    (hdefect : ∀ t ∈ Icc 0 T, ‖F (Y t) - G t‖ ≤ C)
    (hXe : ∀ t ∈ Icc 0 T, X t - x = -(∫ s in 0..t, F (X s)) + B t + A t)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, G s) + B t) :
    ∀ t ∈ Icc 0 T, ‖X t - Y t‖ ≤ gronwallBound 0 (L : ℝ) (C + (L : ℝ) * a) T + a := by
  let D : ℝ → H := fun t => X t - Y t - A t
  let I : ℝ → H := fun t => -((∫ s in 0..t, F (X s)) - ∫ s in 0..t, G s)
  have hDI (t : ℝ) (ht : t ∈ Icc 0 T) : D t = I t := by
    have hx := hXe t ht
    have hy := hYe t ht
    rw [sub_eq_iff_eq_add] at hx hy
    dsimp [D, I]
    rw [hx, hy]
    abel
  have hcFX : Continuous (fun s => F (X s)) := hF.continuous.comp hX
  have hderiv : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt D (-(F (X t) - G t)) (Ici t) t := by
    intro t ht
    have hFX := intervalIntegral.integral_hasDerivAt_right
      (hcFX.intervalIntegrable 0 t) (hcFX.stronglyMeasurableAtFilter volume (𝓝 t)) hcFX.continuousAt
    have hGG := intervalIntegral.integral_hasDerivAt_right
      (hG.intervalIntegrable 0 t) (hG.stronglyMeasurableAtFilter volume (𝓝 t)) hG.continuousAt
    have hI : HasDerivAt I (-(F (X t) - G t)) t := (hFX.sub hGG).neg
    have hevent : D =ᶠ[𝓝[Ici t] t] I := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds ht.2)] with s hst hsT
      exact hDI s ⟨ht.1.trans hst, hsT.le⟩
    exact hI.hasDerivWithinAt.congr_of_eventuallyEq hevent (hDI t ⟨ht.1, ht.2.le⟩)
  have hD0 : D 0 = 0 := by
    simpa only [I, intervalIntegral.integral_same, sub_self, neg_zero] using hDI 0 ⟨le_rfl, hT⟩
  have htriangle (t : ℝ) : ‖X t - Y t‖ ≤ ‖D t‖ + ‖A t‖ := by
    simpa only [D, sub_add_cancel] using norm_add_le (X t - Y t - A t) (A t)
  have hb (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖-(F (X t) - G t)‖ ≤ (L : ℝ) * ‖D t‖ + (C + (L : ℝ) * a) := by
    have hnoise := hAbound t ⟨ht.1, ht.2.le⟩
    have herr := hdefect t ⟨ht.1, ht.2.le⟩
    have hstate : ‖X t - Y t‖ ≤ ‖D t‖ + a := by linarith [htriangle t]
    have hmul := mul_le_mul_of_nonneg_left hstate L.coe_nonneg
    have hh : ‖F (X t) - G t‖ ≤ ‖F (X t) - F (Y t)‖ + ‖F (Y t) - G t‖ := by
      simpa only [dist_eq_norm_sub] using dist_triangle (F (X t)) (F (Y t)) (G t)
    have hlip := hF.norm_sub_le (X t) (Y t)
    rw [norm_neg]
    linarith
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := D) (f' := fun t => -(F (X t) - G t)) (δ := 0)
    (K := (L : ℝ)) (ε := C + (L : ℝ) * a)
    ((hX.sub hY).sub hA).continuousOn hderiv (by simp [hD0]) hb
  intro t ht
  have hg := hgr t ht
  rw [sub_zero] at hg
  have hmono := gronwallBound_mono (δ := 0) (K := (L : ℝ))
    (ε := C + (L : ℝ) * a) (by norm_num) (by positivity) L.coe_nonneg ht.2
  have htA := hAbound t ht
  have htri := htriangle t
  linarith

/-- The zero-initial-error Grönwall response is homogeneous in its forcing. -/
theorem gronwallBound_zero_div (L C T r : ℝ) :
    gronwallBound 0 L (C / r) T = gronwallBound 0 L C T / r := by
  unfold gronwallBound
  split_ifs <;> ring

/-- The uniform forcing and input bounds of order `1/r` give the same scale
for the actual solution error, with an explicit coefficient independent of `r`. -/
theorem integral_forcing_perturbation_scaled
    (F : H → H) (L : ℝ≥0) (hF : LipschitzWith L F)
    (x : H) (B A G X Y : ℝ → H)
    (hA : Continuous A) (hG : Continuous G) (hX : Continuous X) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T) (C a r : ℝ) (hC : 0 ≤ C) (ha : 0 ≤ a) (hr : 0 < r)
    (hAbound : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ a / r)
    (hdefect : ∀ t ∈ Icc 0 T, ‖F (Y t) - G t‖ ≤ C / r)
    (hXe : ∀ t ∈ Icc 0 T, X t - x = -(∫ s in 0..t, F (X s)) + B t + A t)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, G s) + B t) :
    ∀ t ∈ Icc 0 T,
      ‖X t - Y t‖ ≤ (gronwallBound 0 (L : ℝ) (C + (L : ℝ) * a) T + a) / r := by
  have h := integral_forcing_perturbation F L hF x B A G X Y hA hG hX hY T hT
    (C / r) (a / r) (div_nonneg hC hr.le) (div_nonneg ha hr.le) hAbound hdefect hXe hYe
  have heq : C / r + (L : ℝ) * (a / r) = (C + (L : ℝ) * a) / r := by ring
  intro t ht
  have hh := h t ht
  rw [heq, gronwallBound_zero_div] at hh
  simpa only [← add_div] using hh

end ProximalLangevin
