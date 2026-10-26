import PBGSO.BrownianProcess

/-! # Increment estimates derived from the actual integral equations

On a finite horizon a continuous L² solution has bounded continuous drift.
The integral equation and Brownian-coordinate increment moments then give a
square-root increment modulus. It need not be postulated independently of
the constructed process. The drift radius is horizon dependent.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Continuous drift along an actual continuous solution is bounded on every
finite time interval, independently of a numerical mesh. -/
theorem exists_drift_radius (f : E → E) (hf : Continuous f)
    (Y : ℝ → E) (hY : Continuous Y) (T : ℝ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ t ∈ Icc 0 T, ‖f (Y t)‖ ≤ G := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).image
    (hf.comp hY)).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  exact (hC _ (mem_image_of_mem _ ht)).trans (le_max_left _ _)

/-- A segment increment follows by subtracting two actual integral equations. -/
theorem integral_segment_increment (f : E → E) (Y B : ℝ → E) (T a h G N : ℝ)
    (hcont : Continuous (fun t => f (Y t)))
    (ha : 0 ≤ a) (hh : 0 ≤ h) (haT : a + h ≤ T)
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 = (∫ s in 0..t, f (Y s)) + B t)
    (hG : ∀ t ∈ Icc 0 T, ‖f (Y t)‖ ≤ G)
    (hB : ‖B (a + h) - B a‖ ≤ N * Real.sqrt h) :
    ‖Y (a + h) - Y a‖ ≤ G * h + N * Real.sqrt h := by
  have hae : a ∈ Icc 0 T := ⟨ha, by linarith⟩
  have hah : a + h ∈ Icc 0 T := ⟨by linarith, haT⟩
  have hi : (∫ s in 0..a + h, f (Y s)) - (∫ s in 0..a, f (Y s)) =
      ∫ s in a..a + h, f (Y s) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable 0 a) (hcont.intervalIntegrable a (a + h))]
    abel
  have hy : Y (a + h) - Y a =
      (∫ s in a..a + h, f (Y s)) + (B (a + h) - B a) := by
    have he1 := heq (a + h) hah
    have he0 := heq a hae
    calc
      Y (a + h) - Y a = (Y (a + h) - Y 0) - (Y a - Y 0) := by abel
      _ = _ := by rw [he1, he0, ← hi]; abel
  have hint : ‖∫ s in a..a + h, f (Y s)‖ ≤ G * h := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := a + h) (C := G) (f := fun s => f (Y s)) (fun s hs => ?_)
    · simpa only [add_sub_cancel_left, abs_of_nonneg hh] using hb
    · rw [uIoc_of_le (by linarith : a ≤ a + h)] at hs
      exact hG s ⟨ha.trans hs.1.le, hs.2.trans haT⟩
  rw [hy]
  exact (norm_add_le _ _).trans (add_le_add hint hB)

/-- The useful square-root modulus for mesh widths at most one. -/
theorem integral_segment_sqrt_modulus (f : E → E) (Y B : ℝ → E)
    (T a h G N : ℝ) (hcont : Continuous (fun t => f (Y t)))
    (ha : 0 ≤ a) (hh : 0 ≤ h) (hh1 : h ≤ 1) (haT : a + h ≤ T) (hG0 : 0 ≤ G)
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 = (∫ s in 0..t, f (Y s)) + B t)
    (hG : ∀ t ∈ Icc 0 T, ‖f (Y t)‖ ≤ G)
    (hB : ‖B (a + h) - B a‖ ≤ N * Real.sqrt h) :
    ‖Y (a + h) - Y a‖ ≤ (G + N) * Real.sqrt h := by
  have hi := integral_segment_increment f Y B T a h G N hcont ha hh haT heq hG hB
  have hs : h ≤ Real.sqrt h := by
    have he := Real.sq_sqrt hh
    have hp := Real.sqrt_nonneg h
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs hG0]
end Banach

section Brownian
variable {Ω I Z : Type*} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (Q : Measure Ω)

/-- The input difference is exactly the increment over the shifted segment. -/
theorem samplerBrownianInput_segment (K : EuclideanSpace ℝ I →L[ℝ] Z)
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q)
    (a h : ℝ) :
    samplerBrownianInput Q K W hW 0 (a + h) - samplerBrownianInput Q K W hW 0 a =
      samplerBrownianInput Q K W hW a h := by
  change (K.compLpL 2 Q) (ULA.brownianLangevinNoise Q W hW 0 (a + h)) -
    (K.compLpL 2 Q) (ULA.brownianLangevinNoise Q W hW 0 a) =
      (K.compLpL 2 Q) (ULA.brownianLangevinNoise Q W hW a h)
  rw [← map_sub]
  congr 1
  simp only [ULA.brownianLangevinNoise, zero_add]
  module

end Brownian
end PBGSO
