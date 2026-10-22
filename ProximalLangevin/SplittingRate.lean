import ProximalLangevin.SplittingOneStep

set_option linter.style.header false

/-!
# An explicit smoothing-uniform bound for the splitting forcing

This is scalar algebra applied to the derived coupling error, not an assumed
recurrence for algorithm laws. In the equal-step particle application the
uniform envelope gap is exactly at most `h*K²/2` in lifted coordinates.
-/

noncomputable section
namespace ProximalLangevin

/-- A finite coefficient for the squared splitting error floor. -/
def splittingRMSConstant (m L G noise K : ℝ) : ℝ :=
  4 * L ^ 2 / m ^ 2 * (G ^ 2 / m + noise ^ 2) + 2 / m * (G * K + K ^ 2)

/-- The coefficient is nonnegative under the actual moment-bound hypotheses. -/
theorem splittingRMSConstant_nonneg {m L G noise K : ℝ}
    (hm : 0 < m) (hG : 0 ≤ G) (hK : 0 ≤ K) :
    0 ≤ splittingRMSConstant m L G noise K := by
  unfold splittingRMSConstant
  positivity

/-- With a gap of at most `h*K²/2`, the derived one-step forcing is bounded
by `m*h²*C`, where `C` is independent of the smoothing parameter. -/
theorem splittingCouplingForcing_le {m h L G noise K delta : ℝ}
    (hm : 0 < m) (hh : 0 < h) (hsmall : h ≤ 1 / m)
    (_hG : 0 ≤ G) (_hnoise : 0 ≤ noise) (_hK : 0 ≤ K)
    (hdelta : delta ≤ h * K ^ 2 / 2) :
    splittingCouplingForcing m h L G noise K delta ≤
      m * h ^ 2 * splittingRMSConstant m L G noise K := by
  have hs : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  have hlocal : (G * h + noise * Real.sqrt h) ^ 2 ≤
      2 * G ^ 2 * h ^ 2 + 2 * noise ^ 2 * h := by
    nlinarith [sq_nonneg (G * h - noise * Real.sqrt h)]
  have hS : 0 ≤ G ^ 2 / m + noise ^ 2 := by positivity
  have hsmall' : h * m ≤ 1 := (le_div_iff₀ hm).mp hsmall
  have hGscale : G ^ 2 * h ^ 2 ≤ h * (G ^ 2 / m) := by
    apply (mul_le_mul_iff_of_pos_right hm).mp
    have hmul := mul_le_mul_of_nonneg_left hsmall' (sq_nonneg G)
    have hmulh := mul_le_mul_of_nonneg_left hmul hh.le
    have hcancel : (G ^ 2 / m) * m = G ^ 2 := div_mul_cancel₀ _ hm.ne'
    nlinarith
  have hlocal' : (G * h + noise * Real.sqrt h) ^ 2 ≤
      2 * h * (G ^ 2 / m + noise ^ 2) := by nlinarith
  have hweight : 0 ≤ 1 + (m * h)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlocal'
    (mul_nonneg hweight (mul_nonneg (sq_nonneg L) (sq_nonneg h)))
  have heq : (1 + (m * h)⁻¹) * (L ^ 2 * h ^ 2) *
      (2 * h * (G ^ 2 / m + noise ^ 2)) =
      2 * L ^ 2 * h ^ 2 * (h + 1 / m) * (G ^ 2 / m + noise ^ 2) := by
    field_simp
  rw [heq] at hscaled
  have htwice : h + 1 / m ≤ 2 / m := by
    convert add_le_add_right hsmall (1 / m) using 1 <;> ring
  have hfactor := mul_le_mul_of_nonneg_left htwice
    (show 0 ≤ 2 * L ^ 2 * h ^ 2 * (G ^ 2 / m + noise ^ 2) by positivity)
  have hdelta' := mul_le_mul_of_nonneg_left hdelta (show 0 ≤ 2 * h by positivity)
  have hC : m * h ^ 2 * splittingRMSConstant m L G noise K =
      4 * L ^ 2 * h ^ 2 / m * (G ^ 2 / m + noise ^ 2) +
        2 * h ^ 2 * G * K + 2 * h ^ 2 * K ^ 2 := by
    unfold splittingRMSConstant
    field_simp; ring
  have hfirst : (1 + (m * h)⁻¹) * (L * h * (G * h + noise * Real.sqrt h)) ^ 2 ≤
      4 * L ^ 2 * h ^ 2 / m * (G ^ 2 / m + noise ^ 2) := by
    calc
      _ = (1 + (m * h)⁻¹) * (L ^ 2 * h ^ 2) *
          (G * h + noise * Real.sqrt h) ^ 2 := by ring
      _ ≤ 2 * L ^ 2 * h ^ 2 * (h + 1 / m) * (G ^ 2 / m + noise ^ 2) := hscaled
      _ = 2 * L ^ 2 * h ^ 2 * (G ^ 2 / m + noise ^ 2) * (h + 1 / m) := by ring
      _ ≤ 2 * L ^ 2 * h ^ 2 * (G ^ 2 / m + noise ^ 2) * (2 / m) := hfactor
      _ = _ := by ring
  rw [hC]
  unfold splittingCouplingForcing
  linarith

end ProximalLangevin
