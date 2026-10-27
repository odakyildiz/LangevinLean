import AverageLMC.Recurrence

set_option linter.style.header false

/-! # Scalar arithmetic of the fixed-point-control-variate SGLD theorem

Here `m` is the full potential's curvature and `R = n M_rms`. The final
algorithm theorem derives this recurrence from the actual Gaussian-index law.
-/

namespace AverageLMC

/-- The paper's step restriction bounds the dimensionless step by one third. -/
theorem sgld_dimensionless_step {m R h : ℝ} (hm : 0 < m) (hh : 0 ≤ h)
    (hR : m ^ 2 ≤ R ^ 2) (hstep : 3 * R ^ 2 * h ≤ m) : m * h ≤ 1 / 3 := by
  have hr := mul_le_mul_of_nonneg_right hR hh
  have hmul : m * (3 * m * h - 1) ≤ 0 := by nlinarith
  by_contra hn
  have hx : 0 < 3 * m * h - 1 := by linarith
  have hpos := mul_pos hm hx
  linarith

/-- Exact comparison of the SGLD contraction with the reciprocal rate. -/
theorem sgld_contraction_le {m R h : ℝ} (hm : 0 < m) (hh : 0 ≤ h)
    (hR : m ^ 2 ≤ R ^ 2) (hstep : 3 * R ^ 2 * h ≤ m) :
    (1 - m * h) / (1 + m * h) + 2 * R ^ 2 * h ^ 2 ≤ 1 / (1 + m * h) := by
  have ht := sgld_dimensionless_step hm hh hR hstep
  have hd : 0 < 1 + m * h := by positivity
  apply (le_div_iff₀ hd).mpr
  field_simp
  have h1 := mul_le_mul_of_nonneg_right hstep hh
  have h2 := mul_le_mul_of_nonneg_right (show 1 + m * h ≤ 4 / 3 by linarith)
    (show 0 ≤ 2 * R ^ 2 * h ^ 2 by positivity)
  nlinarith [mul_nonneg hm.le hh]

/-- The persistent error coefficient has exactly the paper's constants. -/
theorem sgld_bias_le {m R A h p : ℝ} (hm : 0 < m) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (hstep : 3 * R ^ 2 * h ≤ m) :
    ((A + m) / (1 + m * h) + 2 * R ^ 2 / m) * h ^ 2 * p ≤
      (A + 2 * m + 2 * R ^ 2 / m) * h ^ 2 * p / (1 + m * h) := by
  have hd : 0 < 1 + m * h := by positivity
  have hc : (A + m) / (1 + m * h) + 2 * R ^ 2 / m ≤
      (A + 2 * m + 2 * R ^ 2 / m) / (1 + m * h) := by
    apply (le_div_iff₀ hd).mpr
    field_simp
    nlinarith
  have hs := mul_le_mul_of_nonneg_right hc (show 0 ≤ h ^ 2 * p by positivity)
  convert hs using 1 <;> ring

/-- The exact SGLD finite-horizon rate from its explicitly supplied scalar
one-step inequality. The actual-law theorem discharges that premise. -/
theorem sgld_recurrence_bound (r : ℕ → ℝ) (m R A h p : ℝ)
    (hm : 0 < m) (hh : 0 ≤ h) (hp : 0 ≤ p) (hA : 0 ≤ A)
    (hR : m ^ 2 ≤ R ^ 2) (hstep : 3 * R ^ 2 * h ≤ m)
    (hr : ∀ n, 0 ≤ r n)
    (hrec : ∀ n, r (n + 1) ≤
      ((1 - m * h) / (1 + m * h) + 2 * R ^ 2 * h ^ 2) * r n +
      ((A + m) / (1 + m * h) + 2 * R ^ 2 / m) * h ^ 2 * p)
    (k : ℕ) :
    r k ≤ (1 + m * h)⁻¹ ^ k * r 0 +
      (A + 2 * m + 2 * R ^ 2 / m) * h * p / m := by
  let q := (1 + m * h)⁻¹
  let c := (A + 2 * m + 2 * R ^ 2 / m) * h * p / m
  have hd : 0 < 1 + m * h := by positivity
  have hq : 0 ≤ q := inv_nonneg.mpr hd.le
  have hc : 0 ≤ c := by dsimp [c]; positivity
  apply affine_floor_up_to r q c hq hc k
  intro j hj
  have hcontract := mul_le_mul_of_nonneg_right (sgld_contraction_le hm hh hR hstep) (hr j)
  have hbias := sgld_bias_le (A := A) (p := p) hm hh hp hstep
  have hfix : (A + 2 * m + 2 * R ^ 2 / m) * h ^ 2 * p / (1 + m * h) =
      (1 - q) * c := by
    dsimp [q, c]
    field_simp
    ring
  rw [hfix] at hbias
  have h := hrec j
  simp only [one_div] at hcontract
  change _ ≤ q * r j at hcontract
  linarith

end AverageLMC
