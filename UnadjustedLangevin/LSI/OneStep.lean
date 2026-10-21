import UnadjustedLangevin.LSI.EntropyDecay
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option linter.style.header false

/-!
# The scalar interpolation estimate behind the ULA entropy bound

This file proves the analytic last step of the one-step entropy estimate.
Continuity, entropy production, the pointwise LSI inequality, and the initial
gradient-moment estimate are explicit hypotheses. It does not assert that an
actual ULA interpolation satisfies these analytic hypotheses.
-/

namespace ULA.LSI

open Set

/-- On the small-step interval, a small forcing proportional to the initial
entropy is absorbed by the difference between the two exponential rates. -/
theorem exp_three_halves_gap (x : ℝ) (hx : 0 ≤ x) (hsmall : x ≤ 1 / 4) :
    Real.exp (-(3 / 2 : ℝ) * x) + x / 4 ≤ Real.exp (-x) := by
  have hlow : (1 / 2 : ℝ) ≤ Real.exp (-(3 / 2 : ℝ) * x) := by
    linarith [Real.add_one_le_exp (-(3 / 2 : ℝ) * x)]
  have hmul := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (x / 2))
    (Real.exp_nonneg (-(3 / 2 : ℝ) * x))
  rw [← Real.exp_add, show -(3 / 2 : ℝ) * x + x / 2 = -x by ring] at hmul
  nlinarith [mul_nonneg (sub_nonneg.mpr hlow) hx]

/-- Scalar one-step estimate with the constant `6` from the entropy-production
and gradient-moment bounds. The dimension parameter is a nonnegative real;
finite-dimensional applications substitute the natural dimension cast to `ℝ`. -/
theorem one_step_entropy_of_interpolation
    (H H' I : ℝ → ℝ) (G₀ α L h n : ℝ)
    (hα : 0 < α) (hL : 0 < L) (hh : 0 < h) (hαL : α ≤ L) (hn : 0 ≤ n)
    (hsmall : h ≤ α / (4 * L ^ 2)) (hH₀ : 0 ≤ H 0)
    (hcont : ContinuousOn H (Icc 0 h))
    (hderiv : ∀ t ∈ Ico 0 h, HasDerivWithinAt H (H' t) (Ici t) t)
    (hlsi : ∀ t ∈ Ico 0 h, 2 * α * H t ≤ I t)
    (hproduction : ∀ t ∈ Ico 0 h,
      H' t ≤ -(3 / 4 : ℝ) * I t + t ^ 2 * L ^ 2 * G₀ + 2 * t * n * L ^ 2)
    (hgradient : G₀ ≤ (4 * L ^ 2 / α) * H 0 + 2 * n * L) :
    H h ≤ Real.exp (-α * h) * H 0 + 6 * h ^ 2 * n * L ^ 2 := by
  have hstep : 4 * h * L ^ 2 ≤ α := by
    have := (le_div_iff₀ (by positivity : 0 < 4 * L ^ 2)).mp hsmall
    nlinarith
  have hhL : h * L ≤ 1 / 4 := by
    have hp : (4 * h * L) * L ≤ 1 * L := by nlinarith
    have := (mul_le_mul_iff_of_pos_right hL).mp hp
    linarith
  have hhα : α * h ≤ 1 / 4 := by nlinarith
  let A := (4 * L ^ 2 / α) * H 0 + 2 * n * L
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcoeff : h ^ 2 * L ^ 2 * (4 * L ^ 2 / α) ≤ α / 4 := by
    have hbase : h * L ^ 2 ≤ α / 4 := by linarith
    have hsquare : (h * L ^ 2) ^ 2 ≤ (α / 4) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by positivity)).mpr hbase
    calc
      h ^ 2 * L ^ 2 * (4 * L ^ 2 / α) = 4 * (h * L ^ 2) ^ 2 / α := by ring
      _ ≤ 4 * (α / 4) ^ 2 / α :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsquare (by norm_num)) hα.le
      _ = α / 4 := by field_simp
  have hcoeffH := mul_le_mul_of_nonneg_right hcoeff hH₀
  have hnoise : h ^ 2 * L ^ 2 * (2 * n * L) ≤ (1 / 2 : ℝ) * h * n * L ^ 2 := by
    have hp := mul_le_mul_of_nonneg_left hhL
      (by positivity : 0 ≤ 2 * h * n * L ^ 2)
    nlinarith
  have huniform : h ^ 2 * L ^ 2 * A ≤
      (α / 4) * H 0 + (1 / 2 : ℝ) * h * n * L ^ 2 := by
    dsimp [A]
    nlinarith
  let b := (α / 4) * H 0 + (5 / 2 : ℝ) * h * n * L ^ 2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hbound : ∀ t ∈ Ico 0 h, H' t ≤ -((3 / 2 : ℝ) * α) * H t + b := by
    intro t ht
    have htsq : t ^ 2 ≤ h ^ 2 := (sq_le_sq₀ ht.1 hh.le).mpr ht.2.le
    have hp₁ := mul_le_mul_of_nonneg_left hgradient (by positivity : 0 ≤ t ^ 2 * L ^ 2)
    have hp₂ := mul_le_mul_of_nonneg_right htsq (by positivity : 0 ≤ L ^ 2 * A)
    have hp₃ := mul_le_mul_of_nonneg_right ht.2.le (by positivity : 0 ≤ 2 * n * L ^ 2)
    have hp₄ := mul_le_mul_of_nonneg_left (hlsi t ht) (by norm_num : (0 : ℝ) ≤ 3 / 4)
    have hp₅ := hproduction t ht
    change G₀ ≤ A at hgradient
    change t ^ 2 * L ^ 2 * G₀ ≤ t ^ 2 * L ^ 2 * A at hp₁
    dsimp [b]
    nlinarith
  have hcompare := affine_decay_of_deriv_right_le H H' ((3 / 2 : ℝ) * α) b h
    (by positivity) hcont hderiv hbound h ⟨hh.le, le_rfl⟩
  have hintegral : b / ((3 / 2 : ℝ) * α) *
      (1 - Real.exp (-((3 / 2 : ℝ) * α) * h)) ≤ b * h := by
    have he : 1 - Real.exp (-((3 / 2 : ℝ) * α) * h) ≤ ((3 / 2 : ℝ) * α) * h := by
      linarith [Real.add_one_le_exp (-((3 / 2 : ℝ) * α) * h)]
    have hm := mul_le_mul_of_nonneg_left he
      (div_nonneg hb (by positivity : 0 ≤ (3 / 2 : ℝ) * α))
    have heq : b / ((3 / 2 : ℝ) * α) * (((3 / 2 : ℝ) * α) * h) = b * h := by
      field_simp
    simpa only [heq] using hm
  have hexp := mul_le_mul_of_nonneg_right
    (exp_three_halves_gap (α * h) (by positivity) hhα) hH₀
  have hnoise_final : (5 / 2 : ℝ) * h ^ 2 * n * L ^ 2 ≤ 6 * h ^ 2 * n * L ^ 2 := by
    have : 0 ≤ h ^ 2 * n * L ^ 2 := by positivity
    nlinarith
  have hexp_arg : -((3 / 2 : ℝ) * α) * h = -(3 / 2 : ℝ) * (α * h) := by ring
  rw [hexp_arg] at hcompare hintegral
  rw [show -(α * h) = -α * h by ring] at hexp
  dsimp [b] at hcompare hintegral
  nlinarith

end ULA.LSI
