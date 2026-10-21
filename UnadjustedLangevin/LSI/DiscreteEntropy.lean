import UnadjustedLangevin.Recurrence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-! # The scalar iteration in the LSI analysis of ULA

This file proves the final recurrence calculation in Vempala and Wibisono
(2019), Theorem 2. The one-step inequality is an explicit hypothesis: these
scalar lemmas alone do not establish it for ULA, identify `H` as a KL
divergence, or infer it merely from an LSI assumption.

The constants are those of the published theorem and its Lemma 3:
one-step forcing `6 * h^2 * n * L^2`, and bias bound `8 * h * n * L^2 / α`.
-/

namespace ULA.LSI

/-- The denominator estimate used in the proof of Theorem 2.
The lower tangent bound for `exp x` gives a reciprocal upper bound for
`exp (-x)`, which suffices on the displayed interval. -/
theorem three_quarters_mul_le_one_sub_exp_neg (x : ℝ)
    (hx : 0 ≤ x) (hsmall : x ≤ 1 / 4) :
    (3 / 4 : ℝ) * x ≤ 1 - Real.exp (-x) := by
  have hbase := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x)
    (Real.exp_nonneg (-x))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hbase
  have hpos : 0 < x + 1 := by linarith
  have hreciprocal : x / (x + 1) ≤ 1 - Real.exp (-x) := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [hbase]
  have hlinear : (3 / 4 : ℝ) * x ≤ x / (x + 1) := by
    apply (le_div_iff₀ hpos).mpr
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hsmall)]
  exact hlinear.trans hreciprocal

/-- The exact finite-horizon geometric envelope obtained from the paper's
one-step scalar recurrence. No sign assumption on the initial value is needed. -/
theorem discrete_entropy_recurrence_exact (H : ℕ → ℝ) (α h n L : ℝ)
    (hα : 0 < α) (hh : 0 < h)
    (hstep : ∀ k, H (k + 1) ≤ Real.exp (-α * h) * H k + 6 * h ^ 2 * n * L ^ 2)
    (k : ℕ) :
    H k ≤ Real.exp (-α * h * k) * H 0 +
      (6 * h ^ 2 * n * L ^ 2) * (1 - Real.exp (-α * h * k)) /
        (1 - Real.exp (-α * h)) := by
  have hq : Real.exp (-α * h) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hp : Real.exp (-α * h) ^ k = Real.exp (-α * h * k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [hp] using
    ULA.affine_recurrence_exact H (Real.exp (-α * h)) (6 * h ^ 2 * n * L ^ 2)
      (Real.exp_nonneg _) hq hstep k

/-- The bias-floor envelope obtained from the explicit one-step recurrence.
This is the scalar conclusion of Vempala--Wibisono (2019), Theorem 2;
the analytic proof of the recurrence remains a separate obligation. -/
theorem discrete_entropy_recurrence_bound (H : ℕ → ℝ) (α h n L : ℝ)
    (hα : 0 < α) (hh : 0 < h) (hn : 0 ≤ n) (hsmall : α * h ≤ 1 / 4)
    (hstep : ∀ k, H (k + 1) ≤ Real.exp (-α * h) * H k + 6 * h ^ 2 * n * L ^ 2)
    (k : ℕ) :
    H k ≤ Real.exp (-α * h * k) * H 0 + 8 * h * n * L ^ 2 / α := by
  have hah : 0 < α * h := mul_pos hα hh
  have hq : Real.exp (-α * h) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hden : 0 < 1 - Real.exp (-α * h) := sub_pos.mpr hq
  have hden_lower : (3 / 4 : ℝ) * (α * h) ≤ 1 - Real.exp (-α * h) := by
    simpa only [neg_mul] using
      three_quarters_mul_le_one_sub_exp_neg (α * h) hah.le hsmall
  have hb : 0 ≤ 6 * h ^ 2 * n * L ^ 2 := by positivity
  have hfloor : (6 * h ^ 2 * n * L ^ 2) / (1 - Real.exp (-α * h)) ≤
      8 * h * n * L ^ 2 / α := by
    apply (div_le_iff₀ hden).mpr
    have hmul := mul_le_mul_of_nonneg_left hden_lower
      (show 0 ≤ 8 * h * n * L ^ 2 / α by positivity)
    have heq : (8 * h * n * L ^ 2 / α) * ((3 / 4 : ℝ) * (α * h)) =
        6 * h ^ 2 * n * L ^ 2 := by
      field_simp
      ring
    rw [heq] at hmul
    exact hmul
  have hp : Real.exp (-α * h) ^ k = Real.exp (-α * h * k) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hrec := ULA.affine_recurrence_bound H (Real.exp (-α * h))
    (6 * h ^ 2 * n * L ^ 2) (Real.exp_nonneg _) hq hb hstep k
  rw [hp] at hrec
  exact hrec.trans (add_le_add (le_refl _) hfloor)

end ULA.LSI
