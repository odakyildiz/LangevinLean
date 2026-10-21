import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! # The scalar final step of Dalalyan's synchronous-coupling argument

This file proves only the recurrence calculation. The stochastic one-step
inequality must be established separately; it is not hidden in a definition.
For a fixed positive step the bias remains positive as the number of steps grows.
-/

namespace ULA

open Filter
open scoped Topology

/-- Iterating an affine inequality gives the exact finite geometric sum. -/
theorem affine_recurrence_sum (e : ℕ → ℝ) (q b : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ n, e (n + 1) ≤ q * e n + b) (n : ℕ) :
    e n ≤ q ^ n * e 0 + b * ∑ j ∈ Finset.range n, q ^ j := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hmul := mul_le_mul_of_nonneg_left ih hq
      have hgeom := mul_geom_sum q n
      have hid : q * (∑ j ∈ Finset.range n, q ^ j) + 1 =
          (∑ j ∈ Finset.range n, q ^ j) + q ^ n := by nlinarith
      have hidb := congrArg (fun t : ℝ ↦ b * t) hid
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [hstep n, hidb]

/-- Closed form retaining the finite-horizon factor `1 - q^n`. -/
theorem affine_recurrence_exact (e : ℕ → ℝ) (q b : ℝ) (hq : 0 ≤ q)
    (hq1 : q < 1) (hstep : ∀ n, e (n + 1) ≤ q * e n + b) (n : ℕ) :
    e n ≤ q ^ n * e 0 + b * (1 - q ^ n) / (1 - q) := by
  have hs := affine_recurrence_sum e q b hq hstep n
  rw [geom_sum_eq (ne_of_lt hq1) n] at hs
  rw [show q ^ n - 1 = -(1 - q ^ n) by ring,
    show q - 1 = -(1 - q) by ring, neg_div_neg_eq, ← mul_div_assoc] at hs
  exact hs

/-- Dropping the finite-horizon correction gives the usual bias-floor bound. -/
theorem affine_recurrence_bound (e : ℕ → ℝ) (q b : ℝ) (hq : 0 ≤ q)
    (hq1 : q < 1) (hb : 0 ≤ b)
    (hstep : ∀ n, e (n + 1) ≤ q * e n + b) (n : ℕ) :
    e n ≤ q ^ n * e 0 + b / (1 - q) := by
  have h := affine_recurrence_exact e q b hq hq1 hstep n
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hnum : b * (1 - q ^ n) ≤ b := by
    nlinarith [pow_nonneg hq n]
  exact h.trans (add_le_add_right ((div_le_div_iff_of_pos_right hden).mpr hnum) _)

/-- The upper envelope tends to the bias floor, not necessarily to zero. -/
theorem bias_envelope_tendsto (q b initial : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ ↦ q ^ n * initial + b / (1 - q)) atTop
      (𝓝 (b / (1 - q))) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1
  simpa using (hp.mul_const initial).add_const (b / (1 - q))

/-- Any requested accuracy above the bias floor is eventually attained. -/
theorem eventually_below_bias (e : ℕ → ℝ) (q b : ℝ) (hq : 0 ≤ q)
    (hq1 : q < 1) (hb : 0 ≤ b)
    (hstep : ∀ n, e (n + 1) ≤ q * e n + b)
    (ε : ℝ) (hε : b / (1 - q) < ε) :
    ∀ᶠ n in atTop, e n < ε := by
  have he := (bias_envelope_tendsto q b (e 0) hq hq1).eventually
    (gt_mem_nhds hε)
  filter_upwards [he] with n hn
  exact lt_of_le_of_lt (affine_recurrence_bound e q b hq hq1 hb hstep n) hn

end ULA
