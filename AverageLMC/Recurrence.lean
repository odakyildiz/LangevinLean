import UnadjustedLangevin.Recurrence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Scalar recurrences in the averaged-smoothness LMC paper

These are conditional scalar consequences of the one-step stochastic inequality.
They do not assert that an LMC law satisfies that inequality. `a` denotes the
average condition number plus one, `κ` the maximal condition number, and `t = mh`
the dimensionless step. In this normalization the paper's recursion is
`r (k+1) ≤ (1-t)/(1+t) * r k + a*t^2/(1+t)`.
-/

namespace AverageLMC

/-- The exact contraction in Theorem 1 is at most `exp (-2t)`. -/
theorem contraction_le_exp {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) / (1 + t) ≤ Real.exp (-2 * t) := by
  rcases eq_or_lt_of_le ht1 with h | h
  · subst t
    simpa using (Real.exp_pos (-2 : ℝ)).le
  have hp : 0 < 1 + t := by linarith
  have hm : 0 < 1 - t := by linarith
  have hl := Real.sum_range_le_log_div ht h 1
  simp only [Finset.sum_range_one, mul_zero, zero_add, pow_one] at hl
  have hi : (1 - t) / (1 + t) = ((1 + t) / (1 - t))⁻¹ := by
    simp [inv_div]
  apply (Real.log_le_iff_le_exp (div_pos hm hp)).1
  rw [hi, Real.log_inv]
  linarith

/-- Finite-horizon affine iteration, with a fixed point `c`. -/
theorem affine_floor_up_to (r : ℕ → ℝ) (q c : ℝ) (hq : 0 ≤ q)
    (hc : 0 ≤ c) (n : ℕ)
    (hstep : ∀ j < n, r (j + 1) ≤ q * r j + (1 - q) * c) :
    r n ≤ q ^ n * r 0 + c := by
  have hstrong : ∀ k ≤ n, r k ≤ q ^ k * r 0 + (1 - q ^ k) * c := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hprev := ih (Nat.le_of_succ_le hk)
      have hmul := mul_le_mul_of_nonneg_left hprev hq
      have hs := hstep k (Nat.lt_of_succ_le hk)
      rw [pow_succ]
      nlinarith
  have h := hstrong n le_rfl
  nlinarith [mul_nonneg (pow_nonneg hq n) hc]

/-- The constant-step bound of Theorem 1, for a normalized scalar error.
The stochastic one-step estimate is an explicit input. -/
theorem constant_step_normalized_up_to (r : ℕ → ℝ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hr0 : 0 ≤ r 0) (n : ℕ)
    (hstep : ∀ j < n, r (j + 1) ≤
      (1 - t) / (1 + t) * r j + a * t ^ 2 / (1 + t)) :
    r n ≤ Real.exp (-2 * t * (n : ℝ)) * r 0 + a * t / 2 := by
  have hd : 0 < 1 + t := by linarith
  have hq : 0 ≤ (1 - t) / (1 + t) := div_nonneg (by linarith) hd.le
  have hfix : a * t ^ 2 / (1 + t) =
      (1 - (1 - t) / (1 + t)) * (a * t / 2) := by
    field_simp
    ring
  have h := affine_floor_up_to r ((1 - t) / (1 + t)) (a * t / 2) hq
    (by positivity) n (by simpa only [hfix] using hstep)
  have hp := pow_le_pow_left₀ hq (contraction_le_exp ht ht1) n
  have heq : Real.exp (-2 * t) ^ n = Real.exp (-2 * t * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq] at hp
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hp hr0) le_rfl)

/-- Infinite-sequence version of the scalar constant-step estimate. -/
theorem constant_step_normalized (r : ℕ → ℝ) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hr0 : 0 ≤ r 0)
    (hstep : ∀ j, r (j + 1) ≤
      (1 - t) / (1 + t) * r j + a * t ^ 2 / (1 + t)) (n : ℕ) :
    r n ≤ Real.exp (-2 * t * (n : ℝ)) * r 0 + a * t / 2 :=
  constant_step_normalized_up_to r a t ha ht ht1 hr0 n (fun j _ ↦ hstep j)

/-- The algebraic induction step in Proposition 1, with its exact constants. -/
theorem harmonic_step {a x r : ℝ} (hx : 1 ≤ x)
    (hr : r ≤ a / x) :
    (1 - 1 / x) / (1 + 1 / x) * r + a * (1 / x) ^ 2 / (1 + 1 / x)
      ≤ a / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hd : 0 < 1 + 1 / x := by positivity
  have hdiv : 1 / x ≤ 1 := (div_le_one hx0).mpr hx
  have hq : 0 ≤ (1 - 1 / x) / (1 + 1 / x) := div_nonneg (by linarith) hd.le
  calc
    _ ≤ (1 - 1 / x) / (1 + 1 / x) * (a / x) +
        a * (1 / x) ^ 2 / (1 + 1 / x) :=
      add_le_add (mul_le_mul_of_nonneg_left hr hq) le_rfl
    _ = a / (x + 1) := by
      field_simp
      ring

/-- Once the warmup is complete, the variable schedule gives the paper's
`a / (κ + n)` bound. This is the scalar part of Proposition 1. -/
theorem variable_step_tail (r : ℕ → ℝ) (a κ : ℝ)
    (_ha : 0 ≤ a) (hκ : 1 ≤ κ) (hinit : r 0 ≤ a / κ)
    (hstep : ∀ n, r (n + 1) ≤
      (1 - 1 / (κ + (n : ℝ))) / (1 + 1 / (κ + (n : ℝ))) * r n +
      a * (1 / (κ + (n : ℝ))) ^ 2 / (1 + 1 / (κ + (n : ℝ))))
    (n : ℕ) : r n ≤ a / (κ + (n : ℝ)) := by
  induction n with
  | zero => simpa using hinit
  | succ n ih =>
    have hx : 1 ≤ κ + (n : ℝ) := by
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    have h := (hstep n).trans (harmonic_step hx ih)
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using h

end AverageLMC
