import KineticLangevin.Recurrence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! # Quantitative error budgets and integer iteration counts

This is the scalar accuracy corollary of the proved kinetic error estimate.
It keeps the stability restriction and bias budget separate, treats zero
initial error, and rounds the logarithmic threshold to an actual natural
number. It does not assert an unproved stochastic convergence theorem.
-/

noncomputable section
namespace KineticLangevin

/-- Geometric decay is bounded by its exponential envelope. -/
theorem one_sub_pow_le_exp (α : ℝ) (hα : α ≤ 1) (n : ℕ) :
    (1-α)^n ≤ Real.exp (-α*(n : ℝ)) := by
  have hb : 1-α ≤ Real.exp (-α) := by linarith [Real.add_one_le_exp (-α)]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1-α) hb n
  convert hp using 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- A nonnegative, integer iteration threshold for the paper's initial-error
budget `epsilon/24`. The maximum handles logarithms below zero. -/
def firstOrderIterationCount (α D ε : ℝ) : ℕ :=
  Nat.ceil (max 0 (Real.log (24*D/ε)/α))

/-- Every natural iteration count above the rounded threshold satisfies the
unrounded logarithmic requirement. -/
theorem firstOrderIterationCount_spec (α D ε : ℝ) (hα : 0 < α) (n : ℕ)
    (hn : firstOrderIterationCount α D ε ≤ n) :
    Real.log (24*D/ε) ≤ α*(n : ℝ) := by
  have hceil : max 0 (Real.log (24*D/ε)/α) ≤
      (firstOrderIterationCount α D ε : ℝ) := Nat.le_ceil _
  have hnreal : (firstOrderIterationCount α D ε : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : Real.log (24*D/ε)/α ≤ (n : ℝ) :=
    (le_max_right _ _).trans (hceil.trans hnreal)
  simpa only [mul_comm] using (div_le_iff₀ hα).mp hs

/-- The positive-initial-error logarithm controls the exponential transient. -/
theorem firstOrder_transient_budget (α D ε : ℝ) (hα : α ≤ 1)
    (hD : 0 < D) (hε : 0 < ε) (n : ℕ)
    (hcount : Real.log (24*D/ε) ≤ α*(n : ℝ)) :
    (1-α)^n*D ≤ ε/24 := by
  have he := Real.exp_le_exp.mpr (show -α*(n : ℝ) ≤ -Real.log (24*D/ε) by linarith)
  have hr : 0 < 24*D/ε := by positivity
  rw [Real.exp_neg, Real.exp_log hr] at he
  have hm := mul_le_mul_of_nonneg_right he hD.le
  have hc : (24*D/ε)⁻¹*D = ε/24 := by field_simp
  rw [hc] at hm
  exact (mul_le_mul_of_nonneg_right (one_sub_pow_le_exp α hα n) hD.le).trans hm

/-- The manuscript's `0.94 epsilon` bias allocation and `epsilon/24`
transient allocation imply total error at most `epsilon`. The zero initial
error case needs no logarithm and no iteration lower bound. -/
theorem firstOrder_accuracy_budget (α D ε bias error : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D) (hε : 0 < ε)
    (hbias : bias ≤ (47/50 : ℝ)*ε) (n : ℕ)
    (hn : D = 0 ∨ firstOrderIterationCount α D ε ≤ n)
    (herror : error ≤ Real.sqrt 2 * (1-α)^n*D+bias) : error ≤ ε := by
  have hsqrt : Real.sqrt 2 ≤ (36/25 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  rcases eq_or_lt_of_le hD with hzero | hpos
  · have hz : D = 0 := hzero.symm
    simp only [hz, mul_zero, zero_add] at herror
    linarith
  · have hcount : firstOrderIterationCount α D ε ≤ n := by
      rcases hn with hz | hn
      · exact False.elim (hpos.ne' hz)
      · exact hn
    have ht := firstOrder_transient_budget α D ε hα1 hpos hε n
      (firstOrderIterationCount_spec α D ε hα n hcount)
    have hm := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg 2)
    have heps := mul_le_mul_of_nonneg_right hsqrt hε.le
    nlinarith

end KineticLangevin
