import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Iteration and geometric convergence

This file isolates the elementary convergence argument. A nonnegative gap
that decreases by a factor `ρ ∈ [0, 1)` is bounded by its initial value times
`ρ ^ n`. A quadratic lower bound on the gap then gives convergence of the
iterates in norm.
-/

namespace GradientDescent

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Gradient descent with constant step size, starting from `x₀`. -/
def iterate (g : H → H) (α : ℝ) (x₀ : H) : ℕ → H
  | 0 => x₀
  | n + 1 => iterate g α x₀ n - α • g (iterate g α x₀ n)

@[simp]
theorem iterate_zero (g : H → H) (α : ℝ) (x₀ : H) : iterate g α x₀ 0 = x₀ := rfl

@[simp]
theorem iterate_succ (g : H → H) (α : ℝ) (x₀ : H) (n : ℕ) :
    iterate g α x₀ (n + 1) = iterate g α x₀ n - α • g (iterate g α x₀ n) := rfl

/-- Iterating a scalar one-step contraction gives a geometric bound. -/
theorem geometric_bound {a : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hstep : ∀ n, a (n + 1) ≤ ρ * a n) (n : ℕ) :
    a n ≤ ρ ^ n * a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        a (n + 1) ≤ ρ * a n := hstep n
        _ ≤ ρ * (ρ ^ n * a 0) := mul_le_mul_of_nonneg_left ih hρ
        _ = ρ ^ (n + 1) * a 0 := by rw [pow_succ]; ring

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- The objective gap inherits the geometric bound from its one-step inequality. -/
theorem geometric_gap_bound (f : H → ℝ) (x : ℕ → H) (z : H) {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (hstep : ∀ n, f (x (n + 1)) - f z ≤ ρ * (f (x n) - f z)) (n : ℕ) :
    f (x n) - f z ≤ ρ ^ n * (f (x 0) - f z) :=
  geometric_bound (a := fun n => f (x n) - f z) hρ hstep n

omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
/-- A nonnegative geometrically decreasing objective gap tends to zero. -/
theorem gap_tendsto_zero (f : H → ℝ) (x : ℕ → H) (z : H) {ρ : ℝ}
    (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hgap : ∀ n, 0 ≤ f (x n) - f z)
    (hstep : ∀ n, f (x (n + 1)) - f z ≤ ρ * (f (x n) - f z)) :
    Tendsto (fun n => f (x n) - f z) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ρ ^ n * (f (x 0) - f z)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀ hρ₁).mul_const
      (f (x 0) - f z)
  exact squeeze_zero hgap (geometric_gap_bound f x z hρ₀ hstep) hpow

omit [NormedSpace ℝ H] in
/-- A quadratic gap lower bound gives an explicit squared-distance rate. -/
theorem squared_distance_bound (f : H → ℝ) (x : ℕ → H) (z : H) {m ρ : ℝ}
    (hm : 0 < m) (hρ : 0 ≤ ρ)
    (hlower : ∀ n, m / 2 * ‖x n - z‖ ^ 2 ≤ f (x n) - f z)
    (hstep : ∀ n, f (x (n + 1)) - f z ≤ ρ * (f (x n) - f z)) (n : ℕ) :
    ‖x n - z‖ ^ 2 ≤ (2 / m) * (ρ ^ n * (f (x 0) - f z)) := by
  have h := (hlower n).trans (geometric_gap_bound f x z hρ hstep n)
  have hdiv : ‖x n - z‖ ^ 2 ≤ (ρ ^ n * (f (x 0) - f z)) / (m / 2) :=
    (le_div_iff₀ (by positivity : 0 < m / 2)).2 (by simpa [mul_comm] using h)
  convert hdiv using 1
  field_simp

omit [NormedSpace ℝ H] in
/-- Geometric decay plus a positive quadratic lower bound implies norm convergence. -/
theorem tendsto_of_geometric_gap (f : H → ℝ) (x : ℕ → H) (z : H) {m ρ : ℝ}
    (hm : 0 < m) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1)
    (hlower : ∀ n, m / 2 * ‖x n - z‖ ^ 2 ≤ f (x n) - f z)
    (hstep : ∀ n, f (x (n + 1)) - f z ≤ ρ * (f (x n) - f z)) :
    Tendsto x atTop (𝓝 z) := by
  have hbound : Tendsto (fun n : ℕ => (2 / m) *
      (ρ ^ n * (f (x 0) - f z))) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀ hρ₁).mul_const
      (f (x 0) - f z)).const_mul (2 / m)
  have hsq : Tendsto (fun n => ‖x n - z‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (squared_distance_bound f x z hm hρ₀ hlower hstep)
      hbound
  have hnorm : Tendsto (fun n => ‖x n - z‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt
  exact tendsto_iff_dist_tendsto_zero.2 (by simpa only [dist_eq_norm] using hnorm)

end GradientDescent
