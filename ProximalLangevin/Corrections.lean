import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-! # Exact algebraic certificates for corrections in arXiv:2406.14292

These certificates concern the displayed calculations in the paper. They do
not assert a convergence theorem for a proximal particle algorithm.
-/


noncomputable section

namespace ProximalLangevin.Corrections

/-- The proximal point of `u ↦ u²/2` is `x/(1+lam)`. The difference of
objectives is a nonnegative square; no differentiability of an argmin map is
assumed. -/
theorem quadratic_prox_minimizes (x lam : ℝ) (hlam : 0 < lam) (u : ℝ) :
    (x / (1 + lam)) ^ 2 / 2 + (x / (1 + lam) - x) ^ 2 / (2 * lam) ≤
      u ^ 2 / 2 + (u - x) ^ 2 / (2 * lam) := by
  have hd : 1 + lam ≠ 0 := by positivity
  have hidentity :
      (u ^ 2 / 2 + (u - x) ^ 2 / (2 * lam)) -
        ((x / (1 + lam)) ^ 2 / 2 + (x / (1 + lam) - x) ^ 2 / (2 * lam)) =
      (1 + lam) / (2 * lam) * (u - x / (1 + lam)) ^ 2 := by
    field_simp
    ring
  have hnonneg : 0 ≤ (1 + lam) / (2 * lam) * (u - x / (1 + lam)) ^ 2 := by positivity
  linarith

/-- The second-order coefficient in the proximal expansion has a positive
sign. This exact identity diagnoses the opposite sign in v1 equation (25)
and v3 equation (22). -/
theorem quadratic_prox_expansion (x lam : ℝ) (hlam : 1 + lam ≠ 0) :
    x / (1 + lam) = x - lam * x + lam ^ 2 * x - lam ^ 3 * x / (1 + lam) := by
  field_simp
  ring

/-- The negative second-order term printed in v1 equation (25) / v3 equation
(22) leaves an error of order `lam²`, already for the scalar quadratic. -/
theorem negative_second_order_residual (lam : ℝ) (hlam : 0 < lam) :
    1 / (1 + lam) - (1 - lam - lam ^ 2) = lam ^ 2 * (2 + lam) / (1 + lam) := by
  field_simp
  ring

theorem negative_second_order_residual_ge_sq (lam : ℝ) (hlam : 0 < lam) :
    lam ^ 2 ≤ 1 / (1 + lam) - (1 - lam - lam ^ 2) := by
  rw [negative_second_order_residual lam hlam]
  apply (le_div_iff₀ (by positivity : 0 < 1 + lam)).mpr
  nlinarith [sq_nonneg lam]

/-- Scaling a gradient by `N` scales its squared norm by `N²`, not `N`.
This corrects v1 Corollary A.5; v3 Corollary A.12 already uses this scaling. -/
theorem squared_gradient_scaling {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (N : ℝ) (g : E) :
    ‖N • g‖ ^ 2 = N ^ 2 * ‖g‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

/-- A numerical witness to the invalid `NC` bound from the valid `C` bound
when the gradient is multiplied by `N`. -/
theorem linear_squared_gradient_scaling_fails :
    ¬ ((2 * (1 : ℝ)) ^ 2 ≤ 2 * 1) := by norm_num

/-- The geometric-series denominator is zero at the upper endpoint allowed
in v1 Corollaries A.4--A.6 and v3 Corollaries A.11--A.13. A finite error floor
requires a strict inequality. -/
theorem endpoint_denominator_zero (μ γ : ℝ)
    (hγ : γ ≠ 0) (hden : 1 - μ * γ ≠ 0) :
    1 - (γ / (1 - μ * γ)) * (1 - μ * γ) / γ = 0 := by
  rw [div_mul_cancel₀ γ hden, div_self hγ]
  norm_num

/-- At `q=1`, the recurrence `e(n+1)=e(n)+1` has linear growth.
Interpreting real division by zero cannot rescue the printed error floor. -/
theorem endpoint_error_floor_fails :
    ¬ ((1 : ℝ) ≤ 0 + 1 / (1 - 1)) := by norm_num

/-- If the proximal displacement satisfies the paper's assumption B1, the
envelope gradient inherits the constant `μ/γ`. -/
theorem proximal_displacement_strong_monotonicity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p : E → E) (μ γ : ℝ) (hγ : 0 < γ)
    (hB : ∀ x y, inner ℝ (x - y) (p x - p y) ≤ (1 - μ) * ‖x - y‖ ^ 2)
    (x y : E) :
    (μ / γ) * ‖x - y‖ ^ 2 ≤
      inner ℝ (x - y) (γ⁻¹ • (x - p x) - γ⁻¹ • (y - p y)) := by
  have hid : γ⁻¹ • (x - p x) - γ⁻¹ • (y - p y) =
      γ⁻¹ • ((x - y) - (p x - p y)) := by module
  rw [hid, inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq]
  have h := mul_le_mul_of_nonneg_left (hB x y) (inv_nonneg.mpr hγ.le)
  rw [div_eq_mul_inv]
  nlinarith

/-- The pair objective for the convex, globally Lipschitz penalty
`g₂(θ,x)=|θ-x|` with smoothing parameter one. -/
def pairAbsObjective (θ x θ₀ x₀ : ℝ) : ℝ :=
  |θ - x| + ((θ - θ₀) ^ 2 + (x - x₀) ^ 2) / 2

/-- At pair input `(1,0)`, the true proximal point is `(1/2,1/2)`. -/
theorem pairAbs_first_prox (θ x : ℝ) :
    pairAbsObjective (1 / 2) (1 / 2) 1 0 ≤ pairAbsObjective θ x 1 0 := by
  have ha : (θ - x) / 2 ≤ |θ - x| := by
    nlinarith [le_abs_self (θ - x), abs_nonneg (θ - x)]
  norm_num [pairAbsObjective]
  nlinarith [sq_nonneg (θ - 1 / 2), sq_nonneg (x - 1 / 2)]

/-- At pair input `(1,4)`, the true proximal point is `(2,3)`. -/
theorem pairAbs_second_prox (θ x : ℝ) :
    pairAbsObjective 2 3 1 4 ≤ pairAbsObjective θ x 1 4 := by
  have ha := neg_le_abs (θ - x)
  norm_num [pairAbsObjective]
  nlinarith [sq_nonneg (θ - 2), sq_nonneg (x - 3)]

/-- The two-particle lifted objective in physical particle coordinates.
The quadratic penalty uses precisely the scaled state norm with `N=2`. -/
def sharedAbsObjective (θ x₁ x₂ : ℝ) : ℝ :=
  (|θ - x₁| + |θ - x₂|) / 2 +
    ((θ - 1) ^ 2 + (x₁ ^ 2 + (x₂ - 4) ^ 2) / 2) / 2

/-- Averaging the two true pairwise proximal outputs gives parameter `5/4`
and particles `(1/2,3)`. A feasible competitor `(1,1,3)` has strictly smaller
lifted objective. Thus the pairwise average cannot be a lifted proximal
minimizer, even for a convex globally Lipschitz penalty. -/
theorem averaged_pair_prox_not_lifted_minimizer :
    sharedAbsObjective 1 1 3 < sharedAbsObjective (5 / 4) (1 / 2) 3 := by
  norm_num [sharedAbsObjective]

end ProximalLangevin.Corrections
