import UnadjustedLangevin.SharpContraction
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.header false

/-! # Parameters in the Pedrotti–Whalley Wasserstein mixing estimate

The numerical restrictions are explicit. The potential contract below is
derived from the paper's Hessian bounds in `CurvatureAssumptions`. The actual
stationary dynamics and Gaussian ULA invariant law are constructed later.
-/

noncomputable section

namespace WassersteinMixing

/-- Curvature, dimension and positive step, with precisely the small-step range. -/
structure Parameters where
  alpha : ℝ
  beta : ℝ
  step : ℝ
  dimension : ℕ
  alpha_pos : 0 < alpha
  alpha_le_beta : alpha ≤ beta
  step_pos : 0 < step
  step_beta_le : step * beta ≤ 1

/-- The condition number of the same curvature constants. -/
def Parameters.condition (P : Parameters) : ℝ := P.beta / P.alpha

/-- The contraction factor of a synchronous ULA step. -/
def Parameters.contraction (P : Parameters) : ℝ := 1 - P.alpha * P.step

/-- The literal bias constant in Theorem 1. -/
def Parameters.bias (P : Parameters) : ℝ :=
  6 * P.step * Real.sqrt (P.condition * P.beta * P.dimension)

theorem Parameters.beta_pos (P : Parameters) : 0 < P.beta :=
  P.alpha_pos.trans_le P.alpha_le_beta

theorem Parameters.condition_ge_one (P : Parameters) : 1 ≤ P.condition := by
  exact (le_div_iff₀ P.alpha_pos).mpr (by simpa using P.alpha_le_beta)

theorem Parameters.contraction_nonneg (P : Parameters) : 0 ≤ P.contraction := by
  dsimp [Parameters.contraction]
  have := mul_le_mul_of_nonneg_left P.alpha_le_beta P.step_pos.le
  nlinarith [P.step_beta_le]

theorem Parameters.contraction_lt_one (P : Parameters) : P.contraction < 1 := by
  dsimp [Parameters.contraction]
  nlinarith [mul_pos P.alpha_pos P.step_pos]

theorem Parameters.step_le_inv_beta (P : Parameters) : P.step ≤ 1 / P.beta := by
  exact (le_div_iff₀ P.beta_pos).mpr P.step_beta_le

theorem Parameters.bias_nonneg (P : Parameters) : 0 ≤ P.bias := by
  unfold Parameters.bias
  exact mul_nonneg (mul_nonneg (by norm_num) P.step_pos.le) (Real.sqrt_nonneg _)

/-- The first-order contract used by the existing ULA library. Every field is
derived from the original Hessian bounds in `CurvatureAssumptions`. -/
structure PotentialAssumptions {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (P : Parameters) (V : H → ℝ) : Prop where
  regularity : ContDiff ℝ 2 V
  strongConvexity : StrongConvexOn Set.univ P.alpha V
  gradientLipschitz : LipschitzWith ⟨P.beta, P.beta_pos.le⟩ (gradient V)

end WassersteinMixing
