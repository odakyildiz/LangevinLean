import WassersteinMixing.Parameters
import UnadjustedLangevin.Recurrence

set_option linter.style.header false

/-! # The exact energy floor and the coefficient six

The recurrence is a scalar energy lemma. The actual stochastic comparison
derives its hypotheses from the shifted equation and conditional centering.
-/

noncomputable section

namespace WassersteinMixing

/-- The squared corrector budget obtained from its proved semigroup norm estimate. -/
def Parameters.correctorBudget (P : Parameters) : ℝ :=
  P.step ^ 2 * P.beta * P.dimension

/-- The forcing in the shifted energy equation, with the exact coefficient 19. -/
def Parameters.energyForcing (P : Parameters) : ℝ :=
  19 * P.step ^ 3 * P.beta ^ 2 * P.dimension

/-- The fixed point of the shifted squared-error recurrence. -/
def Parameters.energyFloor (P : Parameters) : ℝ :=
  19 * P.step ^ 2 * P.condition * P.beta * P.dimension

theorem Parameters.correctorBudget_nonneg (P : Parameters) : 0 ≤ P.correctorBudget := by
  unfold Parameters.correctorBudget
  exact mul_nonneg (mul_nonneg (sq_nonneg _) P.beta_pos.le) (Nat.cast_nonneg _)

theorem Parameters.energyFloor_nonneg (P : Parameters) : 0 ≤ P.energyFloor := by
  unfold Parameters.energyFloor
  have := P.condition_ge_one
  have := P.beta_pos
  positivity

/-- The factor in the recurrence cancels the strong-convexity denominator. -/
theorem Parameters.energy_fixed_point (P : Parameters) :
    P.contraction * P.energyFloor + P.energyForcing = P.energyFloor := by
  dsimp [Parameters.contraction, Parameters.energyFloor,
    Parameters.energyForcing, Parameters.condition]
  field_simp [ne_of_gt P.alpha_pos]
  ring

theorem Parameters.correctorBudget_le_floor (P : Parameters) :
    P.correctorBudget ≤ P.energyFloor := by
  have hκ := P.condition_ge_one
  have hbase := P.correctorBudget_nonneg
  change P.correctorBudget ≤ 19 * P.step ^ 2 * P.condition * P.beta * P.dimension
  have heq : 19 * P.step ^ 2 * P.condition * P.beta * P.dimension =
      19 * P.condition * P.correctorBudget := by
    unfold Parameters.correctorBudget
    ring
  rw [heq]
  nlinarith

/-- Starting the synchronous chains together gives a uniform energy floor,
so no unformalized manipulation of a limit superior is needed. -/
theorem shifted_energy_uniform (P : Parameters) (energy : ℕ → ℝ)
    (hzero : energy 0 ≤ P.correctorBudget)
    (hstep : ∀ n, energy (n + 1) ≤ P.contraction * energy n + P.energyForcing)
    (n : ℕ) : energy n ≤ P.energyFloor := by
  induction n with
  | zero => exact hzero.trans P.correctorBudget_le_floor
  | succ n ih =>
    have hmul := mul_le_mul_of_nonneg_left ih P.contraction_nonneg
    have hfix := P.energy_fixed_point
    linarith [hstep n]

/-- An exact finite-time envelope is also available for arbitrary initial energy. -/
theorem shifted_energy_finite (P : Parameters) (energy : ℕ → ℝ)
    (hstep : ∀ n, energy (n + 1) ≤ P.contraction * energy n + P.energyForcing)
    (n : ℕ) :
    energy n ≤ P.contraction ^ n * energy 0 +
      (1 - P.contraction ^ n) * P.energyFloor := by
  have h := ULA.affine_recurrence_exact energy P.contraction P.energyForcing
    P.contraction_nonneg P.contraction_lt_one hstep n
  have hid : P.energyForcing = (1 - P.contraction) * P.energyFloor := by
    nlinarith [P.energy_fixed_point]
  rw [hid] at h
  have hd : 1 - P.contraction ≠ 0 := ne_of_gt (sub_pos.mpr P.contraction_lt_one)
  convert h using 1
  field_simp [hd]

/-- Numerical conversion of the two squared budgets gives the literal
coefficient six in the manuscript. -/
theorem shifted_norm_le_bias {H : Type*} [NormedAddCommGroup H]
    (P : Parameters) (z g : H)
    (hu : ‖z + g‖ ^ 2 ≤ P.energyFloor)
    (hg : ‖g‖ ^ 2 ≤ P.correctorBudget) : ‖z‖ ≤ P.bias := by
  let R := P.step * Real.sqrt (P.condition * P.beta * P.dimension)
  have hbase : 0 ≤ P.condition * P.beta * (P.dimension : ℝ) := by
    have := P.condition_ge_one
    have := P.beta_pos
    positivity
  have hR : 0 ≤ R := mul_nonneg P.step_pos.le (Real.sqrt_nonneg _)
  have hRsq : R ^ 2 = P.step ^ 2 * (P.condition * P.beta * P.dimension) := by
    dsimp [R]
    rw [mul_pow, Real.sq_sqrt hbase]
  have hfloor : P.energyFloor = 19 * R ^ 2 := by
    rw [hRsq]
    unfold Parameters.energyFloor
    ring
  have hgR : P.correctorBudget ≤ R ^ 2 := by
    rw [hRsq]
    have h := mul_le_mul_of_nonneg_right P.condition_ge_one P.correctorBudget_nonneg
    dsimp [Parameters.correctorBudget] at h ⊢
    nlinarith
  have hnormU : ‖z + g‖ ≤ 5 * R := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) hR)).mp
    rw [hfloor] at hu
    nlinarith [sq_nonneg R]
  have hnormG : ‖g‖ ≤ R :=
    (sq_le_sq₀ (norm_nonneg _) hR).mp (hg.trans hgR)
  have htri : ‖z‖ ≤ ‖z + g‖ + ‖g‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (z + g) g
  change ‖z‖ ≤ 6 * P.step * Real.sqrt (P.condition * P.beta * P.dimension)
  change ‖z + g‖ ≤ 5 * R at hnormU
  have : ‖z‖ ≤ 6 * R := by linarith
  simpa only [R, mul_assoc] using this

end WassersteinMixing
