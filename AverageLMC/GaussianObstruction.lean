import KineticLangevin.GaussianFourth
import UnadjustedLangevin.LSI.GaussianDrift

set_option linter.style.header false

/-! # Gaussian probability component of the GLM obstruction

The manuscript's Gaussian design proposition claims a dimension independent
upper bound of order `n` for the Hessian Lipschitz seminorm when `n = p`.
The allowed rank-one perturbation described in `GLMObstruction` forces that
seminorm to be at least the cube of the first design vector's norm.
This file proves that such cubes cannot be bounded by `C * p` with probability
one half uniformly in dimension. The law is the actual standard Gaussian.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace AverageLMC

/-- Exact variance of the squared norm of a standard Gaussian vector. -/
theorem stdGaussian_norm_sq_variance (p : ℕ) :
    variance (fun z : EuclideanSpace ℝ (Fin p) ↦ ‖z‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin p))) = 2 * (p : ℝ) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin p))
  have hfour : Integrable (fun z : EuclideanSpace ℝ (Fin p) ↦ ‖z‖ ^ 4) μ :=
    (IsGaussian.memLp_id μ 4 (by norm_num)).integrable_norm_pow (by norm_num)
  have htwo : MemLp (fun z : EuclideanSpace ℝ (Fin p) ↦ ‖z‖ ^ 2) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    simpa only [← pow_mul] using hfour
  rw [variance_eq_sub htwo]
  have hmean : (∫ z : EuclideanSpace ℝ (Fin p), ‖z‖ ^ 2 ∂μ) = (p : ℝ) := by
    simpa [μ] using
      (ULA.LSI.integral_norm_sq_stdGaussian (E := EuclideanSpace ℝ (Fin p)))
  have hsecond : (∫ z : EuclideanSpace ℝ (Fin p), (‖z‖ ^ 2) ^ 2 ∂μ) =
      (p : ℝ) ^ 2 + 2 * (p : ℝ) := by
    simpa only [← pow_mul, Fintype.card_fin] using
      (KineticLangevin.stdGaussian_norm_fourth_moment (Fin p))
  change (∫ z : EuclideanSpace ℝ (Fin p), (‖z‖ ^ 2) ^ 2 ∂μ) -
    (∫ z : EuclideanSpace ℝ (Fin p), ‖z‖ ^ 2 ∂μ) ^ 2 = _
  rw [hmean, hsecond]
  ring

/-- Chebyshev bounds the small-norm probability by `8 / p`. -/
theorem stdGaussian_small_norm (p : ℕ) (hp : 0 < p) :
    stdGaussian (EuclideanSpace ℝ (Fin p)) {z | ‖z‖ ^ 2 < (p : ℝ) / 2} ≤
      ENNReal.ofReal (8 / (p : ℝ)) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin p))
  have hfour : Integrable (fun z : EuclideanSpace ℝ (Fin p) ↦ ‖z‖ ^ 4) μ :=
    (IsGaussian.memLp_id μ 4 (by norm_num)).integrable_norm_pow (by norm_num)
  have htwo : MemLp (fun z : EuclideanSpace ℝ (Fin p) ↦ ‖z‖ ^ 2) 2 μ := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
    simpa only [← pow_mul] using hfour
  have hmean : (∫ z : EuclideanSpace ℝ (Fin p), ‖z‖ ^ 2 ∂μ) = (p : ℝ) := by
    simpa [μ] using
      (ULA.LSI.integral_norm_sq_stdGaussian (E := EuclideanSpace ℝ (Fin p)))
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hc := meas_ge_le_variance_div_sq htwo (half_pos hp')
  rw [hmean, stdGaussian_norm_sq_variance] at hc
  have hsub : {z : EuclideanSpace ℝ (Fin p) | ‖z‖ ^ 2 < (p : ℝ) / 2} ⊆
      {z | (p : ℝ) / 2 ≤ |‖z‖ ^ 2 - (p : ℝ)|} := by
    intro z hz
    change ‖z‖ ^ 2 < (p : ℝ) / 2 at hz
    change (p : ℝ) / 2 ≤ |‖z‖ ^ 2 - (p : ℝ)|
    have h' := neg_le_abs (‖z‖ ^ 2 - (p : ℝ))
    linarith
  refine (measure_mono hsub).trans (hc.trans_eq ?_)
  congr 1
  field_simp
  ring

/-- Every proposed constant `C` fails in every sufficiently large dimension.
This is an actual Gaussian probability statement, without a moment premise. -/
theorem stdGaussian_cube_bound_fails (p : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hp : 16 < p) (hlarge : 8 * C ^ 2 < (p : ℝ)) :
    stdGaussian (EuclideanSpace ℝ (Fin p)) {z | ‖z‖ ^ 3 ≤ C * (p : ℝ)} <
      (1 / 2 : ℝ≥0∞) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast (lt_trans (by decide : 0 < 16) hp)
  have hsub : {z : EuclideanSpace ℝ (Fin p) | ‖z‖ ^ 3 ≤ C * (p : ℝ)} ⊆
      {z | ‖z‖ ^ 2 < (p : ℝ) / 2} := by
    intro z hz
    by_contra hn
    have hnorm := norm_nonneg z
    have hsq : (p : ℝ) / 2 ≤ ‖z‖ ^ 2 := le_of_not_gt hn
    have hcube : (p : ℝ) ^ 3 / 8 ≤ (‖z‖ ^ 3) ^ 2 := by
      have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (p : ℝ) / 2) hsq 3
      nlinarith [hpow]
    have hupper := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ ‖z‖ ^ 3)
      (mul_nonneg hC hp'.le)).mpr hz
    have hstrict := mul_lt_mul_of_pos_right hlarge (sq_pos_of_pos hp')
    nlinarith
  have hsmall := stdGaussian_small_norm p (by omega)
  refine ((measure_mono hsub).trans hsmall).trans_lt ?_
  have hratio : 8 / (p : ℝ) < 1 / 2 := by
    apply (div_lt_iff₀ hp').mpr
    have : (16 : ℝ) < p := by exact_mod_cast hp
    linarith
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr hratio

/-- No dimension independent constant can make the cubic norm bound hold
with probability at least one half for every standard Gaussian dimension. -/
theorem no_uniform_stdGaussian_cube_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ,
      (1 / 2 : ℝ≥0∞) ≤ stdGaussian (EuclideanSpace ℝ (Fin p))
        {z | ‖z‖ ^ 3 ≤ C * (p : ℝ)} := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨p, hp⟩ := exists_nat_gt (max 16 (8 * C ^ 2))
  have hp16 : 16 < p := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hp)
  have hpC : 8 * C ^ 2 < (p : ℝ) := lt_of_le_of_lt (le_max_right _ _) hp
  exact (stdGaussian_cube_bound_fails p C hC hp16 hpC).not_ge (hbound p)

end AverageLMC
