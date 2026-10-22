import ProximalLangevin.ParticleEnergy
import ProximalLangevin.SplittingMoments

/-!
# Energy ingredients for the actual averaged proximal splitting

All proximal points below are the actual quadratic minimizers. Global
Lipschitzness supplies the nonsmooth energy remainder directly, avoiding
any premise about a convergence estimate or an input subgradient selection.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace BigOperators
namespace ProximalLangevin

section ProximalEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The proximal energy inequality follows directly from a Lipschitz potential. -/
theorem isProxPoint_energy_le_of_lipschitz {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {lam : ℝ} (hlam : 0 < lam)
    {K : ℝ≥0} (hK : LipschitzWith K f) {x p : E}
    (hp : IsProxPoint f lam x p) (a : E) :
    ‖p - a‖ ^ 2 ≤ ‖x - a‖ ^ 2 - 2 * lam * (f x - f a) + lam ^ 2 * (K : ℝ) ^ 2 := by
  have hs := subgradient_of_isProxPoint hf hlam hp a
  rw [show a - p = -(p - a) by abel, real_inner_smul_left, inner_neg_right] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hlam.le
  simp only [mul_add, mul_neg, ← mul_assoc, mul_inv_cancel₀ hlam.ne', one_mul] at hscaled
  have hd := hK.dist_le_mul x p
  rw [Real.dist_eq, dist_eq_norm_sub] at hd
  have hdiff : f x - f p ≤ (K : ℝ) * ‖x - p‖ := (le_abs_self _).trans hd
  have hnorm : ‖x - a‖ ^ 2 = ‖x - p‖ ^ 2 + 2 * ⟪x - p, p - a⟫ + ‖p - a‖ ^ 2 := by
    rw [show x - a = (x - p) + (p - a) by abel, norm_add_sq_real]
  nlinarith [sq_nonneg (‖x - p‖ - lam * (K : ℝ)),
    mul_le_mul_of_nonneg_left hdiff hlam.le]

end ProximalEnergy

/-- The nonsmooth energy bound for the actual averaged pairwise proximal map,
with a global Lipschitz hypothesis instead of an assumed subgradient selection. -/
theorem pairwise_prox_energy_le_lipschitz {N dθ dx : ℕ} (hN : 0 < N)
    {g : IPLA.Joint dθ dx → ℝ} (hg : ConvexOn ℝ univ g)
    (hb : ∃ b, ∀ x, b ≤ g x) {lam : ℝ} (hlam : 0 < lam)
    {K : ℝ≥0} (hK : LipschitzWith K g) (z a : IPLA.State N dθ dx) :
    ‖pairwiseMap (prox g lam) z - a‖ ^ 2 ≤
      ‖z - a‖ ^ 2 - (2 * lam / N) * (IPLA.potential g z - IPLA.potential g a) +
        lam ^ 2 * (K : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have heach (i : Fin N) := isProxPoint_energy_le_of_lipschitz hg hlam hK
    (prox_isProxPoint hg hb hlam (IPLA.joint i z)) (IPLA.joint i a)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
  simp only [← IPLA.joint_sub, IPLA.joint_norm_sq_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  calc
    _ ≤ (∑ i : Fin N, ‖prox g lam (IPLA.joint i z) - IPLA.joint i a‖ ^ 2) / N :=
      pairwiseMap_sq_dist_le hN _ z a
    _ ≤ ((N : ℝ) * ‖z - a‖ ^ 2 -
        2 * lam * (IPLA.potential g z - IPLA.potential g a) +
        (N : ℝ) * (lam ^ 2 * (K : ℝ) ^ 2)) / N :=
      div_le_div_of_nonneg_right (by
        simpa only [IPLA.potential, mul_assoc, mul_left_comm, mul_comm] using hsum) hn.le
    _ = _ := by field_simp

/-- The averaged lifted potential in the physical-time Langevin equation. -/
def averagedPotential {N dθ dx : ℕ} (g : IPLA.Joint dθ dx → ℝ)
    (z : IPLA.State N dθ dx) : ℝ := (N : ℝ)⁻¹ * IPLA.potential g z

/-- Average pair distances are controlled by the scaled state norm. -/
theorem average_joint_norm_le {N dθ dx : ℕ} (hN : 0 < N)
    (z : IPLA.State N dθ dx) :
    (N : ℝ)⁻¹ * ∑ i : Fin N, ‖IPLA.joint i z‖ ≤ ‖z‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq := average_sq_le N hN (fun i => ‖IPLA.joint i z‖)
  rw [IPLA.joint_norm_sq_sum] at hsq
  have hnonneg : 0 ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, ‖IPLA.joint i z‖ := by positivity
  have hsq2 := (mul_le_mul_iff_of_pos_left hn).mp hsq
  nlinarith [norm_nonneg z]

/-- Averaging in the scaled coordinates preserves the pair potential's Lipschitz constant. -/
theorem averagedPotential_lipschitz {N dθ dx : ℕ} (hN : 0 < N)
    {g : IPLA.Joint dθ dx → ℝ} {K : ℝ≥0} (hK : LipschitzWith K g) :
    LipschitzWith K (averagedPotential (N := N) g) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  rw [Real.dist_eq, dist_eq_norm_sub]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have heq : averagedPotential g z - averagedPotential g w =
      (N : ℝ)⁻¹ * ∑ i : Fin N, (g (IPLA.joint i z) - g (IPLA.joint i w)) := by
    simp [averagedPotential, IPLA.potential, Finset.sum_sub_distrib, mul_sub]
  rw [heq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, |g (IPLA.joint i z) - g (IPLA.joint i w)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ i : Fin N, (K : ℝ) * ‖IPLA.joint i (z - w)‖ := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hn.le)
      apply Finset.sum_le_sum
      intro i _
      simpa only [dist_eq_norm_sub, Real.norm_eq_abs, ← IPLA.joint_sub] using
        hK.dist_le_mul (IPLA.joint i z) (IPLA.joint i w)
    _ = (K : ℝ) * ((N : ℝ)⁻¹ * ∑ i : Fin N, ‖IPLA.joint i (z - w)‖) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (K : ℝ) * ‖z - w‖ := mul_le_mul_of_nonneg_left
      (average_joint_norm_le hN (z - w)) K.coe_nonneg

end ProximalLangevin
