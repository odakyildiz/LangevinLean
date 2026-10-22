import ProximalLangevin.ParticleEnergy
import ProximalLangevin.Moreau
import IPLA.Scaling
import UnadjustedLangevin.SharpContraction

set_option linter.style.header false

/-! # Shared-noise contraction of the actual proximal particle recursion

This is a pathwise comparison between two runs of PIPGLA. It is not a
statement that either run converges to the Gibbs target. The pairwise map
is handled by Jensen's inequality, without a lifted-proximal identity.
-/

noncomputable section
open scoped NNReal

namespace ProximalLangevin

/-- Averaging only the shared parameter contracts the squared difference
relative to the average of all separate pairwise squared differences. -/
theorem pairwiseMap_difference_sq_le {N dθ dx : ℕ} (hN : 0 < N)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (z w : IPLA.State N dθ dx) :
    ‖pairwiseMap P z - pairwiseMap P w‖ ^ 2 ≤
      (∑ i : Fin N, ‖P (IPLA.joint i z) - P (IPLA.joint i w)‖ ^ 2) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hs2 := Real.sq_sqrt hn.le
  have hθ (j : Fin dθ) :
      (N : ℝ) * ((N : ℝ)⁻¹ * (∑ i : Fin N, P (IPLA.joint i z) (Sum.inl j)) -
        (N : ℝ)⁻¹ * (∑ i : Fin N, P (IPLA.joint i w) (Sum.inl j))) ^ 2 ≤
      ∑ i : Fin N,
        (P (IPLA.joint i z) (Sum.inl j) - P (IPLA.joint i w) (Sum.inl j)) ^ 2 := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    exact average_sq_le N hN _
  have hx (i : Fin N) (j : Fin dx) :
      (N : ℝ) * ((Real.sqrt N)⁻¹ * P (IPLA.joint i z) (Sum.inr j) -
        (Real.sqrt N)⁻¹ * P (IPLA.joint i w) (Sum.inr j)) ^ 2 =
      (P (IPLA.joint i z) (Sum.inr j) - P (IPLA.joint i w) (Sum.inr j)) ^ 2 := by
    rw [← mul_sub, mul_pow, ← mul_assoc]
    have hc : (N : ℝ) * (Real.sqrt N)⁻¹ ^ 2 = 1 := by
      rw [inv_pow, hs2]
      exact mul_inv_cancel₀ hn.ne'
    rw [hc, one_mul]
  apply (le_div_iff₀ hn).mpr
  rw [mul_comm]
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
    Fintype.sum_prod_type, PiLp.sub_apply, pairwiseMap_parameter, pairwiseMap_particle,
    Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  simp_rw [hx]
  rw [Finset.sum_comm (f := fun i : Fin N ↦ fun j : Fin dθ ↦
    (P (IPLA.joint i z) (Sum.inl j) - P (IPLA.joint i w) (Sum.inl j)) ^ 2)]
  apply add_le_add ?_ le_rfl
  exact Finset.sum_le_sum fun j _ ↦ by simpa only [Finset.mul_sum] using hθ j

/-- A nonexpansive pair map remains nonexpansive after the actual shared
parameter averaging and physical-particle scaling. -/
theorem pairwiseMap_nonexpansive {N dθ dx : ℕ} (hN : 0 < N)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (hP : LipschitzWith 1 P)
    (z w : IPLA.State N dθ dx) :
    ‖pairwiseMap P z - pairwiseMap P w‖ ≤ ‖z - w‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := pairwiseMap_difference_sq_le hN P z w
  have hp (i : Fin N) : ‖P (IPLA.joint i z) - P (IPLA.joint i w)‖ ^ 2 ≤
      ‖IPLA.joint i (z - w)‖ ^ 2 := by
    have hi := hP.norm_sub_le (IPLA.joint i z) (IPLA.joint i w)
    simp only [NNReal.coe_one, one_mul, ← IPLA.joint_sub] at hi
    nlinarith [norm_nonneg (P (IPLA.joint i z) - P (IPLA.joint i w)),
      norm_nonneg (IPLA.joint i (z - w))]
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hp i)
  rw [IPLA.joint_norm_sq_sum] at hb
  have hh := (le_div_iff₀ hn).mp h
  have hsq : ‖pairwiseMap P z - pairwiseMap P w‖ ^ 2 ≤ ‖z - w‖ ^ 2 :=
    (mul_le_mul_iff_of_pos_right hn).mp (hh.trans (by simpa [mul_comm] using hb))
  nlinarith [norm_nonneg (pairwiseMap P z - pairwiseMap P w), norm_nonneg (z - w)]

/-- PIPGLA contracts synchronously driven initial states at the smooth
forward-step rate. No stochastic or equilibrium hypothesis is needed. -/
theorem pipglaUpdate_shared_noise_contract {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m γ lam : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn Set.univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ Set.univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hm : 0 < m) (hmL : m ≤ (L₁ : ℝ)) (hγ : 0 ≤ γ) (hlam : 0 < lam)
    (hsmall : γ ≤ 2 / (m + (L₁ : ℝ))) (z w ξ : IPLA.State N dθ dx) :
    ‖pipglaUpdate g₁ (prox g₂ lam) γ z ξ - pipglaUpdate g₁ (prox g₂ lam) γ w ξ‖ ≤
      (1 - m * γ) * ‖z - w‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hstep := (IPLA.scaled_step_iff N hN m (L₁ : ℝ) γ).mpr hsmall
  have hc := ULA.strong_smooth_gradient_step_contract (@IPLA.potential N dθ dx g₁)
    ((N : ℝ) * m) (γ / N) ((N : ℝ≥0) * L₁)
    (IPLA.potential_differentiable hg₁) (IPLA.potential_strongConvex hsc)
    (IPLA.potential_gradient_lipschitz hg₁ hLip)
    (by simpa using mul_le_mul_of_nonneg_left hmL hn.le)
    (by simp only [NNReal.coe_mul, NNReal.coe_natCast]; positivity)
    (div_nonneg hγ hn.le) hstep z w
  have hfactor : (N : ℝ) * m * (γ / N) = m * γ := by field_simp
  rw [hfactor] at hc
  have hp := pairwiseMap_nonexpansive hN (prox g₂ lam) (prox_lipschitz hg₂ hb hlam)
    (IPLA.scaledUpdate g₁ γ z ξ) (IPLA.scaledUpdate g₁ γ w ξ)
  exact hp.trans (by simpa only [IPLA.scaledUpdate, add_sub_add_right_eq_sub] using hc)

/-- Iterating the actual pathwise inequality controls two PIPGLA runs with
the same innovations. It supplies stability, rather than a Gibbs bias bound. -/
theorem pipglaChain_shared_noise_contract {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m γ lam : ℝ) (L₁ : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn Set.univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ Set.univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hm : 0 < m) (hmL : m ≤ (L₁ : ℝ)) (hγ : 0 ≤ γ) (hlam : 0 < lam)
    (hsmall : γ ≤ 2 / (m + (L₁ : ℝ)))
    (z w : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) (k : ℕ) :
    ‖pipglaChain g₁ (prox g₂ lam) γ z noise k -
        pipglaChain g₁ (prox g₂ lam) γ w noise k‖ ≤
      (1 - m * γ) ^ k * ‖z - w‖ := by
  have hden : 0 < m + (L₁ : ℝ) := by positivity
  have hs := (le_div_iff₀ hden).mp hsmall
  have hq : 0 ≤ 1 - m * γ := by nlinarith
  induction k with
  | zero => simp [pipglaChain, algorithmChain]
  | succ k ih =>
    change ‖pipglaUpdate g₁ (prox g₂ lam) γ
        (pipglaChain g₁ (prox g₂ lam) γ z noise k) (noise k) -
      pipglaUpdate g₁ (prox g₂ lam) γ
        (pipglaChain g₁ (prox g₂ lam) γ w noise k) (noise k)‖ ≤ _
    calc
      _ ≤ (1 - m * γ) * ‖pipglaChain g₁ (prox g₂ lam) γ z noise k -
          pipglaChain g₁ (prox g₂ lam) γ w noise k‖ :=
        pipglaUpdate_shared_noise_contract hN m γ lam L₁ hg₁ hsc hLip hg₂ hb
          hm hmL hγ hlam hsmall _ _ _
      _ ≤ (1 - m * γ) * ((1 - m * γ) ^ k * ‖z - w‖) :=
        mul_le_mul_of_nonneg_left ih hq
      _ = _ := by rw [pow_succ]; ring

end ProximalLangevin
