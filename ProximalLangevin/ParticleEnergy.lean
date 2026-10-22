import ProximalLangevin.Algorithms
import ProximalLangevin.ProximalEnergy
import Mathlib.Algebra.Order.Chebyshev

set_option linter.style.header false

/-! # The averaged pairwise proximal energy inequality

PIPGLA averages the parameter coordinates of separate joint proximal points.
That operation need not be the proximal point of the lifted sum. Jensen's
inequality supplies the squared-distance comparison actually needed by the
energy argument.
-/


noncomputable section
open scoped BigOperators

namespace ProximalLangevin

/-- Jensen's inequality for an average of real coordinates. -/
theorem average_sq_le (N : ℕ) (hN : 0 < N) (b : Fin N → ℝ) :
    (N : ℝ) * ((N : ℝ)⁻¹ * ∑ i, b i) ^ 2 ≤ ∑ i, (b i) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have h := sum_div_card_sq_le_sum_sq_div_card
    (s := (Finset.univ : Finset (Fin N))) (f := b)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hmul := mul_le_mul_of_nonneg_left h hn.le
  simpa [div_eq_mul_inv, mul_comm, hn.ne'] using hmul

/-- Squared distance of the actual averaged output is bounded by the average
of the separate pairwise squared distances. This holds for every joint map. -/
theorem pairwiseMap_sq_dist_le {N dθ dx : ℕ} (hN : 0 < N)
    (P : IPLA.Joint dθ dx → IPLA.Joint dθ dx)
    (z a : IPLA.State N dθ dx) :
    ‖pairwiseMap P z - a‖ ^ 2 ≤
      (∑ i : Fin N, ‖P (IPLA.joint i z) - IPLA.joint i a‖ ^ 2) / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hs2 := Real.sq_sqrt hn.le
  have hθ (j : Fin dθ) :
      (N : ℝ) * ((N : ℝ)⁻¹ * (∑ i : Fin N,
        P (IPLA.joint i z) (Sum.inl j)) - a (Sum.inl j)) ^ 2 ≤
      ∑ i : Fin N, (P (IPLA.joint i z) (Sum.inl j) - a (Sum.inl j)) ^ 2 := by
    have hid : (N : ℝ)⁻¹ * (∑ i : Fin N,
        P (IPLA.joint i z) (Sum.inl j)) - a (Sum.inl j) =
        (N : ℝ)⁻¹ * ∑ i : Fin N,
          (P (IPLA.joint i z) (Sum.inl j) - a (Sum.inl j)) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [hid]
    exact average_sq_le N hN _
  have hx (i : Fin N) (j : Fin dx) :
      (N : ℝ) * ((Real.sqrt N)⁻¹ * P (IPLA.joint i z) (Sum.inr j) -
        a (Sum.inr (i, j))) ^ 2 =
      (P (IPLA.joint i z) (Sum.inr j) - Real.sqrt N * a (Sum.inr (i, j))) ^ 2 := by
    have hid : Real.sqrt N * ((Real.sqrt N)⁻¹ *
        P (IPLA.joint i z) (Sum.inr j) - a (Sum.inr (i, j))) =
        P (IPLA.joint i z) (Sum.inr j) - Real.sqrt N * a (Sum.inr (i, j)) := by
      field_simp
    have hh := congrArg (fun x : ℝ ↦ x ^ 2) hid
    rw [mul_pow, hs2] at hh
    exact hh
  apply (le_div_iff₀ hn).mpr
  rw [mul_comm]
  simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
    Fintype.sum_prod_type, PiLp.sub_apply, pairwiseMap_parameter, pairwiseMap_particle,
    IPLA.joint_parameter, IPLA.joint_particle, Finset.sum_add_distrib,
    mul_add, Finset.mul_sum]
  simp_rw [hx]
  rw [Finset.sum_comm (f := fun i : Fin N ↦ fun j : Fin dθ ↦
    (P (IPLA.joint i z) (Sum.inl j) - a (Sum.inl j)) ^ 2)]
  refine add_le_add ?_ (le_refl _)
  apply Finset.sum_le_sum
  intro j _
  simpa only [Finset.mul_sum] using hθ j

/-- The actual averaged pairwise proximal update satisfies the lifted energy
estimate for the original nonsmooth potential. This proves the bridge needed
in v3 Corollary A.13 directly, without a false `prox`-of-a-sum identity.

The bound only needs one bounded subgradient at each pair input. In
particular the paper's bound on the least-norm subgradient supplies this
hypothesis whenever that minimal section is available. -/
theorem pairwise_prox_energy_le {N dθ dx : ℕ} (hN : 0 < N)
    {g : IPLA.Joint dθ dx → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (hb : ∃ b : ℝ, ∀ x, b ≤ g x) {lam : ℝ} (hlam : 0 < lam)
    (z a : IPLA.State N dθ dx) (C : ℝ)
    (hsub : ∀ i : Fin N, ∃ s : IPLA.Joint dθ dx,
      IsSubgradient g (IPLA.joint i z) s ∧ ‖s‖ ^ 2 ≤ C) :
    ‖pairwiseMap (prox g lam) z - a‖ ^ 2 ≤
      ‖z - a‖ ^ 2 - (2 * lam / N) *
        (IPLA.potential g z - IPLA.potential g a) + lam ^ 2 * C := by
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have heach (i : Fin N) :
      ‖prox g lam (IPLA.joint i z) - IPLA.joint i a‖ ^ 2 ≤
        ‖IPLA.joint i z - IPLA.joint i a‖ ^ 2 -
          2 * lam * (g (IPLA.joint i z) - g (IPLA.joint i a)) + lam ^ 2 * C := by
    obtain ⟨s, hs, hC⟩ := hsub i
    exact prox_energy_le_of_subgradient_bound hg hb hlam hs hC (IPLA.joint i a)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ heach i)
  simp only [← IPLA.joint_sub, IPLA.joint_norm_sq_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  calc
    _ ≤ (∑ i : Fin N, ‖prox g lam (IPLA.joint i z) - IPLA.joint i a‖ ^ 2) / N :=
      pairwiseMap_sq_dist_le hN _ z a
    _ ≤ ((N : ℝ) * ‖z - a‖ ^ 2 -
        2 * lam * (IPLA.potential g z - IPLA.potential g a) +
        (N : ℝ) * (lam ^ 2 * C)) / N :=
      div_le_div_of_nonneg_right (by
        simpa only [IPLA.potential, mul_assoc, mul_left_comm, mul_comm] using hsum) hn.le
    _ = _ := by field_simp

end ProximalLangevin
