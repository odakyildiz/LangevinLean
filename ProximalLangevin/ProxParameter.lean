import ProximalLangevin.SplittingContraction
import UnadjustedLangevin.Recurrence

/-! # Sensitivity to the actual proximal parameter

These estimates compare two actual PIPGLA recursions driven by the same
Gaussian path. They let an equal-step convergence theorem be transferred to
a different proximal parameter without assuming a new law recurrence.
-/

set_option linter.style.header false

noncomputable section
open Set
open scoped NNReal RealInnerProductSpace BigOperators

namespace ProximalLangevin

/-- A bounded genuine subgradient at every input implies global Lipschitzness.
In particular, the paper's uniformly bounded minimal section supplies this
hypothesis, without adding a separate Lipschitz assumption to C1. -/
theorem lipschitz_of_bounded_subgradients {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f : E → ℝ} {K : ℝ≥0}
    (hsub : ∀ x, ∃ s, IsSubgradient f x s ∧ ‖s‖ ≤ (K : ℝ)) :
    LipschitzWith K f := by
  have hupper (x y : E) : f x - f y ≤ (K : ℝ) * ‖x - y‖ := by
    obtain ⟨s, hs, hK⟩ := hsub x
    have hsupport := hs y
    rw [show y - x = -(x - y) by abel, inner_neg_right] at hsupport
    have hinner : ⟪s, x - y⟫ ≤ (K : ℝ) * ‖x - y‖ :=
      (real_inner_le_norm s (x - y)).trans
        (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm_sub]
  apply abs_le.mpr
  constructor
  · have h := hupper y x
    rw [norm_sub_rev y x] at h
    linarith
  · exact hupper x y

/-- The actual proximal point changes by at most `K*|lam-eta|` when the
positive smoothing parameter changes. -/
theorem prox_parameter_sensitivity {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf : ConvexOn ℝ univ f) (hb : ∃ b : ℝ, ∀ x, b ≤ f x)
    {K : ℝ≥0} (hK : LipschitzWith K f) {lam eta : ℝ}
    (hlam : 0 < lam) (heta : 0 < eta) (x : E) :
    ‖prox f lam x - prox f eta x‖ ≤ (K : ℝ) * |lam - eta| := by
  let q := prox f eta x
  let s := residual f eta x
  have hs : IsSubgradient f q s := subgradient_of_isProxPoint hf heta
    (prox_isProxPoint hf hb heta x)
  have hsNorm : ‖s‖ ≤ (K : ℝ) := residual_norm_le hf hb heta hK x
  have hq : IsProxPoint f lam (q + lam • s) q := by
    apply isProxPoint_of_subgradient hlam
    simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]
      using hs
  have hnonexp := (prox_isProxPoint hf hb hlam x).nonexpansive hf hlam hq
  have hxs : x - q = eta • s := by
    dsimp only [q, s, residual]
    rw [smul_smul, mul_inv_cancel₀ heta.ne', one_smul]
  have hid : x - (q + lam • s) = (eta - lam) • s := by
    rw [show x - (q + lam • s) = (x - q) - lam • s by abel, hxs, sub_smul]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_sub_comm eta lam] at hnonexp
  exact hnonexp.trans (by simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hsNorm (abs_nonneg (lam - eta)))

/-- Pairwise averaging is linear in the supplied joint map. -/
theorem pairwiseMap_sub {N dθ dx : ℕ}
    (P Q : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (z : IPLA.State N dθ dx) :
    pairwiseMap (fun x => P x - Q x) z = pairwiseMap P z - pairwiseMap Q z := by
  ext a
  rcases a with j | ⟨i, j⟩
  · simp only [pairwiseMap_parameter, PiLp.sub_apply, Finset.sum_sub_distrib, mul_sub]
  · simp only [pairwiseMap_particle, PiLp.sub_apply, mul_sub]

/-- A uniform difference of joint maps stays uniformly bounded after the
common-parameter averaging and latent-coordinate scaling. -/
theorem pairwiseMap_uniform_difference_le {N dθ dx : ℕ} (hN : 0 < N)
    (P Q : IPLA.Joint dθ dx → IPLA.Joint dθ dx) (c : ℝ) (hc : 0 ≤ c)
    (hPQ : ∀ x, ‖P x - Q x‖ ≤ c) (z : IPLA.State N dθ dx) :
    ‖pairwiseMap P z - pairwiseMap Q z‖ ≤ c := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hgeom := pairwiseMap_sq_dist_le hN (fun x => P x - Q x) z 0
  rw [pairwiseMap_sub] at hgeom
  have hzero (i : Fin N) : IPLA.joint i (0 : IPLA.State N dθ dx) = 0 := by
    ext a
    cases a <;> simp [IPLA.joint]
  simp only [sub_zero, hzero] at hgeom
  have hsum : (∑ i : Fin N, ‖P (IPLA.joint i z) - Q (IPLA.joint i z)‖ ^ 2) ≤
      (N : ℝ) * c ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin N, c ^ 2 := Finset.sum_le_sum (fun i _ => by
        have h := hPQ (IPLA.joint i z)
        nlinarith [norm_nonneg (P (IPLA.joint i z) - Q (IPLA.joint i z))])
      _ = _ := by simp
  have hsq : ‖pairwiseMap P z - pairwiseMap Q z‖ ^ 2 ≤ c ^ 2 := by
    calc
      _ ≤ _ := hgeom
      _ ≤ ((N : ℝ) * c ^ 2) / N := div_le_div_of_nonneg_right hsum hn.le
      _ = c ^ 2 := by field_simp
  nlinarith [norm_nonneg (pairwiseMap P z - pairwiseMap Q z)]

/-- The proximal-parameter sensitivity has no particle-number loss. -/
theorem pairwise_prox_parameter_sensitivity {N dθ dx : ℕ} (hN : 0 < N)
    {g₂ : IPLA.Joint dθ dx → ℝ} (hg₂ : ConvexOn ℝ univ g₂)
    (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z) {K : ℝ≥0} (hK : LipschitzWith K g₂)
    {lam eta : ℝ} (hlam : 0 < lam) (heta : 0 < eta) (z : IPLA.State N dθ dx) :
    ‖pairwiseMap (prox g₂ lam) z - pairwiseMap (prox g₂ eta) z‖ ≤
      (K : ℝ) * |lam - eta| :=
  pairwiseMap_uniform_difference_le hN _ _ _ (by positivity)
    (prox_parameter_sensitivity hg₂ hb hK hlam heta) z

/-- One step of two actual splitting schemes with different proximal
parameters, the same time step, and the same supplied innovation. -/
theorem pipglaUpdate_parameter_comparison {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m γ lam eta : ℝ) (L₁ K : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hK : LipschitzWith K g₂) (hm : 0 < m) (hmL : m ≤ (L₁ : ℝ))
    (hγ : 0 ≤ γ) (hlam : 0 < lam) (heta : 0 < eta)
    (hsmall : γ ≤ 2 / (m + (L₁ : ℝ))) (z w ξ : IPLA.State N dθ dx) :
    ‖pipglaUpdate g₁ (prox g₂ lam) γ z ξ - pipglaUpdate g₁ (prox g₂ eta) γ w ξ‖ ≤
      (1 - m * γ) * ‖z - w‖ + (K : ℝ) * |lam - eta| := by
  calc
    _ ≤ ‖pipglaUpdate g₁ (prox g₂ lam) γ z ξ -
        pipglaUpdate g₁ (prox g₂ lam) γ w ξ‖ +
        ‖pipglaUpdate g₁ (prox g₂ lam) γ w ξ -
          pipglaUpdate g₁ (prox g₂ eta) γ w ξ‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (pipglaUpdate g₁ (prox g₂ lam) γ z ξ)
        (pipglaUpdate g₁ (prox g₂ lam) γ w ξ)
        (pipglaUpdate g₁ (prox g₂ eta) γ w ξ)
    _ ≤ (1 - m * γ) * ‖z - w‖ + (K : ℝ) * |lam - eta| :=
      add_le_add (pipglaUpdate_shared_noise_contract hN m γ lam L₁ hg₁ hsc hLip
        hg₂ hb hm hmL hγ hlam hsmall z w ξ)
        (pairwise_prox_parameter_sensitivity hN hg₂ hb hK hlam heta _)

/-- Exact finite-horizon comparison of two actual splitting recursions. -/
theorem pipglaChain_parameter_comparison_sum {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m γ lam eta : ℝ) (L₁ K : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hK : LipschitzWith K g₂) (hm : 0 < m) (hmL : m ≤ (L₁ : ℝ))
    (hγ : 0 ≤ γ) (hlam : 0 < lam) (heta : 0 < eta)
    (hsmall : γ ≤ 2 / (m + (L₁ : ℝ)))
    (z w : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) (n : ℕ) :
    ‖pipglaChain g₁ (prox g₂ lam) γ z noise n -
      pipglaChain g₁ (prox g₂ eta) γ w noise n‖ ≤
      (1 - m * γ) ^ n * ‖z - w‖ +
        ((K : ℝ) * |lam - eta|) * ∑ j ∈ Finset.range n, (1 - m * γ) ^ j := by
  let e := fun k => ‖pipglaChain g₁ (prox g₂ lam) γ z noise k -
    pipglaChain g₁ (prox g₂ eta) γ w noise k‖
  have hden : 0 < m + (L₁ : ℝ) := by positivity
  have hmul := (le_div_iff₀ hden).mp hsmall
  have hq : 0 ≤ 1 - m * γ := by nlinarith
  have hstep (k : ℕ) : e (k + 1) ≤ (1 - m * γ) * e k + (K : ℝ) * |lam - eta| :=
    pipglaUpdate_parameter_comparison hN m γ lam eta L₁ K hg₁ hsc hLip hg₂ hb hK
      hm hmL hγ hlam heta hsmall _ _ _
  have h := ULA.affine_recurrence_sum e _ _ hq hstep n
  simpa only [e, pipglaChain, algorithmChain_zero] using h

/-- The resulting pathwise difference floor is valid for any two positive
proximal parameters; it is not assumed to be an algorithm error bound. -/
theorem pipglaChain_parameter_comparison_bound {N dθ dx : ℕ} (hN : 0 < N)
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} (m γ lam eta : ℝ) (L₁ K : ℝ≥0)
    (hg₁ : Differentiable ℝ g₁) (hsc : StrongConvexOn univ m g₁)
    (hLip : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b : ℝ, ∀ z, b ≤ g₂ z)
    (hK : LipschitzWith K g₂) (hm : 0 < m) (hmL : m ≤ (L₁ : ℝ))
    (hγ : 0 < γ) (hlam : 0 < lam) (heta : 0 < eta)
    (hsmall : γ ≤ 2 / (m + (L₁ : ℝ)))
    (z w : IPLA.State N dθ dx) (noise : ℕ → IPLA.State N dθ dx) (n : ℕ) :
    ‖pipglaChain g₁ (prox g₂ lam) γ z noise n -
      pipglaChain g₁ (prox g₂ eta) γ w noise n‖ ≤
      (1 - m * γ) ^ n * ‖z - w‖ + (K : ℝ) * |lam - eta| / (m * γ) := by
  let e := fun k => ‖pipglaChain g₁ (prox g₂ lam) γ z noise k -
    pipglaChain g₁ (prox g₂ eta) γ w noise k‖
  have hden : 0 < m + (L₁ : ℝ) := by positivity
  have hmul := (le_div_iff₀ hden).mp hsmall
  have hq : 0 ≤ 1 - m * γ := by nlinarith
  have hq1 : 1 - m * γ < 1 := by nlinarith [mul_pos hm hγ]
  have hstep (k : ℕ) : e (k + 1) ≤ (1 - m * γ) * e k + (K : ℝ) * |lam - eta| :=
    pipglaUpdate_parameter_comparison hN m γ lam eta L₁ K hg₁ hsc hLip hg₂ hb hK
      hm hmL hγ.le hlam heta hsmall _ _ _
  have h := ULA.affine_recurrence_bound e _ _ hq hq1 (by positivity) hstep n
  simpa only [e, pipglaChain, algorithmChain_zero, show 1 - (1 - m * γ) = m * γ by ring]
    using h

/-- In the paper's proximal-parameter corridor, the additional comparison
floor against `eta=γ` is of order `γ`, with every denominator displayed. -/
theorem prox_parameter_corridor_floor (m γ lam : ℝ) (K : ℝ≥0)
    (hm : 0 < m) (hγ : 0 < γ) (hmg : m * γ < 1)
    (hlo : γ ≤ lam) (hhi : lam ≤ γ / (1 - m * γ)) :
    (K : ℝ) * |lam - γ| / (m * γ) ≤ (K : ℝ) * γ / (1 - m * γ) := by
  have hd : 0 < 1 - m * γ := sub_pos.mpr hmg
  have hh := (le_div_iff₀ hd).mp hhi
  have hK := mul_le_mul_of_nonneg_left hh K.coe_nonneg
  rw [abs_of_nonneg (sub_nonneg.mpr hlo), div_le_div_iff₀ (mul_pos hm hγ) hd]
  nlinarith

end ProximalLangevin
