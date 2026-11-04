import WassersteinMixing.CurvatureAssumptions
import IPLA.Geometry

set_option linter.style.header false

/-! # The exact curvature and step scaling for the IPLA application

The lifted potential and its reindexing satisfy the hypotheses of the sharp
Wasserstein theorem as consequences of the original joint-potential bounds.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace WassersteinMixing

/-- The exact ULA parameters of the scaled IPLA state. -/
def iplaParameters (N dθ dx : ℕ) (m L γ : ℝ) (hN : 0 < N)
    (hm : 0 < m) (hmL : m ≤ L) (hγ : 0 < γ) (hγL : γ * L ≤ 1) : Parameters where
  alpha := N * m
  beta := N * L
  step := γ / N
  dimension := dθ + N * dx
  alpha_pos := mul_pos (by exact_mod_cast hN) hm
  alpha_le_beta := mul_le_mul_of_nonneg_left hmL (Nat.cast_nonneg N)
  step_pos := div_pos hγ (by exact_mod_cast hN)
  step_beta_le := by
    have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
    have heq : γ / (N : ℝ) * ((N : ℝ) * L) = γ * L := by field_simp [hn]
    rw [heq]
    exact hγL

/-- A finite sum of joint potentials stays twice continuously differentiable
under the actual scaled pair-extraction maps. -/
theorem ipla_potential_contDiff {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    (hU : ContDiff ℝ 2 U) : ContDiff ℝ 2 (@IPLA.potential N dθ dx U) := by
  exact ContDiff.sum (fun i _ ↦ hU.comp (IPLA.jointCLM i).contDiff)

/-- A linear isometric change of coordinates transports the true gradient. -/
theorem gradient_reindex
    {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (e : H ≃ₗᵢ[ℝ] F) (V : H → ℝ) (hV : Differentiable ℝ V) (x : F) :
    gradient (V ∘ e.symm) x = e (gradient V (e.symm x)) := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left, e.inner_map_eq_flip, inner_gradient_left]
  rw [((hV (e.symm x)).hasFDerivAt.comp x
    e.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv]
  rfl

/-- Isometric reindexing preserves the exact potential contract, including the
curvature constants, without any additional regularity hypothesis. -/
theorem potentialAssumptions_reindex
    {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (P : Parameters) (e : H ≃ₗᵢ[ℝ] F) (V : H → ℝ)
    (hV : PotentialAssumptions P V) : PotentialAssumptions P (V ∘ e.symm) where
  regularity := hV.regularity.comp e.symm.contDiff
  strongConvexity := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    simpa only [Function.comp_apply, map_add, map_smul, ← map_sub, e.symm.norm_map]
      using hV.strongConvexity.2 (mem_univ (e.symm x)) (mem_univ (e.symm y)) ha hb hab
  gradientLipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [gradient_reindex e V (hV.regularity.differentiable (by norm_num)),
      gradient_reindex e V (hV.regularity.differentiable (by norm_num)), e.dist_map]
    simpa only [e.symm.dist_map] using hV.gradientLipschitz.dist_le_mul (e.symm x) (e.symm y)

/-- The ordinary twice differentiable strong-convexity and gradient-smoothness
hypotheses imply the exact lifted contract. -/
theorem ipla_potentialAssumptions
    {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ} {m γ : ℝ} {L : ℝ≥0}
    (hN : 0 < N) (hm : 0 < m) (hmL : m ≤ L) (hγ : 0 < γ) (hγL : γ * L ≤ 1)
    (hU : ContDiff ℝ 2 U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) :
    PotentialAssumptions (iplaParameters N dθ dx m L γ hN hm hmL hγ hγL)
      (@IPLA.potential N dθ dx U) where
  regularity := ipla_potential_contDiff hU
  strongConvexity := IPLA.potential_strongConvex hsc
  gradientLipschitz := by
    exact IPLA.potential_gradient_lipschitz (N := N)
      (hU.differentiable (by norm_num)) hLip

/-- The literal joint Hessian bounds imply all of the lifted-potential
assumptions; no invariant-law or stochastic-comparison input is supplied. -/
theorem ipla_potentialAssumptions_of_hessian
    (Q : Parameters) {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    (hU : HessianAssumptions Q U) (hN : 0 < N)
    {γ : ℝ} (hγ : 0 < γ) (hγL : γ * Q.beta ≤ 1) :
    PotentialAssumptions
      (iplaParameters N dθ dx Q.alpha Q.beta γ hN Q.alpha_pos Q.alpha_le_beta hγ hγL)
      (@IPLA.potential N dθ dx U) := by
  exact ipla_potentialAssumptions (L := ⟨Q.beta, Q.beta_pos.le⟩)
    hN Q.alpha_pos Q.alpha_le_beta hγ hγL
    hU.regularity hU.toPotentialAssumptions.strongConvexity
    hU.toPotentialAssumptions.gradientLipschitz

end WassersteinMixing
