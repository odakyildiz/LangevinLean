import IPLA.StrongLogConcavity
import IPLA.Transport
import UnadjustedLangevin.GibbsConcentration

set_option linter.style.header false

/-! # The complete IPLA equilibrium concentration theorem

This module derives the exact `sqrt (2*dθ/(N*m))` radius from the original joint
potential assumptions. Marginal strong convexity is supplied by the proved
Prékopa theorem; the dimension-sharp moment estimate reuses the shared ULA
continuous-Gibbs dilation theorem. No marginal-concentration or reference-law
hypothesis is introduced.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace IPLA

/-- Multiplying the actual marginal potential by `N` multiplies its proved
strong-convexity constant by `N`. -/
theorem scaled_marginalPotential_strongConvex {N dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    StrongConvexOn Set.univ ((N : ℝ) * m)
      (fun θ ↦ (N : ℝ) * marginalPotential U θ) := by
  refine ⟨convex_univ, ?_⟩
  intro θ hθ θ' hθ' a b ha hb hab
  have h := mul_le_mul_of_nonneg_left
    ((marginalPotential_strongConvex U m hm hdiff hsc).2 hθ hθ' ha hb hab)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  dsimp only at h ⊢
  simp only [smul_eq_mul] at h ⊢
  convert h using 1
  ring

/-- The normalized powered marginal density is exactly the Gibbs law of the
proved `N`-scaled negative log marginal. -/
theorem marginalTarget_eq_gibbsMeasure {N dθ dx : ℕ} (U : Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) :
    marginalTarget N U = ULA.gibbsMeasure (fun θ ↦ (N : ℝ) * marginalPotential U θ) := by
  have hw : ULA.gibbsWeight (fun θ ↦ (N : ℝ) * marginalPotential U θ) =
      fun θ ↦ marginalDensity U θ ^ N := by
    funext θ
    have hz := marginalIntegral_pos U m hm hdiff hsc θ
    have he : Real.exp (-((N : ℝ) * marginalPotential U θ)) = marginalIntegral U θ ^ N := by
      dsimp [marginalPotential]
      rw [mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hz]
    rw [ULA.gibbsWeight, he, ENNReal.ofReal_pow hz.le,
      marginalDensity_eq_ofReal_integral U m hm hdiff hsc θ]
    rfl
  rw [ULA.gibbsMeasure, ULA.gibbsPartition, hw]
  rfl

/-- Exact finite second-moment bound about any parameter maximizing the actual
latent marginal. Its existence and uniqueness were proved separately. -/
theorem marginalTarget_secondMoment_le {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θStar : EuclideanSpace ℝ (Fin dθ))
    (hmax : IsMarginalMaximizer U θStar) :
    (∫ θ, ‖θ - θStar‖ ^ 2 ∂marginalTarget N U) ≤
      2 * (dθ : ℝ) / ((N : ℝ) * m) := by
  have hmode := marginalMaximizer_minimizes_potential U m hm hdiff hsc θStar hmax
  have h := ULA.integral_sq_dist_gibbs_le_of_continuous_strongConvex_mode
    (fun θ ↦ (N : ℝ) * marginalPotential U θ) ((N : ℝ) * m)
    (mul_pos (by exact_mod_cast hN) hm)
    (continuous_const.mul (marginalPotential_continuous U m hm hdiff hsc))
    (scaled_marginalPotential_strongConvex U m hm hdiff hsc) θStar
    (fun θ ↦ mul_le_mul_of_nonneg_left (hmode θ) (Nat.cast_nonneg N))
  rw [← marginalTarget_eq_gibbsMeasure U m hm hdiff hsc] at h
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using h

/-- Transfer the proved marginal moment bound to the actual scaled IPLA Gibbs
measure using the exact parameter-marginal identity. -/
theorem gibbsTarget_parameter_secondMoment_le {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θStar : EuclideanSpace ℝ (Fin dθ))
    (hmax : IsMarginalMaximizer U θStar) :
    (∫ z : State N dθ dx, ‖parameterCLM z - θStar‖ ^ 2 ∂gibbsTarget U) ≤
      2 * (dθ : ℝ) / ((N : ℝ) * m) := by
  have h := marginalTarget_secondMoment_le hN U m hm hdiff hsc θStar hmax
  rw [← gibbsTarget_parameter_marginal hN U m hm hdiff hsc,
    integral_map parameterCLM.continuous.measurable.aemeasurable (by fun_prop)] at h
  exact h

/-- The equilibrium concentration input in IPLA Theorem 1 is a proved theorem
of the original joint assumptions. No gradient-Lipschitz or marginal assumption
is needed for this statistical term. -/
theorem gibbsTarget_parameter_concentration {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (θStar : EuclideanSpace ℝ (Fin dθ))
    (hmax : IsMarginalMaximizer U θStar) :
    projectedRMS (@gibbsTarget N dθ dx U) parameterCLM θStar ≤
      ENNReal.ofReal (Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m))) := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure (@potential N dθ dx U)) :=
    ULA.isProbabilityMeasure_gibbsMeasure (potential U) ((N : ℝ) * m)
      (mul_pos (by exact_mod_cast hN) hm)
      (potential_differentiable hdiff) (potential_strongConvex hsc)
  have hi := (ULA.memLp_id_gibbsMeasure (@potential N dθ dx U) ((N : ℝ) * m)
    (mul_pos (by exact_mod_cast hN) hm)
    (potential_differentiable hdiff) (potential_strongConvex hsc)).continuousLinearMap_comp
      (@parameterCLM N dθ dx)
  apply projectedRMS_le_of_secondMoment _ _ _ _ (Real.sqrt_nonneg _)
    (hi.sub (memLp_const θStar))
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * (dθ : ℝ) / ((N : ℝ) * m))]
  exact gibbsTarget_parameter_secondMoment_le hN U m hm hdiff hsc θStar hmax

end IPLA
