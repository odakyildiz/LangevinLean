import IPLA.LSI.Marginal
import IPLA.LSI.Theorem

set_option linter.style.header false

/-!
# Parameter-marginal consequences of the joint IPLA entropy bound

The marginal target is the parameter pushforward of the actual lifted Gibbs
law. Data processing transfers the full-state KL estimate to this parameter
law, retaining the full-state initial KL. A per-particle normalization of the
joint estimate requires multiplication by `N` for an unscaled parameter bound.

All interpolation obligations and the lifted-target LSI hypothesis remain
visible. Neither an LSI for the original parameter/latent pair nor a claim of
concentration about a marginal-likelihood maximizer is introduced.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace IPLA.LSI

/-- Finite actual joint IPLA KL supplies finite actual parameter KL. -/
theorem parameter_kl_finite
    {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (β γ : ℝ) (L : ℝ≥0)
    (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hγ : 0 ≤ γ)
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) β (γ / N)
      ((N : ℝ≥0) * L) μ) (k : ℕ) :
    InformationTheory.klDiv ((particleLaws U γ μ k).map parameterCLM)
      (@parameterTarget N dθ dx U) ≠ ⊤ := by
  have : IsProbabilityMeasure (particleLaws U γ μ k) :=
    particleLaws_isProbability U γ μ L hdiff hLip k
  have : IsProbabilityMeasure (@gibbsTarget N dθ dx U) := hLSI.1
  exact parameter_kl_ne_top_of_gibbs_joint U (particleLaws U γ μ k)
    (particle_kl_finite U β γ L μ hγ hLSI data k)

/-- The actual parameter marginal inherits the full joint KL bound for any
supplied lifted LSI constant `β`. The initial entropy is the full joint entropy. -/
theorem parameter_kl_bound
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (β γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hβ : 0 < β) (hβL : β ≤ (N : ℝ) * (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ β / (4 * (N : ℝ) * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) β)
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) β (γ / N)
      ((N : ℝ≥0) * L) μ) (k : ℕ) :
    (InformationTheory.klDiv ((particleLaws U γ μ k).map parameterCLM)
      (@parameterTarget N dθ dx U)).toReal ≤
      Real.exp (-β * γ * k / N) *
        (InformationTheory.klDiv μ (gibbsTarget U)).toReal +
          8 * γ * N * (dθ + N * dx : ℕ) * (L : ℝ) ^ 2 / β := by
  have : IsProbabilityMeasure (particleLaws U γ μ k) :=
    particleLaws_isProbability U γ μ L hdiff hLip k
  have : IsProbabilityMeasure (@gibbsTarget N dθ dx U) := hLSI.1
  exact parameter_kl_bound_of_gibbs_joint_bound U (particleLaws U γ μ k)
    (particle_kl_finite U β γ L μ hγ.le hLSI data k) _
    (particle_kl_bound hN U β γ L μ hdiff hLip hβ hβL hγ hsmall hLSI data k)

/-- Under the supplied lifted LSI constant `N * α`, the normalized joint
entropy estimate bounds unscaled parameter KL only after multiplication by `N`.
This does not replace the initial joint entropy with initial parameter entropy. -/
theorem parameter_kl_bound_of_linear_lsi
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ)
    (α γ : ℝ) (L : ℝ≥0) (μ : Measure (State N dθ dx)) [IsProbabilityMeasure μ]
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hα : 0 < α) (hαL : α ≤ (L : ℝ)) (hγ : 0 < γ)
    (hsmall : γ ≤ α / (4 * (L : ℝ) ^ 2))
    (hLSI : ULA.LSI.IsLogSobolev (@gibbsTarget N dθ dx U) ((N : ℝ) * α))
    (data : ULA.LSI.RegularInterpolationData (@potential N dθ dx U) ((N : ℝ) * α)
      (γ / N) ((N : ℝ≥0) * L) μ) (k : ℕ) :
    (InformationTheory.klDiv ((particleLaws U γ μ k).map parameterCLM)
      (@parameterTarget N dθ dx U)).toReal ≤
      (N : ℝ) * (Real.exp (-α * γ * k) *
        ((InformationTheory.klDiv μ (gibbsTarget U)).toReal / N) +
          (8 * γ * (L : ℝ) ^ 2 / α) * ((dx : ℝ) + (dθ : ℝ) / N)) := by
  have : IsProbabilityMeasure (particleLaws U γ μ k) :=
    particleLaws_isProbability U γ μ L hdiff hLip k
  have : IsProbabilityMeasure (@gibbsTarget N dθ dx U) := hLSI.1
  exact parameter_kl_bound_of_per_particle_bound hN
    (particleLaws U γ μ k) (gibbsTarget U)
    (particle_kl_finite U ((N : ℝ) * α) γ L μ hγ.le hLSI data k) _
    (particle_kl_bound_of_linear_lsi hN U α γ L μ hdiff hLip
      hα hαL hγ hsmall hLSI data k)

end IPLA.LSI
