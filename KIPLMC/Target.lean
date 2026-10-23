import ProximalLangevin.SharpIPLA
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # The kinetic Gibbs target and its concentrating parameter marginal

These are probability and concentration results for the explicitly defined
Gibbs measure. Invariance of this measure under the kinetic SDE is a separate
analytic assertion and is not silently assumed here.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace KIPLMC

/-- The scaled physical velocities have independent centered Gaussian
coordinates of variance `1/N`. -/
def velocityTarget (N dθ dx : ℕ) : Measure (IPLA.State N dθ dx) :=
  (stdGaussian (IPLA.State N dθ dx)).map (fun v ↦ (Real.sqrt N)⁻¹ • v)

instance velocityTarget_probability (N dθ dx : ℕ) :
    IsProbabilityMeasure (velocityTarget N dθ dx) := by
  unfold velocityTarget
  constructor
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- Explicit candidate invariant measure: independent thermal velocities and
the already normalized lifted Gibbs positions. Velocity comes first. -/
def gibbsPhaseTarget {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) :
    Measure (IPLA.State N dθ dx × IPLA.State N dθ dx) :=
  (velocityTarget N dθ dx).prod (IPLA.gibbsTarget U)

/-- Strong convexity normalizes the phase target. -/
theorem gibbsPhaseTarget_probability {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U) :
    IsProbabilityMeasure (@gibbsPhaseTarget N dθ dx U) := by
  letI := IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  unfold gibbsPhaseTarget
  infer_instance

/-- Integrating velocities leaves the configuration Gibbs measure exactly. -/
theorem gibbsPhaseTarget_position {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U) :
    (@gibbsPhaseTarget N dθ dx U).map Prod.snd = IPLA.gibbsTarget U := by
  letI := IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  simpa only [gibbsPhaseTarget, measure_univ, one_smul] using
    (Measure.map_snd_prod (μ := velocityTarget N dθ dx) (ν := IPLA.gibbsTarget U))

/-- The phase-space parameter marginal is the powered marginal likelihood.
All normalizations in this identity are derived from the original potential. -/
theorem gibbsPhaseTarget_parameter {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U) :
    (@gibbsPhaseTarget N dθ dx U).map (fun z ↦ IPLA.parameterCLM z.2) =
      IPLA.marginalTarget N U := by
  rw [← Function.comp_def, ← Measure.map_map
    IPLA.parameterCLM.continuous.measurable measurable_snd]
  rw [gibbsPhaseTarget_position hN U m hm hdiff hsc]
  exact IPLA.gibbsTarget_parameter_marginal hN U m hm hdiff hsc

/-- The MMLE center exists and is unique by joint strong convexity. -/
theorem existsUnique_mmle {dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn univ m U) :
    ∃! θ, IPLA.IsMarginalMaximizer U θ :=
  IPLA.existsUnique_marginalMaximizer U m hm hdiff hsc

/-- The concentration term in both KIPLMC error bounds, with its sharp
dimension constant. This theorem reuses the actual powered Gibbs marginal. -/
theorem parameter_secondMoment_le {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) :
    (∫ θ, ‖θ - θStar‖ ^ 2 ∂IPLA.marginalTarget N U) ≤
      (dθ : ℝ) / ((N : ℝ) * m) :=
  ProximalLangevin.sharp_marginalTarget_secondMoment_le hN U m hm hdiff hsc θStar hmax

/-- A dimension-sharp RMS concentration bound in the existing transport API. -/
theorem parameter_concentration {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) :
    IPLA.projectedRMS (@IPLA.gibbsTarget N dθ dx U) IPLA.parameterCLM θStar ≤
      ENNReal.ofReal (Real.sqrt ((dθ : ℝ) / ((N : ℝ) * m))) :=
  ProximalLangevin.sharp_gibbsTarget_parameter_concentration
    hN U m hm hdiff hsc θStar hmax

end KIPLMC
