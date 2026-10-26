import PBGSO.ConstructedSamplerModification
import PBGSO.ContinuousBrownianDriver

/-! # Constructed continuous original sampler paths
A continuous adapted Brownian modification is constructed internally from
the actual Driver. Its proved integral invariance then yields a simultaneous
continuous original-equation version, without a Brownian path premise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.ConstructedPredictableModel
open FilteredBrownian
variable {Ω S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {D : Driver (I := I) Q}
  {M : Model S Θ Z X I} {T : ℝ≥0}

/-- Actual original-model sampler and noise paths on one probability-one
horizon event. Brownian continuity and stochastic-output matching are derived
internally; only the original drift's strong measurability is additional. -/
theorem Data.exists_continuous_sampler_version_constructed (U : Data Q D M T)
    (hf : StronglyMeasurable (fun p : (Icc 0 (T : ℝ)) × Z =>
      M.drift (M.parameter (U.optimizer p.1.val)) p.2)) :
    ∃ u b : ℝ → Ω → Z,
      StronglyMeasurable (Function.uncurry u) ∧ StronglyMeasurable (Function.uncurry b) ∧
      (∀ t ∈ Icc 0 (T : ℝ), u t =ᵐ[Q] U.sampler t) ∧
      (∀ t ∈ Icc 0 (T : ℝ), b t =ᵐ[Q]
        integral Q D T U.diffusion U.diffusion_square U.diffusion_adapted t) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → AEStronglyMeasurable[D.filtration t] (u t) Q) ∧
      ∀ᵐ ω ∂Q,
        ContinuousOn (fun t => u t ω) (Icc 0 (T : ℝ)) ∧
        ContinuousOn (fun t => b t ω) (Icc 0 (T : ℝ)) ∧
        u 0 ω = U.sampler 0 ω ∧
        IntervalIntegrable (fun t => M.drift (M.parameter (U.optimizer t)) (u t ω)) volume 0 (T : ℝ) ∧
        ∀ t ∈ Icc 0 (T : ℝ), u t ω - u 0 ω =
          (∫ s in 0..t, M.drift (M.parameter (U.optimizer s)) (u s ω)) + b t ω := by
  exact U.exists_continuous_sampler_version_of_modification
    (continuousDriver Q D) (fun i t => (continuousDriver_process_ae Q D i t).symm)
    (fun _ => le_refl _) (continuousDriver_joint_continuous Q D) hf

end PBGSO.ConstructedPredictableModel
