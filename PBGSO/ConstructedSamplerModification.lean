import PBGSO.ConstructedMeasurableSamplerPaths
import PBGSO.FilteredIntegralModification

/-! # Original computed sampler paths under a continuous Brownian modification
The raw original Brownian representatives need not be simultaneously
continuous. Actual fixed-time modifications preserve the computed integrals,
so the derived joint continuous sampler version realizes the original model.
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

/-- A valid Brownian modification changes only the driver representation;
actual model states, drift and diffusion columns stay literally the same. -/
def Data.modifyDriver (U : Data Q D M T) (E : Driver (I := I) Q)
    (hprocess : ∀ i t, D.process i t =ᵐ[Q] E.process i t)
    (henlarge : ∀ t, D.filtration t ≤ E.filtration t) : Data Q E M T where
  optimizer := U.optimizer
  optimizerDrift := U.optimizerDrift
  sampler := U.sampler
  drift := U.drift
  diffusion := U.diffusion
  optimizerDrift_integrable := U.optimizerDrift_integrable
  drift_integrable := U.drift_integrable
  diffusion_square := U.diffusion_square
  sampler_adapted t := (U.sampler_adapted t).mono (henlarge t)
  diffusion_adapted t i := (U.diffusion_adapted t i).mono (henlarge t)
  optimizerDrift_realizes := U.optimizerDrift_realizes
  optimizer_integral := U.optimizer_integral
  sampler_integral t ht := by
    rw [U.sampler_integral t ht]
    congr 1
    exact (predictableCurveIntegral_congr_ae Q D E hprocess henlarge T U.diffusion U.diffusion_square
      U.diffusion_adapted (fun t i => (U.diffusion_adapted t i).mono (henlarge t)) t.toNNReal).symm
  drift_realizes := U.drift_realizes
  diffusion_realizes := U.diffusion_realizes
  observation_integrable := U.observation_integrable

/-- Joint continuous original-model sampler paths, with no false continuity
claim for the original raw Brownian representatives. Only the valid modified
Driver has actual coordinate continuity. All computed output identities are
proved from fixed-time AE equality of those drivers. -/
theorem Data.exists_continuous_sampler_version_of_modification (U : Data Q D M T)
    (E : Driver (I := I) Q)
    (hprocess : ∀ i t, D.process i t =ᵐ[Q] E.process i t)
    (henlarge : ∀ t, D.filtration t ≤ E.filtration t)
    (hB : ∀ᵐ ω ∂Q, ∀ i, Continuous (fun t => E.process i t ω))
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
  let V := U.modifyDriver E hprocess henlarge
  obtain ⟨u, b, hu, hb, huEq, hbEq, _, hpath⟩ :=
    V.exists_continuous_sampler_version_of_stronglyMeasurable hB hf
  refine ⟨u, b, hu, hb, huEq, ?_, ?_, hpath⟩
  · intro t ht
    have he := hbEq t ht
    have hi : integral Q E T U.diffusion U.diffusion_square
        (fun t i => (U.diffusion_adapted t i).mono (henlarge t)) t =
        integral Q D T U.diffusion U.diffusion_square U.diffusion_adapted t :=
      predictableCurveIntegral_congr_ae Q D E hprocess henlarge T U.diffusion U.diffusion_square
        U.diffusion_adapted (fun t i => (U.diffusion_adapted t i).mono (henlarge t)) t.toNNReal
    exact he.trans (Eventually.of_forall (fun ω => congrArg (fun A : Lp Z 2 Q => A ω) hi))
  · intro t ht
    exact (U.sampler_adapted t).congr (huEq t ⟨t.coe_nonneg, ht⟩).symm

end PBGSO.ConstructedPredictableModel
