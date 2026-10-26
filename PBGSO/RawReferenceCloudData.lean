import PBGSO.RawReferenceCloudEquation
import PBGSO.RawNaturalSampler

/-! # Natural independent-cloud equations produce actual controlled raw data
The reference cloud is constructed from independent whole seeds. Its literal
physical equation feeds the generic natural sampler realization; all drift,
diffusion, output-law and same-driver stochastic identities are conclusions.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawReferenceCloudData
open FilteredBrownian RawReferenceCloud
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (M : Model S Θ Z X I) (N : ℕ) {T : ℝ≥0}

/-- The auxiliary physical sampler model. Its unused observation is zero;
only its literal independent coordinate drift/diffusion enters this file. -/
def cloudModel : Model S Θ (Cloud N Z) (Cloud N Z) (Fin N × I) where
  parameter := M.parameter
  position := id
  observation _ _ := 0
  optimizer := M.optimizer
  drift θ z := WithLp.toLp 2 (fun i => M.drift θ (z i))
  diffusion θ z ij := single (Z := Z) N ij.1 (M.diffusion θ (z ij.1) ij.2)

variable (U : RawLocalStationarity.Data Q D M T)

/-- The natural original full-cloud equation, with actual local noise and
physical coefficients, is derived from the one-copy equations. -/
def samplerData : RawLocalStationarity.SamplerData
    (IndependentCopies.seeds (J := Fin N) Q) (RawIndependentCopies.driver Q D N)
    (cloudModel M N) T U.optimizer where
  localDiffusion := diffusion Q D N U.sampler.localDiffusion
  state := state Q D N U
  measurable := state_measurable Q D N U
  adapted t := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => Z)).symm.continuous.comp_aestronglyMeasurable
    (RawIndependentCopies.cloud_adapted Q D N U t)
  continuous_paths := state_continuous_paths Q D N U
  drift_integrable := by
    have he (r : ℝ) (ω : Fin N → Ω) :
        (cloudModel M N).drift ((cloudModel M N).parameter (U.optimizer r)) (state Q D N U r ω) =
          RawReferenceCloud.drift Q D N U r ω := by
      apply PiLp.ext
      intro i
      exact (RawReferenceCloud.drift_apply Q D N U r ω i).symm
    simpa only [he] using RawReferenceCloud.drift_integrable Q D N U
  diffusion_realizes := physical_columns Q D N U
  equation := by
    have he (r : ℝ) (ω : Fin N → Ω) :
        (cloudModel M N).drift ((cloudModel M N).parameter (U.optimizer r)) (state Q D N U r ω) =
          RawReferenceCloud.drift Q D N U r ω := by
      apply PiLp.ext
      intro i
      exact (RawReferenceCloud.drift_apply Q D N U r ω i).symm
    simpa only [he] using RawReferenceCloud.equation Q D N U

/-- The actual full iid reference cloud acquires controlled raw dynamics
without any reference coefficient, joint law, noise output or moment premise.
Only the original one-copy solution and primitive projected-drift Borel
regularity enter. -/
def build
    (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2)) :
    RawNaturalSampler.Realization (samplerData Q D M N U) := by
  have hb : Measurable (fun p : S × Cloud N Z =>
      (cloudModel M N).drift ((cloudModel M N).parameter p.1) p.2) := by
    have hm : Measurable (fun p : S × Cloud N Z => fun i =>
        M.drift (M.parameter p.1) (p.2 i)) := by
      apply measurable_pi_lambda
      intro i
      exact hDrift.comp (measurable_fst.prodMk
        ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => Z) i).continuous.measurable.comp measurable_snd))
    exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => Z)).symm.continuous.measurable.comp hm
  exact RawNaturalSampler.build (samplerData Q D M N U)
    (RawSamplerGrowth.optimizer_continuous U)
    (state_square Q D N U 0 ⟨le_rfl,T.coe_nonneg⟩) hb

end PBGSO.RawReferenceCloudData
