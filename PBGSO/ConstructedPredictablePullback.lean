import PBGSO.ConstructedPredictableModel
import PBGSO.PredictableIntegralTransport
import PBGSO.CoupledBrownianFiltration

/-! # Actual predictable model equations on common coupled Brownian sources
The original time-L² diffusion, integral equation and marginal laws transport
through a measure-preserving source map and valid filtration enlargement.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.ConstructedPredictableModel
open FilteredBrownian
variable {Ω Ω' I Z S Θ X : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)
  {D : Driver (I := I) R} (E : Driver (I := I) Q)
  (hp : (pullbackDriver hf D).process = E.process)
  (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
  {M : Model S Θ Z X I} {T : ℝ≥0}

/-- Original model data transported into one actual common Brownian source.
All marginal laws and the stochastic integral equation are derived. -/
def Data.pullback (U : Data R D M T) : Data Q E M T where
  optimizer := U.optimizer
  optimizerDrift := U.optimizerDrift
  sampler t := lpPullbackCLM (E := Z) hf (U.sampler t)
  drift t := lpPullbackCLM (E := Z) hf (U.drift t)
  diffusion t := columnPullbackCLM (I := I) (Z := Z) hf (U.diffusion t)
  optimizerDrift_integrable := U.optimizerDrift_integrable
  drift_integrable := by
    constructor
    · exact (lpPullbackCLM (E := Z) hf).integrable_comp U.drift_integrable.1
    · exact (lpPullbackCLM (E := Z) hf).integrable_comp U.drift_integrable.2
  diffusion_square := (columnPullbackCLM (I := I) (Z := Z) hf).comp_memLp' U.diffusion_square
  sampler_adapted t := (columnPullback_adapted hf D t (U.sampler t) (U.sampler_adapted t)).mono (he t)
  diffusion_adapted t i :=
    (columnPullback_adapted hf D t (U.diffusion t i) (U.diffusion_adapted t i)).mono (he t)
  optimizerDrift_realizes t ht := by
    rw [lpPullback_law]
    exact U.optimizerDrift_realizes t ht
  optimizer_integral := U.optimizer_integral
  sampler_integral t ht := by
    have hi := congrArg (lpPullbackCLM (E := Z) hf) (U.sampler_integral t ht)
    rw [map_add, map_add, ← (lpPullbackCLM (E := Z) hf).intervalIntegral_comp_comm
      (U.drift_integrable.mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le T.coe_nonneg]
        exact Icc_subset_Icc le_rfl ht.2))] at hi
    rw [hi]
    congr 1
    exact (predictableCurveIntegral_pullback_enlarge hf D E hp he T U.diffusion
      U.diffusion_square U.diffusion_adapted t.toNNReal).symm
  drift_realizes t ht := by
    filter_upwards [lpPullback_coe hf (U.drift t),
      hf.quasiMeasurePreserving.ae_eq_comp (U.drift_realizes t ht),
      lpPullback_coe hf (U.sampler t)] with ω hd hr hs
    simp only [Function.comp_apply] at hr
    rw [hd, hr, hs]
  diffusion_realizes t ht i := by
    filter_upwards [lpPullback_coe hf (U.diffusion t i),
      hf.quasiMeasurePreserving.ae_eq_comp (U.diffusion_realizes t ht i),
      lpPullback_coe hf (U.sampler t)] with ω hd hr hs
    change (lpPullbackCLM (E := Z) hf (U.diffusion t i)) ω = _
    simp only [Function.comp_apply] at hr
    rw [hd, hr, hs]
  observation_integrable t ht := by
    rw [lpPullback_law]
    exact U.observation_integrable t ht

end PBGSO.ConstructedPredictableModel
