import PBGSO.RawConstantNoiseContraction
import PBGSO.RawLocalPullback

/-! # Naturality of original raw constant-diffusion model equations
The actual original raw paths transport to valid enlarged Brownian spaces.
The proof identifies computed local integrals; no noise identity or output-law
coherence is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawConstantNoiseContraction
open FilteredBrownian
variable {Ω Ω' S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)
  {D : Driver (I := I) R} (E : Driver (I := I) Q)
  (hp : (pullbackDriver hf D).process = E.process)
  (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
  {T : ℝ≥0} {M : Model S Θ Z X I}
  (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
  {L : RawLocalDiffusion (Z := Z) R D T}

include hf

/-- Actual sampler laws are preserved by raw composition. -/
theorem rawSampler_pullback_law (U : Data R M D T L) (t : ℝ) :
    Q.map (fun ω => U.sampler t (f ω)) = R.map (U.sampler t) := by
  change Q.map (U.sampler t ∘ f) = R.map (U.sampler t)
  rw [← Measure.map_map U.sampler_strong.of_uncurry_left.measurable hf.measurable,hf.map_eq]

/-- Original raw equations on the genuine pulled/enlarged Brownian past.
All fields are derived from composition and actual local-integral naturality. -/
def Data.pullback (U : Data R M D T L) : Data Q M E T (L.pullback hf E he) where
  optimizer := U.optimizer
  optimizerDrift := U.optimizerDrift
  sampler r ω := U.sampler r (f ω)
  optimizer_strong := U.optimizer_strong
  optimizerDrift_strong := U.optimizerDrift_strong
  sampler_strong := U.sampler_strong.comp_measurable
    (measurable_fst.prodMk (hf.measurable.comp measurable_snd))
  drift_strong := U.drift_strong.comp_measurable
    (measurable_fst.prodMk (hf.measurable.comp measurable_snd))
  optimizerDrift_integrable := U.optimizerDrift_integrable
  optimizerDrift_realizes r hr := by
    rw [rawSampler_pullback_law hf U r]
    exact U.optimizerDrift_realizes r hr
  optimizer_equation := U.optimizer_equation
  drift_integrable := hf.quasiMeasurePreserving.ae U.drift_integrable
  sampler_equation := by
    filter_upwards [hf.quasiMeasurePreserving.ae U.sampler_equation,
      L.pullback_noise_on_horizon hf E he hp (diffusion_square R M U hσ)] with ω hu hn
    intro r hr
    rw [hu r hr,hn r.toNNReal ((Real.toNNReal_le_iff_le_coe).mpr hr.2)]
  diffusion_realizes i r ω := U.diffusion_realizes i r (f ω)
  sampler_square r hr := (U.sampler_square r hr).comp_measurePreserving hf
  observation_integrable r hr := by
    rw [rawSampler_pullback_law hf U r]
    exact U.observation_integrable r hr

@[simp] theorem Data.pullback_law (U : Data R M D T L) (t : ℝ) :
    Q.map ((U.pullback hf E hp he hσ).sampler t) = R.map (U.sampler t) :=
  rawSampler_pullback_law hf U t


/-- Literal fixed-time L² sections transport by the actual pullback isometry. -/
theorem Data.pullback_section (U : Data R M D T L) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ProductLpSections.sectionLp Q (U.pullback hf E hp he hσ).sampler t =
      lpPullbackCLM hf (ProductLpSections.sectionLp R U.sampler t) := by
  apply Lp.ext
  have hleft := ProductLpSections.sectionLp_ae Q (U.pullback hf E hp he hσ).sampler
    ((U.pullback hf E hp he hσ).sampler_square t ht)
  have hright := (lpPullback_coe hf (ProductLpSections.sectionLp R U.sampler t)).trans
    (hf.quasiMeasurePreserving.ae_eq_comp (ProductLpSections.sectionLp_ae R U.sampler (U.sampler_square t ht)))
  exact hleft.trans hright.symm

end PBGSO.RawConstantNoiseContraction
