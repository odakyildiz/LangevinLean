import PBGSO.RawLocalPullbackLocal
import PBGSO.RawLocalStationarity

/-! # Original local strong equations under changes of probability space

Actual raw sampler and coupled optimiser equations are transported along a
measure-preserving initial/noise map into a valid larger Brownian filtration.
Local stochastic integral naturality and every marginal law identity are
derived. No global coefficient moments or matching-noise assumptions enter.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.RawLocalStationarity
open FilteredBrownian
variable {Ω Ω' S Θ Z X I : Type*}
  [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω'] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)
  {D : Driver (I := I) R} (E : Driver (I := I) Q)
  (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
  (hp : ∀ i t, (pullbackDriver hf D).process i t =ᵐ[Q] E.process i t)
  {M : Model S Θ Z X I} {T : ℝ≥0} {a : ℝ → S}

/-- The original raw sampler equation, transported with the actual computed
local stochastic integral. A common event supports its complete time path. -/
def SamplerData.pullback (U : SamplerData R D M T a) : SamplerData Q E M T a where
  localDiffusion := U.localDiffusion.pullback hf E he
  state t ω := U.state t (f ω)
  measurable t ht := (U.measurable t ht).comp hf.measurable
  adapted t := by
    refine ⟨(U.adapted t).mk (U.state t) ∘ f, ?_, ?_⟩
    · exact (U.adapted t).stronglyMeasurable_mk.comp_measurable
        (measurable_iff_comap_le.mpr (he t))
    · exact hf.quasiMeasurePreserving.ae_eq_comp (U.adapted t).ae_eq_mk
  continuous_paths := hf.quasiMeasurePreserving.ae U.continuous_paths
  drift_integrable := hf.quasiMeasurePreserving.ae U.drift_integrable
  diffusion_realizes := hf.quasiMeasurePreserving.ae U.diffusion_realizes
  equation := by
    filter_upwards [hf.quasiMeasurePreserving.ae U.equation,
      U.localDiffusion.pullback_localNoise_on_horizon hf E he hp] with ω hu hn
    intro t ht
    have hnt : t.toNNReal ≤ T := by exact_mod_cast (Real.toNNReal_le_iff_le_coe).mpr ht.2
    change U.state t (f ω) = U.state 0 (f ω) + _ + _
    rw [hn t.toNNReal hnt]
    exact hu t ht

variable (U : SamplerData R D M T a)

/-- The exact original marginal law survives probability-space transport. -/
theorem SamplerData.pullback_law (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Q.map ((U.pullback hf E he hp).state t) = R.map (U.state t) := by
  change Q.map (U.state t ∘ f) = _
  rw [← Measure.map_map (U.measurable t ht) hf.measurable, hf.map_eq]

/-- Every original coupled equation and domain condition is preserved.
The marginal-law and stochastic-noise matches are conclusions of transport. -/
def Data.pullback (U : Data R D M T) : Data Q E M T where
  optimizer := U.optimizer
  sampler := U.sampler.pullback hf E he hp
  second_moment t ht := by rw [U.sampler.pullback_law hf E he hp t ht]; exact U.second_moment t ht
  observation_integrable t ht := by
    rw [U.sampler.pullback_law hf E he hp t ht]
    exact U.observation_integrable t ht
  optimizer_field_integrable := by
    apply (intervalIntegrable_congr (g := fun t =>
      M.optimizerField t (U.optimizer t) (R.map (U.sampler.state t))) ?_).mpr
      U.optimizer_field_integrable
    intro t ht
    rw [uIoc_of_le T.coe_nonneg] at ht
    dsimp only
    rw [U.sampler.pullback_law hf E he hp t (Ioc_subset_Icc_self ht)]
  optimizer_equation t ht := by
    rw [U.optimizer_equation t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    dsimp only
    rw [U.sampler.pullback_law hf E he hp r ⟨hr.1, hr.2.trans ht.2⟩]

/-- Frozen local strong samplers transport on arbitrary primitive local
diffusion classes, with invariant law and initial L² derived under pullback. -/
def FrozenSamplerData.pullback {sStar : S} {νStar : Measure Z}
    (F : FrozenSamplerData R D M T sStar νStar) : FrozenSamplerData Q E M T sStar νStar where
  toSamplerData := F.toSamplerData.pullback hf E he hp
  initial_square := F.initial_square.comp_measurePreserving hf
  invariant_law t ht := (F.toSamplerData.pullback_law hf E he hp t ht).trans (F.invariant_law t ht)

include hf he hp

/-- Strong uniqueness transfers original solution laws across an actual
initial/noise map. The final marginal match is derived by the proved raw
equation transport; it is not included as a solution-realization premise. -/
theorem law_unique_of_initial_noise_map
    (hunique : PathwiseUniqueness Q E M T)
    (U : Data R D M T) (V : Data Q E M T)
    (hs : V.optimizer 0 = U.optimizer 0)
    (hz : V.sampler.state 0 =ᵐ[Q] fun ω => U.sampler.state 0 (f ω))
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    V.optimizer t = U.optimizer t ∧ Q.map (V.sampler.state t) = R.map (U.sampler.state t) := by
  have h := hunique V (U.pullback hf E he hp) hs hz t ht
  exact ⟨h.1, (Measure.map_congr h.2).trans (U.sampler.pullback_law hf E he hp t ht)⟩

/-- Stationary product laws transfer from an actual frozen strong sampler
to any source carrying the same initial/noise input, without a same-space
frozen-realization or global-coefficient-moment assumption. -/
theorem stationary_product_law_of_initial_noise_map [MeasurableSpace S]
    (hunique : PathwiseUniqueness Q E M T)
    {sStar : S} {νStar : Measure Z}
    (F : FrozenSamplerData R D M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0)
    (V : Data Q E M T) (hs : V.optimizer 0 = sStar)
    (hz : V.sampler.state 0 =ᵐ[Q] fun ω => F.state 0 (f ω))
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Q.map (fun ω => (V.optimizer t, V.sampler.state t ω)) = (Measure.dirac sStar).prod νStar :=
  stationary_product_law hunique (F.pullback hf E he hp) hint hg hfix V hs hz t ht

end PBGSO.RawLocalStationarity
