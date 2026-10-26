import PBGSO.ConstructedItoModel
import PBGSO.CoupledBrownianFiltration

/-! # Original constructed model equations under a common Brownian coupling
The actual coefficient columns, completed integrals and model equations
transport through a measure-preserving map and a valid filtration enlargement.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω Ω' I Z : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R) (D : Driver (I := I) R)

/-- A variable adapted to the original past pulls to the actual pulled past. -/
theorem pullback_adapted (t : ℝ≥0) (U : Lp Z 2 R)
    (hU : AEStronglyMeasurable[D.filtration t] U R) :
    AEStronglyMeasurable[(pullbackDriver hf D).filtration t] (lpPullbackCLM (E := Z) hf U) Q := by
  refine ⟨hU.mk U ∘ f, ?_, ?_⟩
  · exact hU.stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  · exact (lpPullback_coe hf U).trans (hf.quasiMeasurePreserving.ae_eq_comp hU.ae_eq_mk)

/-- Actual continuous-integrand integration commutes with source pullback. -/
theorem continuousIntegral_pullback (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) R) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) R)
    (t : ℝ≥0) :
    continuousIntegral Q (pullbackDriver hf D) T
      (fun r => columnPullbackCLM (I := I) (Z := Z) hf (u r)) ((columnPullbackCLM (I := I) (Z := Z) hf).continuous.comp hu)
      (fun r i => pullback_adapted hf D r (u r i) (hU r i)) t =
      lpPullbackCLM (E := Z) hf (continuousIntegral R D T u hu hU t) := by
  let v := continuousCutDomain Q (pullbackDriver hf D) T
    (fun r => columnPullbackCLM (I := I) (Z := Z) hf (u r)) ((columnPullbackCLM (I := I) (Z := Z) hf).continuous.comp hu)
    (fun r i => pullback_adapted hf D r (u r i) (hU r i)) t
  let w := pullbackDomain hf D (GridIntegralCompletion.dyadicGrids T)
    (continuousCutDomain R D T u hu hU t)
  have hv : v = w := by
    apply Subtype.ext
    apply Lp.ext
    have hw := (columnPullbackCLM (I := I) (Z := Z) hf).coeFn_compLpL
      (continuousCutDomain R D T u hu hU t).val
    filter_upwards [continuousCutDomain_coe Q (pullbackDriver hf D) T
      (fun r => columnPullbackCLM (I := I) (Z := Z) hf (u r)) ((columnPullbackCLM (I := I) (Z := Z) hf).continuous.comp hu)
      (fun r i => pullback_adapted hf D r (u r i) (hU r i)) t,
      continuousCutDomain_coe R D T u hu hU t, hw] with r hv hr hw
    change v.val r = w.val r
    change w.val r = columnPullbackCLM (I := I) (Z := Z) hf ((continuousCutDomain R D T u hu hU t).val r) at hw
    rw [hv, hw, hr]
    by_cases hR : r ∈ Ioc 0 (T : ℝ) <;> by_cases hrt : r ∈ Ioc 0 (t : ℝ)
    all_goals simp only [Set.indicator, hR, hrt, ite_true, ite_false, map_zero]
  change stochasticIntegral Q (pullbackDriver hf D) _ v = _
  rw [hv]
  exact stochasticIntegral_pullback hf D _ _

/-- The same pullback identity in any valid larger filtration carrying the
literal pulled Brownian coordinates. -/
theorem continuousIntegral_pullback_enlarge (E : Driver (I := I) Q)
    (hp : (pullbackDriver hf D).process = E.process)
    (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
    (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) R) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) R)
    (t : ℝ≥0) :
    continuousIntegral Q E T
      (fun r => columnPullbackCLM (I := I) (Z := Z) hf (u r))
      ((columnPullbackCLM (I := I) (Z := Z) hf).continuous.comp hu)
      (fun r i => (pullback_adapted hf D r (u r i) (hU r i)).mono (he r)) t =
      lpPullbackCLM (E := Z) hf (continuousIntegral R D T u hu hU t) := by
  rw [continuousIntegral_enlarge Q (pullbackDriver hf D) E hp he T
    _ _ (fun r i => pullback_adapted hf D r (u r i) (hU r i))]
  exact continuousIntegral_pullback hf D T u hu hU t

end PBGSO.FilteredBrownian

namespace PBGSO.ConstructedItoModel
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
  diffusion_continuous := (columnPullbackCLM (I := I) (Z := Z) hf).continuous.comp U.diffusion_continuous
  sampler_adapted t := (pullback_adapted hf D t (U.sampler t) (U.sampler_adapted t)).mono (he t)
  diffusion_adapted t i :=
    (pullback_adapted hf D t (U.diffusion t i) (U.diffusion_adapted t i)).mono (he t)
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
    exact (continuousIntegral_pullback_enlarge hf D E hp he T U.diffusion
      U.diffusion_continuous U.diffusion_adapted t.toNNReal).symm
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

end PBGSO.ConstructedItoModel
