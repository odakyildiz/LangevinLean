import PBGSO.RawSamplerGrowthLaw
import PBGSO.RawConstantNoiseContraction
import PBGSO.RawLocalGauge
import PBGSO.ContinuousProcessRepresentative
import PBGSO.RawDampedState

/-! # Natural raw solutions with primitive constant diffusion
The raw sampler receives a joint representative preserving its whole
horizon. The chosen constant local coefficient is exactly a model diffusion
value, and gauge independence identifies its actual noise with the original
local integral. No expected drift/noise moments or positive work are assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawNaturalConstantNoise
open FilteredBrownian RawLocalStationarity RawDampedState
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {M : Model S Θ Z X I} {T : ℝ≥0}

/-- Literal deterministic coefficient columns, with their actual constant
square-energy gauge. No stochastic process or isometry is supplied. -/
def constantLocal (c : I → Z) : RawLocalDiffusion (Z := Z) Q D T where
  sigma _ _ _ := c _
  sigma_strong _ := stronglyMeasurable_const
  sigma_adapted _ _ := stronglyMeasurable_const.aestronglyMeasurable
  q _ _ := ∑ i, ‖c i‖ ^ 2
  q_strong := stronglyMeasurable_const
  q_nonneg _ _ := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  q_local _ := integrable_const _
  q_progressive t := by
    exact (stronglyMeasurable_const.indicator measurableSet_Ioc).comp_measurable measurable_fst
  sigma_control _ _ := le_rfl

/-- The actual constant-noise raw realization, with the original whole-path
state and optimizer identities proved over the horizon. -/
structure Realization (U : RawLocalStationarity.Data Q D M T) where
  localDiffusion : RawLocalDiffusion (Z := Z) Q D T
  data : RawConstantNoiseContraction.Data Q M D T localDiffusion
  optimizer_eq : ∀ t ∈ Icc 0 (T : ℝ), data.optimizer t = U.optimizer t
  sampler_eq : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ), data.sampler t ω = U.sampler.state t ω

variable (U : RawLocalStationarity.Data Q D M T)
  (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i)
  (hObs : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
  (hDrift : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
  (hOptimizer : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2))
include hσ hObs hDrift hOptimizer

/-- Natural original equations and primitive Borel fields produce the
constant-noise realization used by the one-sided work theorems. Every law,
coefficient, and actual local-noise match is a derived conclusion. -/
def build : Realization U := Classical.choice <| by
  classical
  let a : ℝ → S := fun r => U.optimizer (timeClamp T r)
  have haC : Continuous a := (RawSamplerGrowth.optimizer_continuous U).comp_continuous
    (by unfold timeClamp; fun_prop : Continuous (timeClamp T)) (timeClamp_mem T)
  have ha (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : a r = U.optimizer r := by
    dsimp only [a]
    rw [timeClamp_eq T hr]
  have hxMeas (r : ℝ) : Measurable (U.sampler.state (timeClamp T r)) :=
    U.sampler.measurable _ (timeClamp_mem T r)
  have hxCont : ∀ᵐ ω ∂Q, Continuous (fun r => U.sampler.state (timeClamp T r) ω) := by
    filter_upwards [U.sampler.continuous_paths] with ω h
    exact h.comp_continuous (by unfold timeClamp; fun_prop : Continuous (timeClamp T)) (timeClamp_mem T)
  obtain ⟨x,hxJoint,hxC,hxAE⟩ := ContinuousProcessRepresentative.exists_joint_of_measurable Q
    (fun r ω => U.sampler.state (timeClamp T r) ω) hxMeas hxCont
  have hx : ∀ᵐ ω ∂Q, ∀ r ∈ Icc 0 (T : ℝ), x r ω = U.sampler.state r ω := by
    filter_upwards [hxAE] with ω h r hr
    simpa only [timeClamp_eq T hr] using h r
  have hxLaw (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) : Q.map (x r) = Q.map (U.sampler.state r) :=
    Measure.map_congr (hx.mono (fun _ h => h r hr))
  let c : I → Z := M.diffusion (M.parameter (U.optimizer 0)) 0
  let L : RawLocalDiffusion (Z := Z) Q D T := constantLocal c
  have hnoise : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T →
      L.localNoise t ω = U.sampler.localDiffusion.localNoise t ω := by
    apply L.localNoise_gauge_congr_on_horizon U.sampler.localDiffusion
    filter_upwards [U.sampler.diffusion_realizes] with ω h i r hr
    exact (hσ (U.optimizer 0) (U.optimizer r) 0 (U.sampler.state r ω) i).trans
      (h r (Ioc_subset_Icc_self hr) i).symm
  let j : ℝ → S := fun r => M.optimizerField r (a r) (Q.map (x r))
  have hjEq (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      j r = M.optimizerField r (U.optimizer r) (Q.map (U.sampler.state r)) := by
    dsimp only [j]
    rw [ha r hr,hxLaw r hr]
  have hObsJoint : StronglyMeasurable (fun p : ℝ × Ω =>
      M.observation (M.parameter (a p.1)) (M.position (x p.1 p.2))) :=
    (hObs.comp ((haC.measurable.comp measurable_fst).prodMk hxJoint.measurable)).stronglyMeasurable
  have hjStrong : StronglyMeasurable j := by
    have hm := hObsJoint.integral_prod_right' (ν := Q)
    have hψ : StronglyMeasurable (fun r => M.optimizer r (a r)
        (∫ ω, M.observation (M.parameter (a r)) (M.position (x r ω)) ∂Q)) :=
      (hOptimizer.comp (measurable_id.prodMk (haC.measurable.prodMk hm.measurable))).stronglyMeasurable
    convert hψ using 1
    funext r
    dsimp only [j,Model.optimizerField,Model.meanGradient]
    have hxr : Measurable (x r) := hxJoint.of_uncurry_left.measurable
    have hor : Measurable (fun z : Z => M.observation (M.parameter (a r)) (M.position z)) :=
      hObs.comp (measurable_const.prodMk measurable_id)
    congr 1
    exact integral_map hxr.aemeasurable hor.stronglyMeasurable.aestronglyMeasurable
  have hjInt : IntervalIntegrable j volume 0 (T : ℝ) := by
    apply (intervalIntegrable_congr (g := fun r =>
      M.optimizerField r (U.optimizer r) (Q.map (U.sampler.state r))) ?_).mpr U.optimizer_field_integrable
    intro r hr
    rw [uIoc_of_le T.coe_nonneg] at hr
    exact hjEq r (Ioc_subset_Icc_self hr)
  let V : RawConstantNoiseContraction.Data Q M D T L := {
    optimizer := a
    optimizerDrift := j
    sampler := x
    optimizer_strong := haC.stronglyMeasurable
    optimizerDrift_strong := hjStrong
    sampler_strong := hxJoint
    drift_strong := (hDrift.comp ((haC.measurable.comp measurable_fst).prodMk hxJoint.measurable)).stronglyMeasurable
    optimizerDrift_integrable := hjInt
    optimizerDrift_realizes := fun _ _ => rfl
    optimizer_equation := by
      intro r hr
      rw [ha r hr,ha 0 ⟨le_rfl,T.coe_nonneg⟩,U.optimizer_equation r hr]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hr.1] at hs
      exact (hjEq s ⟨hs.1,hs.2.trans hr.2⟩).symm
    drift_integrable := by
      filter_upwards [U.sampler.drift_integrable,hx] with ω hb hx
      apply (intervalIntegrable_congr (g := fun r =>
        M.drift (M.parameter (U.optimizer r)) (U.sampler.state r ω)) ?_).mpr hb
      intro r hr
      rw [uIoc_of_le T.coe_nonneg] at hr
      dsimp only
      rw [ha r (Ioc_subset_Icc_self hr),hx r (Ioc_subset_Icc_self hr)]
    sampler_equation := by
      filter_upwards [U.sampler.equation,hx,hnoise] with ω he hx hn
      intro r hr
      rw [hx r hr,hx 0 ⟨le_rfl,T.coe_nonneg⟩,hn r.toNNReal ((Real.toNNReal_le_iff_le_coe).mpr hr.2),he r hr]
      congr 2
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hr.1] at hs
      dsimp only
      rw [ha s ⟨hs.1,hs.2.trans hr.2⟩,hx s ⟨hs.1,hs.2.trans hr.2⟩]
    diffusion_realizes := by
      intro i r ω
      exact hσ (U.optimizer 0) (a r) 0 (x r ω) i
    sampler_square := by
      intro r hr
      exact (memLp_congr_ae (hx.mono (fun _ h => h r hr))).mpr (RawSamplerGrowth.sampler_memLp D U r hr)
    observation_integrable := by
      intro r hr
      rw [ha r hr,hxLaw r hr]
      exact U.observation_integrable r hr }
  exact ⟨⟨L,V,ha,hx⟩⟩

end PBGSO.RawNaturalConstantNoise

namespace PBGSO.RawNaturalConstantNoise
open FilteredBrownian RawLocalStationarity
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {M : Model S Θ Z X I} {T : ℝ≥0}
  {U : RawLocalStationarity.Data Q D M T} (A : Realization U)

/-- The original raw output laws are retained exactly. -/
theorem Realization.sampler_law (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Q.map (A.data.sampler t) = Q.map (U.sampler.state t) :=
  Measure.map_congr (A.sampler_eq.mono (fun _ h => h t ht))

/-- The optimizer response is the original field at every horizon time. -/
theorem Realization.optimizerDrift_eq (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    A.data.optimizerDrift t = M.optimizerField t (U.optimizer t) (Q.map (U.sampler.state t)) := by
  rw [A.data.optimizerDrift_realizes t ht,A.optimizer_eq t ht,A.sampler_law t ht]

/-- The L² state is the section of the original raw state itself. -/
theorem Realization.sampler_section (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ProductLpSections.sectionLp Q A.data.sampler t =
      ProductLpSections.sectionLp Q U.sampler.state t := by
  apply Lp.ext
  have hx : A.data.sampler t =ᵐ[Q] U.sampler.state t := A.sampler_eq.mono (fun _ h => h t ht)
  exact (ProductLpSections.sectionLp_ae Q A.data.sampler (A.data.sampler_square t ht)).trans
    (hx.trans (ProductLpSections.sectionLp_ae Q U.sampler.state
      (RawSamplerGrowth.sampler_memLp D U t ht)).symm)

/-- The exact actual local stochastic noise is the original one on a
single full-measure event over the complete horizon. -/
theorem Realization.localNoise_eq_original
    (hσ : ∀ s s' z w i, M.diffusion (M.parameter s) z i = M.diffusion (M.parameter s') w i) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T →
      A.localDiffusion.localNoise t ω = U.sampler.localDiffusion.localNoise t ω := by
  apply A.localDiffusion.localNoise_gauge_congr_on_horizon U.sampler.localDiffusion
  filter_upwards [U.sampler.diffusion_realizes] with ω h i r hr
  rw [A.data.diffusion_realizes]
  exact (hσ (A.data.optimizer r) (U.optimizer r) (A.data.sampler r ω) (U.sampler.state r ω) i).trans
    (h r (Ioc_subset_Icc_self hr) i).symm

end PBGSO.RawNaturalConstantNoise
