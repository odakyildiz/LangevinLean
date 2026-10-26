import PBGSO.RawLocalDriftEnergy
import PBGSO.RawLocalStationarity
import PBGSO.RawLinearGrowthModel

/-! # Natural raw strong equations in the linear-growth branch
The local energy gauge is augmented internally, with the actual original
local noise preserved. Global state/coefficient moments and the constructed
predictable model are conclusions. The raw drift's joint measurability,
progressivity and the primitive source linear-growth condition are explicit.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawSamplerGrowth
open FilteredBrownian RawLocalStationarity ConstructedPredictableModel
variable {Ω S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {M : Model S Θ Z X I} {T : ℝ≥0}

/-- Actual output of the derived localization/moment pipeline. State and
optimizer identities are recorded as conclusions of its construction. -/
structure Construction (U : RawLocalStationarity.Data Q D M T) (C P : ℝ) where
  localDiffusion : RawLocalDiffusion (Z := Z) Q (nullAugmentedDriver Q D) T
  stateData : RawLinearGrowthState.Data localDiffusion C P
  realization : RawLinearGrowthModel.Realization M localDiffusion C P stateData
  state_eq : stateData.state = U.sampler.state
  optimizer_eq : realization.optimizer = U.optimizer

variable (U : RawLocalStationarity.Data Q D M T)
  (hb : StronglyMeasurable (Function.uncurry (originalRawDrift M U.optimizer U.sampler.state)))
  (hprog : ∀ t : ℝ≥0,
    StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (D.filtration t)]
      (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator
        (fun r => originalRawDrift M U.optimizer U.sampler.state r p.2) p.1))
  (hσ : ∀ i, StronglyMeasurable
    (Function.uncurry (originalRawDiffusion M U.optimizer U.sampler.state i)))
  (hσB : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
  (C P : ℝ) (hC : 0 ≤ C) (hP : 0 ≤ P)
  (hparam : ∀ t ∈ Icc 0 (T : ℝ), ‖M.parameter (U.optimizer t)‖ ≤ P)
  (hgrowth : ∀ s z, ‖M.drift (M.parameter s) z‖+
    ‖WithLp.toLp 2 (M.diffusion (M.parameter s) z)‖ ≤ C*(1+‖M.parameter s‖+‖z‖))

include hb hprog hσ hσB hC hP hparam hgrowth

/-- Natural original raw equations produce genuine controlled local data,
global moments, original coefficient realization, and the full predictable
model. Drift control and stochastic matching are derived internally. -/
def build : Construction U C P := Classical.choice <| by
  classical
  have hloc : ∀ᵐ ω ∂Q, IntegrableOn
      (fun r => originalRawDrift M U.optimizer U.sampler.state r ω) (Ioc 0 (T : ℝ)) :=
    U.sampler.drift_integrable.mono (fun ω h =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp h)
  obtain ⟨L,b',hb',hdom,hbAE,hσAE,hnAE⟩ := U.sampler.localDiffusion.exists_withDriftEnergy_of_ae
    (originalRawDrift M U.optimizer U.sampler.state) hb hprog hloc
  have hinit : MemLp (U.sampler.state 0) 2 Q := by
    apply (memLp_two_iff_integrable_sq_norm
      (U.sampler.measurable 0 ⟨le_rfl,T.coe_nonneg⟩).stronglyMeasurable.aestronglyMeasurable).mpr
    exact (integrable_map_measure (by fun_prop)
      (U.sampler.measurable 0 ⟨le_rfl,T.coe_nonneg⟩).aemeasurable).mp
        (U.second_moment 0 ⟨le_rfl,T.coe_nonneg⟩)
  let V : RawLinearGrowthState.Data L C P := {
    state := U.sampler.state
    drift := b'
    drift_strong := hb'
    drift_control := hdom
    initial_square := hinit
    K_nonneg := hC
    P_nonneg := hP
    growth := by
      intro r hr
      filter_upwards [hbAE,hσAE,U.sampler.diffusion_realizes] with ω hbr hσr hmodel
      have he : (fun i => L.sigma i r ω) = M.diffusion (M.parameter (U.optimizer r)) (U.sampler.state r ω) := by
        funext i
        exact (hσr i r).trans (hmodel r hr i)
      rw [hbr r,he]
      exact (hgrowth (U.optimizer r) (U.sampler.state r ω)).trans (by gcongr; exact hparam r hr)
    equation := by
      filter_upwards [U.sampler.equation,hbAE,hnAE] with ω he hb hn
      intro r hr
      rw [he r hr,hn r.toNNReal ((Real.toNNReal_le_iff_le_coe).mpr hr.2)]
      congr 2
      exact intervalIntegral.integral_congr (fun s _ => (hb s).symm) }
  let R : RawLinearGrowthModel.Realization M L C P V := {
    optimizer := U.optimizer
    optimizerDrift r := M.optimizerField r (U.optimizer r) (Q.map (U.sampler.state r))
    optimizerDrift_integrable := U.optimizer_field_integrable
    state_adapted t := (U.sampler.adapted t).mono (filtration_le_nullAugmented Q D.filtration t)
    diffusion_borel := hσB
    drift_strong := hb
    diffusion_strong := hσ
    coefficients := by
      filter_upwards [hbAE,hσAE,U.sampler.diffusion_realizes] with ω hb hσ hm
      intro r hr
      exact ⟨hb r,fun i => (hσ i r).trans (hm r hr i)⟩
    optimizer_field := fun _ _ => rfl
    optimizer_equation := U.optimizer_equation
    observation_integrable := U.observation_integrable }
  exact ⟨⟨L,V,R,rfl,rfl⟩⟩

/-- The actual global predictable model associated to the original raw
solution. No coefficient moment or stochastic-energy input is supplied. -/
def predictableData : ConstructedPredictableModel.Data Q (nullAugmentedDriver Q D) M T :=
  (build U hb hprog hσ hσB C P hC hP hparam hgrowth).realization.predictableData

/-- The original optimizer is retained exactly. -/
theorem predictableData_optimizer :
    (predictableData U hb hprog hσ hσB C P hC hP hparam hgrowth).optimizer = U.optimizer :=
  (build U hb hprog hσ hσB C P hC hP hparam hgrowth).optimizer_eq

/-- Sampler sections are those of the original raw state itself. -/
theorem predictableData_sampler (r : ℝ) :
    (predictableData U hb hprog hσ hσB C P hC hP hparam hgrowth).sampler r =
      ProductLpSections.sectionLp Q U.sampler.state r := by
  let A := build U hb hprog hσ hσB C P hC hP hparam hgrowth
  change ProductLpSections.sectionLp Q A.stateData.state r = _
  rw [A.state_eq]

/-- The actual original marginal laws are preserved. -/
theorem predictableData_law (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    Q.map ((predictableData U hb hprog hσ hσB C P hC hP hparam hgrowth).sampler r) =
      Q.map (U.sampler.state r) := by
  let A := build U hb hprog hσ hσB C P hC hP hparam hgrowth
  have h := A.realization.predictableData_law r hr
  rw [A.state_eq] at h
  exact h

end PBGSO.RawSamplerGrowth

namespace PBGSO.RawSamplerGrowth
open FilteredBrownian RawLocalStationarity ConstructedPredictableModel
variable {Ω S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {M : Model S Θ Z X I} {T : ℝ≥0}

/-- Continuity of the actual optimizer follows from its original Bochner
integral equation and pathwise time-L¹ vector field. -/
theorem optimizer_continuous (U : RawLocalStationarity.Data Q D M T) :
    ContinuousOn U.optimizer (Icc 0 (T : ℝ)) := by
  have hc : ContinuousOn (fun r => U.optimizer 0+
      ∫ s in 0..r, M.optimizerField s (U.optimizer s) (Q.map (U.sampler.state s)))
      (uIcc 0 (T : ℝ)) :=
    continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval'
      U.optimizer_field_integrable (show (0 : ℝ) ∈ uIcc 0 (T : ℝ) from left_mem_uIcc))
  rw [uIcc_of_le T.coe_nonneg] at hc
  exact hc.congr U.optimizer_equation

/-- The finite-horizon parameter radius is derived from compactness of the
original optimizer path and continuity of the parameter projection. -/
theorem exists_parameter_bound (U : RawLocalStationarity.Data Q D M T)
    (hProjection : Continuous M.parameter) :
    ∃ P, 0 ≤ P ∧ ∀ r ∈ Icc 0 (T : ℝ), ‖M.parameter (U.optimizer r)‖ ≤ P := by
  obtain ⟨P,hP⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hProjection.comp_continuousOn (optimizer_continuous U))
  exact ⟨max P 0,le_max_right _ _,fun r hr => (hP r hr).trans (le_max_left _ _)⟩

/-- Primitive realization regularity and source linear growth. These fields
contain no coefficient moments, drift-control gauge, noise match, stopped
energy, or prescribed L²-valued solution curve. -/
structure Regularity (U : RawLocalStationarity.Data Q D M T) where
  drift_strong : StronglyMeasurable (Function.uncurry (originalRawDrift M U.optimizer U.sampler.state))
  drift_progressive : ∀ t : ℝ≥0,
    StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (D.filtration t)]
      (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator
        (fun r => originalRawDrift M U.optimizer U.sampler.state r p.2) p.1)
  diffusion_strong : ∀ i, StronglyMeasurable
    (Function.uncurry (originalRawDiffusion M U.optimizer U.sampler.state i))
  drift_borel : ∀ θ, Measurable (M.drift θ)
  diffusion_borel : ∀ θ i, Measurable (fun z => M.diffusion θ z i)
  projection_continuous : Continuous M.parameter
  growthConstant : ℝ
  growth_nonneg : 0 ≤ growthConstant
  linear_growth : ∀ s z, ‖M.drift (M.parameter s) z‖+
    ‖WithLp.toLp 2 (M.diffusion (M.parameter s) z)‖ ≤ growthConstant*(1+‖M.parameter s‖+‖z‖)

variable {U : RawLocalStationarity.Data Q D M T} (R : Regularity U)

def Regularity.parameterRadius : ℝ := (exists_parameter_bound U R.projection_continuous).choose

theorem Regularity.parameterRadius_nonneg : 0 ≤ R.parameterRadius :=
  (exists_parameter_bound U R.projection_continuous).choose_spec.1

theorem Regularity.parameterRadius_bound :
    ∀ r ∈ Icc 0 (T : ℝ), ‖M.parameter (U.optimizer r)‖ ≤ R.parameterRadius :=
  (exists_parameter_bound U R.projection_continuous).choose_spec.2

/-- Original natural strong equations instantiate the computed predictable
model with all global state/coefficient moments derived. -/
def Regularity.predictableData : ConstructedPredictableModel.Data Q (nullAugmentedDriver Q D) M T :=
  PBGSO.RawSamplerGrowth.predictableData U R.drift_strong R.drift_progressive R.diffusion_strong R.diffusion_borel
    R.growthConstant R.parameterRadius R.growth_nonneg R.parameterRadius_nonneg
    R.parameterRadius_bound R.linear_growth

theorem Regularity.predictableData_optimizer : R.predictableData.optimizer = U.optimizer :=
  PBGSO.RawSamplerGrowth.predictableData_optimizer U R.drift_strong R.drift_progressive R.diffusion_strong R.diffusion_borel
    R.growthConstant R.parameterRadius R.growth_nonneg R.parameterRadius_nonneg
    R.parameterRadius_bound R.linear_growth

theorem Regularity.predictableData_sampler (r : ℝ) :
    R.predictableData.sampler r = ProductLpSections.sectionLp Q U.sampler.state r :=
  PBGSO.RawSamplerGrowth.predictableData_sampler U R.drift_strong R.drift_progressive R.diffusion_strong R.diffusion_borel
    R.growthConstant R.parameterRadius R.growth_nonneg R.parameterRadius_nonneg
    R.parameterRadius_bound R.linear_growth r

theorem Regularity.predictableData_law (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    Q.map (R.predictableData.sampler r) = Q.map (U.sampler.state r) :=
  PBGSO.RawSamplerGrowth.predictableData_law U R.drift_strong R.drift_progressive R.diffusion_strong R.diffusion_borel
    R.growthConstant R.parameterRadius R.growth_nonneg R.parameterRadius_nonneg
    R.parameterRadius_bound R.linear_growth r hr

/-- Source A3 contracts actual original raw solutions in the primitive
linear-growth realization class on a common filtered Brownian source.
Global drift/diffusion L², stochastic isometry, martingale and matching
premises are all discharged by the actual construction. -/
theorem law_distance_decay (U V : RawLocalStationarity.Data Q D M T)
    (R : Regularity U) (R' : Regularity V) (G : TwistedGeometry S Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M G ρ) :
    optimizerLawDistance (U.optimizer T) (V.optimizer T)
      (Q.map (U.sampler.state T)) (Q.map (V.sampler.state T)) ≤
      Real.sqrt G.conditionNumber * Real.exp (-ρ * (T : ℝ)) *
        Real.sqrt (‖U.optimizer 0-V.optimizer 0‖ ^ 2+
          ‖ProductLpSections.sectionLp Q U.sampler.state 0-
            ProductLpSections.sectionLp Q V.sampler.state 0‖ ^ 2) := by
  have h := ConstructedPredictableModel.law_distance_decay G R.predictableData R'.predictableData
    R.drift_borel R.diffusion_borel ρ hmono
  rw [R.predictableData_optimizer,R'.predictableData_optimizer,
    R.predictableData_law T ⟨T.coe_nonneg,le_rfl⟩,R'.predictableData_law T ⟨T.coe_nonneg,le_rfl⟩,
    R.predictableData_sampler 0,R'.predictableData_sampler 0] at h
  exact h

end PBGSO.RawSamplerGrowth
