import PBGSO.RawLocalIntegral
import PBGSO.Framework
import Mathlib.MeasureTheory.Measure.Prod

/-! # Source stationarity in the actual local strong-equation class
The stochastic noise is the constructed local Brownian integral, not a free
interpretation operator. Only pathwise time-L¹ drift and local square diffusion
are required. Source A1 is exposed as same-driver pathwise uniqueness in this
class; actual frozen invariance is source A2. Neither an energy identity nor
time-L¹(L²) drift is used in the stationarity argument.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawLocalStationarity
open FilteredBrownian
variable {Ω S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D : Driver (I := I) Q) (M : Model S Θ Z X I) (T : ℝ≥0)

/-- Original raw sampler equation with actual constructed local Brownian
noise. The local coefficients may be normalized on a common null event;
their realization as the original model coefficients is stated explicitly.
Pathwise Bochner integrability does not imply a time-L¹(L²) assumption here. -/
structure SamplerData (a : ℝ → S) where
  localDiffusion : RawLocalDiffusion (Z := Z) Q D T
  state : ℝ → Ω → Z
  measurable : ∀ t ∈ Icc 0 (T : ℝ), Measurable (state t)
  adapted : ∀ t : ℝ≥0, AEStronglyMeasurable[D.filtration t] (state t) Q
  continuous_paths : ∀ᵐ ω ∂Q, ContinuousOn (fun t => state t ω) (Icc 0 (T : ℝ))
  drift_integrable : ∀ᵐ ω ∂Q, IntervalIntegrable
    (fun r => M.drift (M.parameter (a r)) (state r ω)) volume 0 (T : ℝ)
  diffusion_realizes : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ), ∀ i,
    localDiffusion.sigma i t ω = M.diffusion (M.parameter (a t)) (state t ω) i
  equation : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ), state t ω = state 0 ω +
    (∫ r in 0..t, M.drift (M.parameter (a r)) (state r ω)) +
      localDiffusion.localNoise t.toNNReal ω

/-- Original mean-field optimiser integral ODE and actual local sampler equation.
The marginal P₂/observation domains are explicit source assumptions. -/
structure Data where
  optimizer : ℝ → S
  sampler : SamplerData Q D M T optimizer
  second_moment : ∀ t ∈ Icc 0 (T : ℝ), HasFiniteSecondMoment (Q.map (sampler.state t))
  observation_integrable : ∀ t ∈ Icc 0 (T : ℝ), Integrable
    (fun z => M.observation (M.parameter (optimizer t)) (M.position z))
      (Q.map (sampler.state t))
  optimizer_field_integrable : IntervalIntegrable
    (fun t => M.optimizerField t (optimizer t) (Q.map (sampler.state t))) volume 0 (T : ℝ)
  optimizer_equation : ∀ t ∈ Icc 0 (T : ℝ), optimizer t = optimizer 0 +
    ∫ r in 0..t, M.optimizerField r (optimizer r) (Q.map (sampler.state r))

/-- The same-driver uniqueness conclusion needed from source A1, now for
actual computed local integrals. It quantifies over local energy choices and
common-null coefficient realizations, rather than assuming identical gauges. -/
def PathwiseUniqueness : Prop :=
  ∀ U V : Data Q D M T, U.optimizer 0 = V.optimizer 0 →
    U.sampler.state 0 =ᵐ[Q] V.sampler.state 0 → ∀ t ∈ Icc 0 (T : ℝ),
      U.optimizer t = V.optimizer t ∧ U.sampler.state t =ᵐ[Q] V.sampler.state t

/-- Source A2 as an actual invariant frozen sampler trajectory satisfying
the original locally integrable SDE. Its original optimiser is not supplied:
the constant optimiser solution is constructed from the zero-gradient rule. -/
structure FrozenSamplerData (sStar : S) (νStar : Measure Z) extends
    SamplerData Q D M T (fun _ => sStar) where
  initial_square : MemLp (state 0) 2 Q
  invariant_law : ∀ t ∈ Icc 0 (T : ℝ), Q.map (state t) = νStar

variable {Q D M T}

/-- Normalization is derived from the actual invariant frozen output. -/
theorem FrozenSamplerData.probability {sStar : S} {νStar : Measure Z}
    (F : FrozenSamplerData Q D M T sStar νStar) : IsProbabilityMeasure νStar := by
  rw [← F.invariant_law 0 ⟨le_rfl, T.coe_nonneg⟩]
  exact (Measure.isProbabilityMeasure_map_iff
    (F.measurable 0 ⟨le_rfl, T.coe_nonneg⟩).aemeasurable).mpr inferInstance

/-- The frozen invariant law's second moment follows from its original
initial L² variable; no all-time coefficient moment is assumed. -/
theorem FrozenSamplerData.second_moment {sStar : S} {νStar : Measure Z}
    (F : FrozenSamplerData Q D M T sStar νStar) : HasFiniteSecondMoment νStar := by
  rw [← F.invariant_law 0 ⟨le_rfl, T.coe_nonneg⟩]
  apply (integrable_map_measure (by fun_prop)
    (F.measurable 0 ⟨le_rfl, T.coe_nonneg⟩).aemeasurable).mpr
  exact (memLp_two_iff_integrable_sq_norm
    (F.measurable 0 ⟨le_rfl, T.coe_nonneg⟩).stronglyMeasurable.aestronglyMeasurable).mp
      F.initial_square

/-- The zero optimiser drift is proved from actual frozen invariance,
zero mean gradient and the optimiser fixed point. The original local sampler
equation is retained verbatim, including arbitrary multiplicative diffusion. -/
def FrozenSamplerData.constantData {sStar : S} {νStar : Measure Z}
    (F : FrozenSamplerData Q D M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0) : Data Q D M T where
  optimizer _ := sStar
  sampler := F.toSamplerData
  second_moment t ht := by rw [F.invariant_law t ht]; exact F.second_moment
  observation_integrable t ht := by rw [F.invariant_law t ht]; exact hint
  optimizer_field_integrable := by
    apply (intervalIntegrable_congr (g := fun _ => (0 : S)) ?_).mpr intervalIntegrable_const
    intro r hr
    rw [uIoc_of_le T.coe_nonneg] at hr
    simp only [Model.optimizerField, F.invariant_law r (Ioc_subset_Icc_self hr), hg,
      hfix r (Ioc_subset_Icc_self hr)]
  optimizer_equation t ht := by
    have hi : (∫ r in 0..t, M.optimizerField r sStar (Q.map (F.state r))) = 0 := by
      calc
        _ = ∫ _r in 0..t, (0 : S) := by
          apply intervalIntegral.integral_congr
          intro r hr
          rw [uIcc_of_le ht.1] at hr
          have hrT : r ∈ Icc 0 (T : ℝ) := ⟨hr.1, hr.2.trans ht.2⟩
          simp only [Model.optimizerField, F.invariant_law r hrT, hg, hfix r hrT]
        _ = 0 := intervalIntegral.integral_zero
    simpa only [hi, add_zero]

/-- Source invariant-measure conclusion using the actual local Brownian
integral and only source pathwise uniqueness, frozen invariance, zero gradient
and optimiser fixed-point assumptions. No stronger drift moment or energy
hypothesis is introduced. -/
theorem stationary_of_frozen (hunique : PathwiseUniqueness Q D M T)
    {sStar : S} {νStar : Measure Z} (F : FrozenSamplerData Q D M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0)
    (U : Data Q D M T) (hs : U.optimizer 0 = sStar)
    (hz : U.sampler.state 0 =ᵐ[Q] F.state 0)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    U.optimizer t = sStar ∧ Q.map (U.sampler.state t) = νStar := by
  have hu := hunique U (F.constantData hint hg hfix) hs hz t ht
  exact ⟨hu.1, (Measure.map_congr hu.2).trans (F.invariant_law t ht)⟩

/-- Literal complete-state stationary product law. Optimiser and sampler
auxiliary variables remain in their original state spaces. -/
theorem stationary_product_law [MeasurableSpace S]
    (hunique : PathwiseUniqueness Q D M T)
    {sStar : S} {νStar : Measure Z} (F : FrozenSamplerData Q D M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0)
    (U : Data Q D M T) (hs : U.optimizer 0 = sStar)
    (hz : U.sampler.state 0 =ᵐ[Q] F.state 0)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Q.map (fun ω => (U.optimizer t, U.sampler.state t ω)) =
      (Measure.dirac sStar).prod νStar := by
  obtain ⟨hopt, hsam⟩ := stationary_of_frozen hunique F hint hg hfix U hs hz t ht
  have hm := U.sampler.measurable t ht
  haveI : IsProbabilityMeasure νStar := F.probability
  rw [hopt, Measure.dirac_prod, ← hsam, Measure.map_map measurable_prodMk_left hm]
  rfl

end PBGSO.RawLocalStationarity
