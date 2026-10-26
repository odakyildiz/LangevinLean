import PBGSO.ConstructedPredictableModel
import Mathlib.MeasureTheory.Measure.Prod

/-! # Stationarity for the actually constructed predictable Brownian integral
The frozen sampler solves the original computed integral equation. Its
constant-law property is the actual invariant-law assumption. Only uniqueness
of the displayed finite-horizon L¹-drift/time-L²-diffusion data class is used;
no equivalence with minimal strong-SDE A1 is asserted.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.ConstructedStationarity
open FilteredBrownian ConstructedPredictableModel
variable {Ω S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (M : Model S Θ Z X I) (T : ℝ≥0)

/-- Same-driver uniqueness restricted to the explicit actual-data class.
The inputs are original integral equations, not a stationarity or energy
conclusion. This is the exact well-posedness part needed below. -/
def DataUniqueness : Prop :=
  ∀ U V : Data Q D M T, U.optimizer 0 = V.optimizer 0 → U.sampler 0 = V.sampler 0 →
    ∀ t ∈ Icc 0 (T : ℝ), U.optimizer t = V.optimizer t ∧ U.sampler t = V.sampler t

/-- An actual invariant frozen sampler in the time-L¹(L²) drift and time-L²
diffusion realization class. The optimizer trajectory is deliberately absent:
it is constructed as a theorem below. The Brownian integral is the verified
computed integral, not an arbitrary supplied interpretation operator. -/
structure FrozenSamplerData (sStar : S) (νStar : Measure Z) where
  sampler : ℝ → Lp Z 2 Q
  drift : ℝ → Lp Z 2 Q
  diffusion : ℝ → ColumnHilbert (I := I) (Z := Z) Q
  drift_integrable : IntervalIntegrable drift volume 0 (T : ℝ)
  diffusion_square : MemLp diffusion 2 (volume.restrict (Ioc 0 (T : ℝ)))
  sampler_adapted : ∀ t : ℝ≥0, AEStronglyMeasurable[D.filtration t] (sampler t) Q
  diffusion_adapted : ∀ t : ℝ≥0, ∀ i,
    AEStronglyMeasurable[D.filtration t] (diffusion t i) Q
  sampler_integral : ∀ t ∈ Icc 0 (T : ℝ), sampler t = sampler 0 + (∫ r in 0..t, drift r) +
    ConstructedPredictableModel.integral Q D T diffusion diffusion_square diffusion_adapted t
  drift_realizes : ∀ t ∈ Icc 0 (T : ℝ), drift t =ᵐ[Q]
    fun ω => M.drift (M.parameter sStar) (sampler t ω)
  diffusion_realizes : ∀ t ∈ Icc 0 (T : ℝ), ∀ i, diffusion t i =ᵐ[Q]
    fun ω => M.diffusion (M.parameter sStar) (sampler t ω) i
  invariant_law : ∀ t ∈ Icc 0 (T : ℝ), Q.map (sampler t) = νStar

variable {Q D M T}

/-- Probability normalization follows from the actual frozen L² state. -/
theorem FrozenSamplerData.probability {sStar : S} {νStar : Measure Z}
    (F : FrozenSamplerData Q D M T sStar νStar) : IsProbabilityMeasure νStar := by
  have he := F.invariant_law 0 ⟨le_rfl, T.coe_nonneg⟩
  rw [← he]
  exact (Measure.isProbabilityMeasure_map_iff (Lp.aestronglyMeasurable _).aemeasurable).mpr inferInstance

/-- The actual frozen invariant law has the source P₂ moment; this is a
conclusion of the L² realization rather than an extra law-moment premise. -/
theorem FrozenSamplerData.second_moment {sStar : S} {νStar : Measure Z}
    (F : FrozenSamplerData Q D M T sStar νStar) : HasFiniteSecondMoment νStar := by
  rw [← F.invariant_law 0 ⟨le_rfl, T.coe_nonneg⟩]
  exact lp_law_second_moment Q (F.sampler 0)

/-- The constant optimizer and zero optimizer drift are constructed from
frozen sampler invariance, the exact zero gradient and optimizer fixed point.
No optimizer derivative or preexisting mean-field solution is an input. -/
def FrozenSamplerData.constantData {sStar : S} {νStar : Measure Z}
    (F : FrozenSamplerData Q D M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0) : Data Q D M T where
  optimizer _ := sStar
  optimizerDrift _ := 0
  sampler := F.sampler
  drift := F.drift
  diffusion := F.diffusion
  optimizerDrift_integrable := intervalIntegrable_const
  drift_integrable := F.drift_integrable
  diffusion_square := F.diffusion_square
  sampler_adapted := F.sampler_adapted
  diffusion_adapted := F.diffusion_adapted
  optimizerDrift_realizes := by
    intro t ht
    change 0 = M.optimizer t sStar (M.meanGradient (Q.map (F.sampler t)) sStar)
    rw [F.invariant_law t ht, hg, hfix t ht]
  optimizer_integral := by intro t _; simp only [intervalIntegral.integral_zero, add_zero]
  sampler_integral := F.sampler_integral
  drift_realizes := F.drift_realizes
  diffusion_realizes := F.diffusion_realizes
  observation_integrable := by
    intro t ht
    rw [F.invariant_law t ht]
    exact hint

/-- Original computed integral data with the invariant frozen initial state
have exactly constant optimizer and the frozen invariant sampler law. -/
theorem stationary_of_frozen (hunique : DataUniqueness Q D M T)
    {sStar : S} {νStar : Measure Z} (F : FrozenSamplerData Q D M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0)
    (U : Data Q D M T) (hs : U.optimizer 0 = sStar) (hz : U.sampler 0 = F.sampler 0)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    U.optimizer t = sStar ∧ Q.map (U.sampler t) = νStar := by
  have hu := hunique U (F.constantData hint hg hfix) hs hz t ht
  refine ⟨hu.1, ?_⟩
  rw [hu.2]
  exact F.invariant_law t ht

/-- The full stationary state law is literally δ_sStar × νStar, retaining
all optimizer and sampler auxiliary coordinates and arbitrary diffusion. -/
theorem stationary_product_law [MeasurableSpace S] (hunique : DataUniqueness Q D M T)
    {sStar : S} {νStar : Measure Z} (F : FrozenSamplerData Q D M T sStar νStar)
    (hint : Integrable (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t ∈ Icc 0 (T : ℝ), M.optimizer t sStar 0 = 0)
    (U : Data Q D M T) (hs : U.optimizer 0 = sStar) (hz : U.sampler 0 = F.sampler 0)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    Q.map (fun ω => (U.optimizer t, U.sampler t ω)) = (Measure.dirac sStar).prod νStar := by
  obtain ⟨hopt, hsam⟩ := stationary_of_frozen hunique F hint hg hfix U hs hz t ht
  have hm : Measurable (U.sampler t : Ω → Z) := (Lp.stronglyMeasurable _).measurable
  haveI : IsProbabilityMeasure νStar := hsam ▸
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  rw [hopt, Measure.dirac_prod, ← hsam, Measure.map_map measurable_prodMk_left hm]
  rfl

end PBGSO.ConstructedStationarity
