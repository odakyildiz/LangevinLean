import PBGSO.FilteredWeightedCompletion
import PBGSO.TimeGridContinuity

/-! # Continuous adapted diffusion columns belong to the constructed integral domain
Actual adapted representatives and literal dyadic convergence are derived.
Deterministic interval cuts are included, so an increment domain does not
require a separately supplied approximation or density premise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Choose actual adapted representatives of given L² coefficient columns. -/
def coefficientOfLp (t : ℝ≥0) (U : ColumnHilbert (I := I) (Z := Z) Q)
    (hU : ∀ i, AEStronglyMeasurable[D.filtration t] (U i) Q) :
    Coefficient (Z := Z) Q D t where
  value i := (hU i).mk (U i)
  adapted i := (hU i).stronglyMeasurable_mk
  square i := (memLp_congr_ae (hU i).ae_eq_mk).mp (Lp.memLp (U i))

/-- The chosen adapted representatives have exactly the original L² columns. -/
theorem coefficientOfLp_toLp (t : ℝ≥0) (U : ColumnHilbert (I := I) (Z := Z) Q)
    (hU : ∀ i, AEStronglyMeasurable[D.filtration t] (U i) Q) :
    (coefficientOfLp Q D t U hU).toLp = U := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  exact ((coefficientOfLp Q D t U hU).square i).coeFn_toLp.trans (hU i).ae_eq_mk.symm

/-- Actual dyadic predictable coefficients of a time curve. -/
def curveCoefficients (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (τ : ℕ → ℝ≥0) : Coefficients (Z := Z) Q D τ :=
  fun k => coefficientOfLp Q D (τ k) (u (τ k)) (hU (τ k))

/-- The actual adapted step embedding is the literal left-sampled time grid. -/
theorem curveCoefficients_step (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (τ : ℕ → ℝ≥0) (n : ℕ) :
    coefficientStep Q D τ (curveCoefficients Q D u hU τ) n =
      TimeGridEnergy.grid τ (fun k => u (τ k)) n := by
  simp only [coefficientStep, curveCoefficients, coefficientOfLp_toLp]

/-- Bounded a.e.-continuous adapted columns enter the actual completion domain;
no supplied step-approximation or stochastic-integral conclusion is needed. -/
def boundedContinuousDomain (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hum : AEStronglyMeasurable u (volume : Measure ℝ)) (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P)
    (hc : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)), ContinuousAt u r)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    IntegralDomain (Z := Z) Q D (GridIntegralCompletion.dyadicGrids T) := by
  refine ⟨TimeGridContinuity.horizonLp T u hum P hP, ?_⟩
  refine ⟨fun n => curveCoefficients Q D u hU ((GridIntegralCompletion.dyadicGrids T).time n), ?_⟩
  simpa only [curveCoefficients_step] using
    TimeGridContinuity.dyadic_grid_tendsto T u hum P hP0 hP hc

/-- The domain entry represents the literal finite-horizon diffusion curve. -/
theorem boundedContinuousDomain_coe (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hum : AEStronglyMeasurable u (volume : Measure ℝ)) (P : ℝ) (hP0 : 0 ≤ P)
    (hP : ∀ r ∈ Icc 0 (T : ℝ), ‖u r‖ ≤ P)
    (hc : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)), ContinuousAt u r)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    (boundedContinuousDomain Q D T u hum P hP0 hP hc hU).val =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator u :=
  (TimeGridContinuity.horizon_memLp T u hum P hP).coeFn_toLp

/-- Compactness derives a finite-horizon bound; continuous adapted diffusion
columns therefore have a constructed integral without any radius premise. -/
theorem exists_continuous_domain (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    ∃ U : IntegralDomain (Z := Z) Q D (GridIntegralCompletion.dyadicGrids T),
      U.val =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator u := by
  obtain ⟨P, hP0, hP⟩ := TimeGridContinuity.exists_horizon_bound T u hu
  let hc := ae_of_all ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))
    (fun r => hu.continuousAt (x := r))
  exact ⟨boundedContinuousDomain Q D T u hu.aestronglyMeasurable P hP0 hP hc hU,
    boundedContinuousDomain_coe Q D T u hu.aestronglyMeasurable P hP0 hP hc hU⟩

/-- Deterministic time cuts preserve actual adaptedness of every L² column. -/
theorem masked_columns_adapted (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (s t : ℝ) (r : ℝ≥0) (i : I) :
    AEStronglyMeasurable[D.filtration r] (((Ioc s t).indicator u) r i) Q := by
  by_cases hr : (r : ℝ) ∈ Ioc s t
  · simpa only [Set.indicator_of_mem hr] using hU r i
  · rw [Set.indicator_of_notMem hr]
    change AEStronglyMeasurable[D.filtration r] ((0 : Lp Z 2 Q) : Ω → Z) Q
    exact aestronglyMeasurable_zero.congr (Lp.coeFn_zero Z 2 Q).symm

/-- Every deterministic interval cut of a continuous adapted diffusion curve
belongs to the actual domain. Its two boundary discontinuities are proved null. -/
theorem exists_masked_continuous_domain (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (s t : ℝ) :
    ∃ U : IntegralDomain (Z := Z) Q D (GridIntegralCompletion.dyadicGrids T),
      U.val =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator ((Ioc s t).indicator u) := by
  obtain ⟨P, hP0, hP⟩ := TimeGridContinuity.exists_horizon_bound T u hu
  let v := (Ioc s t).indicator u
  have hvm : AEStronglyMeasurable v (volume : Measure ℝ) :=
    hu.aestronglyMeasurable.indicator measurableSet_Ioc
  have hvP : ∀ r ∈ Icc 0 (T : ℝ), ‖v r‖ ≤ P := fun r hr =>
    (norm_indicator_le_norm_self u r).trans (hP r hr)
  have hc : ∀ᵐ r ∂(volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)), ContinuousAt v r :=
    ae_restrict_of_ae (TimeGridContinuity.continuous_mask_ae u hu s t)
  have hva := masked_columns_adapted Q D u hU s t
  exact ⟨boundedContinuousDomain Q D T v hvm P hP0 hvP hc hva,
    boundedContinuousDomain_coe Q D T v hvm P hP0 hvP hc hva⟩

/-- Cuts contained in the horizon represent exactly the displayed interval
integrand, with no extra initial-horizon indicator remaining. -/
theorem exists_interval_continuous_domain (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ T) :
    ∃ U : IntegralDomain (Z := Z) Q D (GridIntegralCompletion.dyadicGrids T),
      U.val =ᵐ[volume] (Ioc s t).indicator u := by
  obtain ⟨U, hU⟩ := exists_masked_continuous_domain Q D T u hu hU s t
  refine ⟨U, hU.trans (ae_of_all _ fun r => ?_)⟩
  by_cases hr : r ∈ Ioc s t
  · have hR : r ∈ Ioc 0 (T : ℝ) := ⟨lt_of_le_of_lt hs hr.1, hr.2.trans ht⟩
    rw [Set.indicator_of_mem hR]
  · rw [Set.indicator_of_notMem hr]
    exact Set.indicator_apply_eq_zero.mpr (fun _ => Set.indicator_of_notMem hr _)



/-- A concrete actual domain entry for the full finite-horizon curve. -/
def continuousDomain (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    IntegralDomain (Z := Z) Q D (GridIntegralCompletion.dyadicGrids T) :=
  Classical.choose (exists_continuous_domain Q D T u hu hU)

theorem continuousDomain_coe (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    (continuousDomain Q D T u hu hU).val =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator u :=
  Classical.choose_spec (exists_continuous_domain Q D T u hu hU)

/-- A concrete actual domain entry for each interval in the horizon. -/
def continuousIntervalDomain (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ T) :
    IntegralDomain (Z := Z) Q D (GridIntegralCompletion.dyadicGrids T) :=
  Classical.choose (exists_interval_continuous_domain Q D T u hu hU s t hs ht)

theorem continuousIntervalDomain_coe (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ T) :
    (continuousIntervalDomain Q D T u hu hU s t hs ht).val =ᵐ[volume] (Ioc s t).indicator u :=
  Classical.choose_spec (exists_interval_continuous_domain Q D T u hu hU s t hs ht)

/-- The actual interval entry equals a literal time cut of the full entry.
This proves the input identities required by the stochastic increment theorem. -/
theorem continuousIntervalDomain_eq_timeCut (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (s t : ℝ) (hs : 0 ≤ s) (ht : t ≤ T) :
    (continuousIntervalDomain Q D T u hu hU s t hs ht).val =
      timeCut Q (continuousDomain Q D T u hu hU).val s t := by
  apply Lp.ext
  filter_upwards [continuousIntervalDomain_coe Q D T u hu hU s t hs ht,
    timeCut_coe Q (continuousDomain Q D T u hu hU).val s t,
    continuousDomain_coe Q D T u hu hU] with r hinterval hcut hfull
  rw [hinterval, hcut]
  by_cases hr : r ∈ Ioc s t
  · have hR : r ∈ Ioc 0 (T : ℝ) := ⟨lt_of_le_of_lt hs hr.1, hr.2.trans ht⟩
    rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, hfull, Set.indicator_of_mem hR]
  · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]

/-- The completed integrals of continuous adapted diffusion columns have
an exact weighted increment isometry with every input-domain identity derived. -/
theorem continuous_integral_increment_isometry (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    QuadraticMartingale.weightedPairing Q W
      (stochasticIntegral Q D (GridIntegralCompletion.dyadicGrids T)
        (continuousIntervalDomain Q D T u hu hU 0 t le_rfl ht) -
       stochasticIntegral Q D (GridIntegralCompletion.dyadicGrids T)
        (continuousIntervalDomain Q D T u hu hU 0 s le_rfl (hst.trans ht)))
      (stochasticIntegral Q D (GridIntegralCompletion.dyadicGrids T)
        (continuousIntervalDomain Q D T u hu hU 0 t le_rfl ht) -
       stochasticIntegral Q D (GridIntegralCompletion.dyadicGrids T)
        (continuousIntervalDomain Q D T u hu hU 0 s le_rfl (hst.trans ht))) =
      ∫ r in Ioc s t, ∑ i, QuadraticMartingale.weightedPairing Q W (u r i) (u r i) := by
  rw [stochasticIntegral_increment_isometry Q D W hW
    (GridIntegralCompletion.dyadicGrids T) (continuousDomain Q D T u hu hU).val s t hs hst
    _ _ (continuousIntervalDomain_eq_timeCut Q D T u hu hU 0 s le_rfl (hst.trans ht))
    (continuousIntervalDomain_eq_timeCut Q D T u hu hU 0 t le_rfl ht)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (continuousDomain_coe Q D T u hu hU),
    ae_restrict_mem measurableSet_Ioc] with r hr hmem
  have hR : r ∈ Ioc 0 (T : ℝ) := ⟨lt_of_le_of_lt hs hmem.1, hmem.2.trans ht⟩
  rw [Set.indicator_of_mem hR] at hr
  rw [hr]

end PBGSO.FilteredBrownian
