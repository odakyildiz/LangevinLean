import PBGSO.ClosedIntegralMartingale
import PBGSO.ClosedStepAlgebra

/-! # Exact increments and time continuity of arbitrary completed integrals -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
open PBGSO.QuadraticMartingale
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

theorem timeCut_norm_sq
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (s t : ℝ) :
    ‖timeCut Q U s t‖ ^ 2 = ∫ r in Ioc s t, ‖U r‖ ^ 2 := by
  rw [ProximalLangevin.lp_norm_sq_eq_integral, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [timeCut_coe Q U s t] with r hr
  rw [hr]
  by_cases hm : r ∈ Ioc s t
  · simp only [Set.indicator_of_mem hm]
  · simp only [Set.indicator_of_notMem hm, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]

/-- Every deterministic cut of a completed integrand has the exact weighted
Brownian increment moment, now derived on the whole closed domain. -/
theorem closedIntegral_increment_isometry (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    weightedPairing Q W (closedIntegral Q D T U t - closedIntegral Q D T U s)
      (closedIntegral Q D T U t - closedIntegral Q D T U s) =
      ∫ r in Ioc (s : ℝ) t, ∑ i, weightedPairing Q W ((U.val r).ofLp i) ((U.val r).ofLp i) := by
  rw [closedIntegral, closedIntegral, ← closedStepIntegral_sub,
    closedStepIntegral_weighted Q D W hW]
  change ⟪timeCut Q U.val 0 t - timeCut Q U.val 0 s,
    (columnWeight (I := I) Q W).compLpL 2 (volume : Measure ℝ)
      (timeCut Q U.val 0 t - timeCut Q U.val 0 s)⟫_ℝ = _
  rw [timeCut_sub Q U.val s t s.coe_nonneg (by exact_mod_cast hst), timeCut_weighted]

@[simp] theorem timeCut_same
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (t : ℝ) :
    timeCut Q U t t = 0 := by
  apply Lp.ext
  filter_upwards [timeCut_coe Q U t t, Lp.coeFn_zero (ColumnHilbert (I := I) (Z := Z) Q) 2 volume]
    with r hr hz
  rw [hr, hz]
  simp only [Ioc_self, Set.indicator_empty, Pi.zero_apply]

@[simp] theorem closedIntegral_zero (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) : closedIntegral Q D T U 0 = 0 := by
  have he : closedCutDomain Q D T U 0 0 = closedSub Q D (dyadicGrids T) U U := by
    apply Subtype.ext
    change timeCut Q U.val 0 0 = U.val - U.val
    rw [timeCut_same, sub_self]
  rw [closedIntegral, NNReal.coe_zero, he, closedStepIntegral_sub, sub_self]

/-- The expected squared stochastic increment is exactly the actual time-L²
energy of the diffusion columns. No coefficient continuity is required. -/
theorem closedIntegral_increment_norm_sq (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖closedIntegral Q D T U t - closedIntegral Q D T U s‖ ^ 2 =
      ∫ r in Ioc (s : ℝ) t, ‖U.val r‖ ^ 2 := by
  have he := (closedStepIntegral_isometry (Z := Z) Q D (dyadicGrids T)).dist_eq
    (closedCutDomain Q D T U 0 t) (closedCutDomain Q D T U 0 s)
  simp only [dist_eq_norm, Subtype.dist_eq, closedCutDomain] at he
  change ‖closedIntegral Q D T U t - closedIntegral Q D T U s‖ =
    ‖timeCut Q U.val 0 t - timeCut Q U.val 0 s‖ at he
  rw [he, timeCut_sub Q U.val s t s.coe_nonneg (by exact_mod_cast hst), timeCut_norm_sq]

/-- The increment norm is controlled by an actual absolutely continuous
primitive of the square-integrable diffusion energy. -/
theorem closedIntegral_increment_primitive (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (s t : ℝ≥0) :
    ‖closedIntegral Q D T U t - closedIntegral Q D T U s‖ ^ 2 =
      |(∫ r in 0..(t : ℝ), ‖U.val r‖ ^ 2) - (∫ r in 0..(s : ℝ), ‖U.val r‖ ^ 2)| := by
  have hi : Integrable (fun r : ℝ => ‖U.val r‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp U.val).aestronglyMeasurable).mp (Lp.memLp U.val)
  wlog hst : s ≤ t generalizing s t
  · rw [norm_sub_rev, abs_sub_comm]
    exact this t s (le_of_not_ge hst)
  rw [closedIntegral_increment_norm_sq Q D T U s t hst,
    intervalIntegral.integral_interval_sub_left hi.intervalIntegrable hi.intervalIntegrable,
    intervalIntegral.integral_of_le (by exact_mod_cast hst)]
  exact (abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))).symm

/-- Actual time-L² integrands give an L²-continuous computed Brownian integral.
Time continuity and a uniform coefficient bound are both conclusions or
unnecessary; neither is an input hypothesis on the diffusion columns. -/
theorem closedIntegral_continuous (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    Continuous (closedIntegral Q D T U) := by
  have hi : Integrable (fun r : ℝ => ‖U.val r‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp U.val).aestronglyMeasurable).mp (Lp.memLp U.val)
  have hF : Continuous (fun t : ℝ≥0 => ∫ r in 0..(t : ℝ), ‖U.val r‖ ^ 2) :=
    (intervalIntegral.continuous_primitive (fun _ _ => hi.intervalIntegrable) 0).comp continuous_subtype_val
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs := ((hF.tendsto t).sub_const (∫ r in 0..(t : ℝ), ‖U.val r‖ ^ 2)).abs
  have hs' : Tendsto (fun s : ℝ≥0 => ‖closedIntegral Q D T U s - closedIntegral Q D T U t‖ ^ 2)
      (𝓝 t) (𝓝 0) := by
    simpa only [closedIntegral_increment_primitive Q D T U, sub_self, abs_zero] using hs
  have hn := (Real.continuous_sqrt.tendsto 0).comp hs'
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn

/-- The actual Brownian integral of a time-L² family adapted only almost
everywhere in time. Density and its domain membership are derived. -/
def predictableIntegral (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) (t : ℝ≥0) : Lp Z 2 Q :=
  closedIntegral Q D T (predictableDomain Q D T U hU) t

theorem predictableIntegral_martingale (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) :
    Martingale (MartingaleL2Limit.representative Q D.filtration (predictableIntegral Q D T U hU))
      D.filtration Q := closedIntegral_martingale Q D T _

theorem predictableIntegral_continuous (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) : Continuous (predictableIntegral Q D T U hU) :=
  closedIntegral_continuous Q D T _

@[simp] theorem predictableIntegral_zero (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) : predictableIntegral Q D T U hU 0 = 0 :=
  closedIntegral_zero Q D T _

/-- Exact weighted increment identity for merely time-square-integrable
adapted columns, with the displayed original coefficient family on the RHS. -/
theorem predictableIntegral_increment_isometry (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U)
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T) :
    weightedPairing Q W (predictableIntegral Q D T U hU t - predictableIntegral Q D T U hU s)
      (predictableIntegral Q D T U hU t - predictableIntegral Q D T U hU s) =
      ∫ r in Ioc (s : ℝ) t, ∑ i, weightedPairing Q W ((U r).ofLp i) ((U r).ofLp i) := by
  rw [predictableIntegral, predictableIntegral, closedIntegral_increment_isometry Q D T _ W hW s t hst]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (timeCut_coe Q U 0 T), ae_restrict_mem measurableSet_Ioc]
    with r hr hm
  have hR : r ∈ Ioc 0 (T : ℝ) :=
    ⟨lt_of_le_of_lt s.coe_nonneg hm.1, hm.2.trans (by exact_mod_cast ht)⟩
  change (timeCut Q U 0 T) r = _ at hr
  rw [Set.indicator_of_mem hR] at hr
  change (∑ i, weightedPairing Q W (((timeCut Q U 0 T) r).ofLp i)
    (((timeCut Q U 0 T) r).ofLp i)) = _
  rw [hr]

end PBGSO.FilteredBrownian
