import PBGSO.ClosedIntegralEnergy

/-! # Actual integration of merely time-square-integrable adapted diffusion curves -/
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

theorem curveHorizon_memLp (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))) :
    MemLp ((Ioc 0 (T : ℝ)).indicator u) 2 (volume : Measure ℝ) :=
  (memLp_indicator_iff_restrict measurableSet_Ioc).mpr hu

/-- The actual finite-horizon time-L² class. No boundedness or continuous-time
coefficient representative is assumed. -/
def curveHorizon (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))) :
    Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) :=
  (curveHorizon_memLp Q T u hu).toLp ((Ioc 0 (T : ℝ)).indicator u)

theorem curveHorizon_coe (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))) :
    curveHorizon Q T u hu =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator u :=
  (curveHorizon_memLp Q T u hu).coeFn_toLp

/-- Adaptedness of the horizon class follows from actual coefficient
adaptedness and filtration monotonicity, including its zero extension. -/
theorem curveHorizon_pastAdapted (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q) :
    PastAdaptedColumns Q D (curveHorizon Q T u hu) := by
  apply pastAdaptedColumns_congr Q D ((Ioc 0 (T : ℝ)).indicator u)
    (curveHorizon Q T u hu) (curveHorizon_coe Q T u hu).symm
  apply pastAdaptedColumns_of_adapted Q D
  · intro r hr
    exact Set.indicator_of_notMem (fun hm : r ∈ Ioc 0 (T : ℝ) => (not_lt_of_gt hr) hm.1) _
  · exact masked_columns_adapted Q D u hU 0 T

/-- The actual computed Brownian integral of merely time-L² adapted columns. -/
def predictableCurveIntegral (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q)
    (t : ℝ≥0) : Lp Z 2 Q :=
  predictableIntegral Q D T (curveHorizon Q T u hu) (curveHorizon_pastAdapted Q D T u hu hU) t

theorem predictableCurveIntegral_martingale (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q) :
    Martingale (MartingaleL2Limit.representative Q D.filtration (predictableCurveIntegral Q D T u hu hU))
      D.filtration Q := predictableIntegral_martingale Q D T _ _

theorem predictableCurveIntegral_representative_ae (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q) (t : ℝ≥0) :
    MartingaleL2Limit.representative Q D.filtration (predictableCurveIntegral Q D T u hu hU) t =ᵐ[Q]
      predictableCurveIntegral Q D T u hu hU t :=
  closedIntegral_representative_ae Q D T _ t

theorem predictableCurveIntegral_representative_memLp (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q) (t : ℝ≥0) :
    MemLp (MartingaleL2Limit.representative Q D.filtration (predictableCurveIntegral Q D T u hu hU) t) 2 Q :=
  closedIntegral_representative_memLp Q D T _ t

theorem predictableCurveIntegral_continuous (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q) :
    Continuous (predictableCurveIntegral Q D T u hu hU) :=
  predictableIntegral_continuous Q D T _ _

@[simp] theorem predictableCurveIntegral_zero (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q) :
    predictableCurveIntegral Q D T u hu hU 0 = 0 := predictableIntegral_zero Q D T _ _

/-- Exact weighted stochastic increment moments are derived from the raw
adapted time-L² diffusion columns. No isometry/noise-radius premise remains. -/
theorem predictableCurveIntegral_increment_isometry (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q)
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ T) :
    weightedPairing Q W (predictableCurveIntegral Q D T u hu hU t - predictableCurveIntegral Q D T u hu hU s)
      (predictableCurveIntegral Q D T u hu hU t - predictableCurveIntegral Q D T u hu hU s) =
      ∫ r in Ioc (s : ℝ) t, ∑ i, weightedPairing Q W ((u r).ofLp i) ((u r).ofLp i) := by
  rw [predictableCurveIntegral, predictableCurveIntegral,
    predictableIntegral_increment_isometry Q D T _ _ W hW s t hst ht]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (curveHorizon_coe Q T u hu), ae_restrict_mem measurableSet_Ioc]
    with r hr hm
  have hR : r ∈ Ioc 0 (T : ℝ) :=
    ⟨lt_of_le_of_lt s.coe_nonneg hm.1, hm.2.trans (by exact_mod_cast ht)⟩
  rw [Set.indicator_of_mem hR] at hr
  rw [hr]

theorem curveHorizon_sub (T : ℝ≥0)
    (u v : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hv : MemLp v 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))) :
    curveHorizon Q T (u - v) (hu.sub hv) = curveHorizon Q T u hu - curveHorizon Q T v hv := by
  apply Lp.ext
  filter_upwards [curveHorizon_coe Q T (u - v) (hu.sub hv), curveHorizon_coe Q T u hu,
    curveHorizon_coe Q T v hv, Lp.coeFn_sub (curveHorizon Q T u hu) (curveHorizon Q T v hv)]
    with r hs h1 h2 hsub
  rw [hsub, Pi.sub_apply, hs, h1, h2]
  by_cases hr : r ∈ Ioc 0 (T : ℝ)
  · simp only [Set.indicator_of_mem hr, Pi.sub_apply]
  · simp only [Set.indicator_of_notMem hr, sub_self]

/-- Actual adaptation of the difference columns is derived from the two
original adapted coefficient families. -/
theorem curveSubtract_adapted (u v : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q)
    (hV : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((v t).ofLp i) Q)
    (t : ℝ≥0) (i : I) : AEStronglyMeasurable[D.filtration t] (((u - v) t).ofLp i) Q :=
  ((hU t i).sub (hV t i)).congr (Lp.coeFn_sub ((u t).ofLp i) ((v t).ofLp i)).symm

/-- Computed stochastic integration preserves differences for merely time-L²
adapted coefficient curves. Integrability and adaptation of u-v are derived. -/
theorem predictableCurveIntegral_sub (T : ℝ≥0)
    (u v : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hv : MemLp v 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q)
    (hV : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((v t).ofLp i) Q)
    (t : ℝ≥0) :
    predictableCurveIntegral Q D T (u - v) (hu.sub hv) (curveSubtract_adapted Q D u v hU hV) t =
      predictableCurveIntegral Q D T u hu hU t - predictableCurveIntegral Q D T v hv hV t := by
  change closedStepIntegral Q D (dyadicGrids T) _ =
    closedStepIntegral Q D (dyadicGrids T) _ - closedStepIntegral Q D (dyadicGrids T) _
  rw [← closedStepIntegral_sub]
  congr 1
  apply Subtype.ext
  change timeCut Q (timeCut Q (curveHorizon Q T (u - v) (hu.sub hv)) 0 T) 0 t =
    timeCut Q (timeCut Q (curveHorizon Q T u hu) 0 T) 0 t -
      timeCut Q (timeCut Q (curveHorizon Q T v hv) 0 T) 0 t
  rw [curveHorizon_sub, timeCut_subtract, timeCut_subtract]

end PBGSO.FilteredBrownian
