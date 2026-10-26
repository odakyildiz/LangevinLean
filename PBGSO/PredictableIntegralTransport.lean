import PBGSO.PredictableCurveIntegral
import PBGSO.ClosedIntegralTransport

/-! # Actual time-L² diffusion integrals on coupled probability spaces -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω Ω' I Z : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

section Pullback
variable {Q : Measure Ω} [IsProbabilityMeasure Q] {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R) (D : Driver (I := I) R)

/-- Every actual adapted L² column pulls to the actual pulled past. -/
theorem columnPullback_adapted (t : ℝ≥0) (U : Lp Z 2 R)
    (hU : AEStronglyMeasurable[D.filtration t] U R) :
    AEStronglyMeasurable[(pullbackDriver hf D).filtration t] (lpPullbackCLM (E := Z) hf U) Q := by
  refine ⟨hU.mk U ∘ f, ?_, ?_⟩
  · exact hU.stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  · exact (lpPullback_coe hf U).trans (hf.quasiMeasurePreserving.ae_eq_comp hU.ae_eq_mk)

/-- Horizon time-L² classes of the literal pulled coefficient curve are the
actual bounded-linear pullback of the original class. -/
theorem curveHorizon_pullback (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) R)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ)))) :
    curveHorizon Q T (fun r => columnPullbackCLM (I := I) (Z := Z) hf (u r))
      ((columnPullbackCLM (I := I) (Z := Z) hf).comp_memLp' hu) =
      timePullbackCLM (I := I) (Z := Z) hf (curveHorizon R T u hu) := by
  apply Lp.ext
  filter_upwards [curveHorizon_coe Q T (fun r => columnPullbackCLM (I := I) (Z := Z) hf (u r))
      ((columnPullbackCLM (I := I) (Z := Z) hf).comp_memLp' hu),
    curveHorizon_coe R T u hu,
    (columnPullbackCLM (I := I) (Z := Z) hf).coeFn_compLpL (curveHorizon R T u hu)] with r hQ hR hp
  change (timePullbackCLM (I := I) (Z := Z) hf (curveHorizon R T u hu)) r = _ at hp
  rw [hQ, hp, hR]
  by_cases hr : r ∈ Ioc 0 (T : ℝ)
  · simp only [Set.indicator_of_mem hr]
  · simp only [Set.indicator_of_notMem hr, map_zero]

/-- Actual Brownian integration of merely time-L² adapted curves commutes
with measure-preserving pullback at every observation time. -/
theorem predictableCurveIntegral_pullback (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) R)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) R)
    (t : ℝ≥0) :
    predictableCurveIntegral Q (pullbackDriver hf D) T
      (fun r => columnPullbackCLM (I := I) (Z := Z) hf (u r))
      ((columnPullbackCLM (I := I) (Z := Z) hf).comp_memLp' hu)
      (fun r i => columnPullback_adapted hf D r ((u r).ofLp i) (hU r i)) t =
      lpPullbackCLM hf (predictableCurveIntegral R D T u hu hU t) := by
  let UR := predictableDomain R D T (curveHorizon R T u hu) (curveHorizon_pastAdapted R D T u hu hU)
  let UQ := predictableDomain Q (pullbackDriver hf D) T
    (curveHorizon Q T (fun r => columnPullbackCLM (I := I) (Z := Z) hf (u r))
      ((columnPullbackCLM (I := I) (Z := Z) hf).comp_memLp' hu))
    (curveHorizon_pastAdapted Q (pullbackDriver hf D) T _ _
      (fun r i => columnPullback_adapted hf D r ((u r).ofLp i) (hU r i)))
  have he : UQ = pullbackClosedDomain hf D (dyadicGrids T) UR := by
    apply Subtype.ext
    change timeCut Q (curveHorizon Q T _ _) 0 T =
      timePullbackCLM (I := I) (Z := Z) hf (timeCut R (curveHorizon R T u hu) 0 T)
    rw [curveHorizon_pullback, timeCut_pullback]
  change closedIntegral Q (pullbackDriver hf D) T UQ t =
    lpPullbackCLM hf (closedIntegral R D T UR t)
  rw [he, closedIntegral_pullback]
end Pullback

section Enlargement
variable (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D E : Driver (I := I) Q) (hprocess : D.process = E.process)
  (henlarge : ∀ t, D.filtration t ≤ E.filtration t)
include hprocess henlarge

/-- Merely time-square-integrable computed integrals are invariant under
valid filtration enlargement carrying the same actual Brownian coordinates. -/
theorem predictableCurveIntegral_enlarge (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hD : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q)
    (hE : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[E.filtration t] ((u t).ofLp i) Q)
    (t : ℝ≥0) :
    predictableCurveIntegral Q E T u hu hE t = predictableCurveIntegral Q D T u hu hD t := by
  exact closedStepIntegral_eq_of_enlargement Q D E hprocess henlarge (dyadicGrids T)
    (closedCutDomain Q D T (predictableDomain Q D T _ (curveHorizon_pastAdapted Q D T u hu hD)) 0 t)
    (closedCutDomain Q E T (predictableDomain Q E T _ (curveHorizon_pastAdapted Q E T u hu hE)) 0 t) rfl
end Enlargement

section PullbackEnlargement
variable {Q : Measure Ω} [IsProbabilityMeasure Q] {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R) (D : Driver (I := I) R)

/-- Actual pulled integrals in any valid common larger filtration preserve
the original marginal computed noise process. No output-law premise occurs. -/
theorem predictableCurveIntegral_pullback_enlarge (E : Driver (I := I) Q)
    (hp : (pullbackDriver hf D).process = E.process)
    (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
    (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) R)
    (hu : MemLp u 2 ((volume : Measure ℝ).restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) R)
    (t : ℝ≥0) :
    predictableCurveIntegral Q E T (fun r => columnPullbackCLM (I := I) (Z := Z) hf (u r))
      ((columnPullbackCLM (I := I) (Z := Z) hf).comp_memLp' hu)
      (fun r i => (columnPullback_adapted hf D r ((u r).ofLp i) (hU r i)).mono (he r)) t =
      lpPullbackCLM hf (predictableCurveIntegral R D T u hu hU t) := by
  rw [predictableCurveIntegral_enlarge Q (pullbackDriver hf D) E hp he T _ _
    (fun r i => columnPullback_adapted hf D r ((u r).ofLp i) (hU r i))]
  exact predictableCurveIntegral_pullback hf D T u hu hU t
end PullbackEnlargement
end PBGSO.FilteredBrownian
