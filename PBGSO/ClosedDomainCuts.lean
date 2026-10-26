import PBGSO.PredictableStepDensity

/-! # Interval stability of the literal closed predictable-step domain -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Literal finite predictable time steps are measurable with respect to every
later past. This is proved from the actual coefficient representatives. -/
theorem coefficientStep_pastAdapted (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    PastAdaptedColumns Q D (coefficientStep Q D τ A n) := by
  apply pastAdaptedColumns_congr Q D
    (TimeGridContinuity.rawGrid τ (fun k => (A k).toLp) n)
    (coefficientStep Q D τ A n) (TimeGridContinuity.grid_coe τ _ n).symm
  intro i t
  apply Eventually.of_forall
  intro r hrt
  change AEStronglyMeasurable[D.filtration t]
    ((TimeGridContinuity.rawGrid τ (fun k => (A k).toLp) n r).ofLp i) Q
  by_cases hr : r ∈ Ioc (τ 0 : ℝ) (τ n)
  · obtain ⟨k, hk⟩ := TimeGridContinuity.exists_interval τ hτ n r hr
    rw [TimeGridContinuity.rawGrid_eq τ hτ _ n k r hk]
    have hkt : τ k ≤ t := by exact_mod_cast hk.1.le.trans hrt
    have hm := ((A k).adapted i).mono (D.filtration.mono hkt)
    exact hm.aestronglyMeasurable.congr ((A k).square i).coeFn_toLp.symm
  · rw [TimeGridContinuity.rawGrid_zero_outside τ hτ _ n r hr]
    exact aestronglyMeasurable_zero.congr (Lp.coeFn_zero Z 2 Q).symm

/-- Literal interval masks preserve past adaptedness without pointwise time
regularity or a boundedness assumption. -/
theorem timeCut_pastAdapted
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) (s t : ℝ) :
    PastAdaptedColumns Q D (timeCut Q U s t) := by
  intro i r
  filter_upwards [hU i r, timeCut_coe Q U s t] with a ha hcut har
  rw [hcut]
  by_cases ham : a ∈ Ioc s t
  · rw [Set.indicator_of_mem ham]
    exact ha har
  · rw [Set.indicator_of_notMem ham]
    exact aestronglyMeasurable_zero.congr (Lp.coeFn_zero Z 2 Q).symm

/-- Nested masks intersect their deterministic intervals. -/
theorem timeCut_commute
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (a b s t : ℝ) :
    timeCut Q (timeCut Q U a b) s t = timeCut Q (timeCut Q U s t) a b := by
  apply Lp.ext
  filter_upwards [timeCut_coe Q (timeCut Q U a b) s t,
    timeCut_coe Q (timeCut Q U s t) a b, timeCut_coe Q U a b,
    timeCut_coe Q U s t] with r h1 h2 h3 h4
  rw [h1, h2]
  by_cases hr : r ∈ Ioc a b <;> by_cases hs : r ∈ Ioc s t
  all_goals simp only [Set.indicator, hr, hs, ite_true, ite_false] at h3 h4 ⊢
  all_goals simp_all only []

/-- An actual finite step supported in the fixed horizon is unchanged by
horizon restriction. Endpoint values are harmless time-null choices. -/
theorem coefficientStep_horizon (T : ℝ≥0) (n : ℕ)
    (A : Coefficients (Z := Z) Q D ((dyadicGrids T).time n)) :
    timeCut Q (coefficientStep Q D ((dyadicGrids T).time n) A ((dyadicGrids T).count n))
      0 T = coefficientStep Q D ((dyadicGrids T).time n) A ((dyadicGrids T).count n) := by
  let G := dyadicGrids T
  have hz : G.time n 0 = 0 := by simp [G, GridIntegralCompletion.dyadicGrids]
  have he : G.time n (G.count n) = T := by
    simp only [G, GridIntegralCompletion.dyadicGrids, Nat.cast_pow, Nat.cast_ofNat]
    have hp : (2 : ℝ≥0) ^ n ≠ 0 := by positivity
    field_simp
  apply Lp.ext
  filter_upwards [timeCut_coe Q (coefficientStep Q D (G.time n) A (G.count n)) 0 T,
    TimeGridContinuity.grid_coe (G.time n) (fun k => (A k).toLp) (G.count n)]
    with r hc hg
  change (coefficientStep Q D (G.time n) A (G.count n)) r = _ at hg
  change (timeCut Q (coefficientStep Q D (G.time n) A (G.count n)) 0 T) r =
    (coefficientStep Q D (G.time n) A (G.count n)) r
  rw [hc]
  by_cases hr : r ∈ Ioc 0 (T : ℝ)
  · exact Set.indicator_of_mem hr _
  · rw [Set.indicator_of_notMem hr, hg]
    exact (TimeGridContinuity.rawGrid_zero_outside (G.time n) (G.monotone n) _
      (G.count n) r (by simpa only [hz, he, NNReal.coe_zero] using hr)).symm

/-- Cutting an actual finite predictable step stays in the completed domain;
the new observation endpoints need not be dyadic grid points. -/
theorem finiteStep_timeCut_mem (T : ℝ≥0)
    (A : FiniteStepData (Z := Z) Q D (dyadicGrids T)) (s t : ℝ) :
    timeCut Q (finiteStepInput Q D (dyadicGrids T) A) s t ∈
      closure (Set.range (finiteStepInput (Z := Z) Q D (dyadicGrids T))) := by
  have ha := coefficientStep_pastAdapted Q D ((dyadicGrids T).time A.1)
    ((dyadicGrids T).monotone A.1) A.2 ((dyadicGrids T).count A.1)
  have hc := timeCut_mem_closedStep Q D T
    (timeCut Q (finiteStepInput Q D (dyadicGrids T) A) s t)
    (timeCut_pastAdapted Q D _ ha s t)
  rw [timeCut_commute Q _ s t 0 T] at hc
  change timeCut Q (timeCut Q (coefficientStep Q D ((dyadicGrids T).time A.1) A.2
    ((dyadicGrids T).count A.1)) 0 T) s t ∈ _ at hc
  rw [coefficientStep_horizon Q D T A.1 A.2] at hc
  exact hc

/-- Every interval cut preserves the literal closed predictable-step domain.
This follows from actual finite-step density and the norm-one indicator map. -/
theorem closedStep_timeCut_mem (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (s t : ℝ) :
    timeCut Q U.val s t ∈ closure (Set.range (finiteStepInput (Z := Z) Q D (dyadicGrids T))) := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D (dyadicGrids T) U
  have hl := ((timeCut_lipschitz (I := I) (Z := Z) Q s t).continuous.tendsto U.val).comp hA
  apply isClosed_closure.mem_of_tendsto hl
  exact Eventually.of_forall (fun n => finiteStep_timeCut_mem Q D T (A n) s t)

/-- The actual completed-domain entry for an arbitrary deterministic interval. -/
def closedCutDomain (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (s t : ℝ) :
    ClosedStepDomain (Z := Z) Q D (dyadicGrids T) :=
  ⟨timeCut Q U.val s t, closedStep_timeCut_mem Q D T U s t⟩

end PBGSO.FilteredBrownian
