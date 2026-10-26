import PBGSO.FilteredPastAverages
import PBGSO.LpIntegralSections

/-! # Past-average density in the literal closed predictable-step domain -/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

theorem averagedDomain_eq_timeCut (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) (ε : ℝ) (hε : 0 < ε) :
    (averagedDomain Q D T U hU ε hε.le).val = timeCut Q (PastAverages.average U ε) 0 T := by
  apply Lp.ext
  filter_upwards [averagedDomain_coe Q D T U hU ε hε.le,
    timeCut_coe Q (PastAverages.average U ε) 0 T,
    LpIntegralSections.average_coe_ae U ε hε] with r hmean hcut hr
  rw [hmean, hcut]
  by_cases hR : r ∈ Ioc 0 (T : ℝ)
  · simp only [Set.indicator_of_mem hR, hr]
  · simp only [Set.indicator_of_notMem hR]

/-- Every time-L² column family adapted to the actual past belongs, after horizon
restriction, to the literal closure of finite predictable Brownian steps.
Past averaging, continuous adapted approximation and Fubini prove membership. -/
theorem timeCut_mem_closedStep (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) :
    timeCut Q U 0 T ∈ closure (Set.range (finiteStepInput (Z := Z) Q D (dyadicGrids T))) := by
  have hlim := ((timeCut_lipschitz (I := I) (Z := Z) Q 0 T).continuous.tendsto U).comp
    (PastAverages.average_tendsto U)
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  have hc := (averagedClosedDomain Q D T U hU ε hε'.le).property
  have he := averagedDomain_eq_timeCut Q D T U hU ε hε'
  change (averagedDomain Q D T U hU ε hε'.le).val ∈ _ at hc
  rw [he] at hc
  exact hc

/-- Actual completed stochastic-integral domain for a time-L² adapted family.
Its membership proof is derived and does not ask for step approximants. -/
def predictableDomain (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) :
    ClosedStepDomain (Z := Z) Q D (dyadicGrids T) :=
  ⟨timeCut Q U 0 T, timeCut_mem_closedStep Q D T U hU⟩

@[simp] theorem predictableDomain_val (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) :
    (predictableDomain Q D T U hU).val = timeCut Q U 0 T := rfl

end PBGSO.FilteredBrownian
