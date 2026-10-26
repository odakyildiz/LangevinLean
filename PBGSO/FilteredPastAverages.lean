import PBGSO.AdaptedPastAverages
import PBGSO.ClosedStepIntegration
import PBGSO.FilteredIntegralContinuity

/-! # Continuous adapted approximants for general time-L² diffusion columns -/
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

def columnEval (i : I) : ColumnHilbert (I := I) (Z := Z) Q →L[ℝ] Lp Z 2 Q :=
  (ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => Lp Z 2 Q)).toContinuousLinearMap

@[simp] theorem columnEval_apply (i : I) (x : ColumnHilbert (I := I) (Z := Z) Q) :
    columnEval Q i x = x.ofLp i := rfl

/-- Past adaptedness is required only up to time-null sets. -/
def PastAdaptedColumns (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) : Prop :=
  ∀ i, AdaptedPastAverages.PastAdapted Q D.filtration (fun r => (u r).ofLp i)

theorem pastMean_column (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : LocallyIntegrable u (volume : Measure ℝ)) (ε t : ℝ) (i : I) :
    (PastAverages.pastMean u ε t).ofLp i = PastAverages.pastMean (fun r => (u r).ofLp i) ε t := by
  have hi : IntervalIntegrable u volume (t - ε) t :=
    intervalIntegrable_iff.mpr ((hu.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  change columnEval Q i (ε⁻¹ • ∫ r in t - ε..t, u r) = _
  rw [map_smul, ← (columnEval Q i).intervalIntegral_comp_comm hi]
  rfl

/-- Moving past averages of arbitrary time-L² columns are actual adapted
continuous L²-valued diffusion curves. -/
theorem pastMean_columns_adapted
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ≥0) (i : I) :
    AEStronglyMeasurable[D.filtration t] ((PastAverages.pastMean U ε t).ofLp i) Q := by
  have hloc := (Lp.memLp U).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [pastMean_column Q U hloc ε t i]
  have hv := (columnEval (Z := Z) Q i).comp_memLp U
  change MemLp (fun r => (U r).ofLp i) 2 (volume : Measure ℝ) at hv
  have hi : LocallyIntegrable (fun r => (U r).ofLp i) (volume : Measure ℝ) :=
    hv.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact AdaptedPastAverages.pastMean_adapted Q D.filtration _ hi (hU i) ε hε t

/-- A concrete old-domain entry for every actual moving past average. Its
continuity, adaptation and finite-horizon bound are all derived. -/
def averagedDomain (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) (ε : ℝ) (hε : 0 ≤ ε) :
    IntegralDomain (Z := Z) Q D (dyadicGrids T) :=
  continuousDomain Q D T (PastAverages.pastMean U ε)
    (PastAverages.pastMean_continuous U ((Lp.memLp U).locallyIntegrable (by norm_num)) ε)
    (pastMean_columns_adapted Q D U hU ε hε)

theorem averagedDomain_coe (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) (ε : ℝ) (hε : 0 ≤ ε) :
    (averagedDomain Q D T U hU ε hε).val =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (PastAverages.pastMean U ε) :=
  continuousDomain_coe Q D T _ _ _

/-- The continuous moving-average approximants are members of the literal
closed predictable-step domain. -/
def averagedClosedDomain (T : ℝ≥0)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hU : PastAdaptedColumns Q D U) (ε : ℝ) (hε : 0 ≤ ε) :
    ClosedStepDomain (Z := Z) Q D (dyadicGrids T) :=
  toClosedStepDomain Q D (dyadicGrids T) (averagedDomain Q D T U hU ε hε)



/-- Time-null-set changes do not affect the primitive past-adaptation
property of the Hilbert-valued diffusion columns. -/
theorem pastAdaptedColumns_congr (u v : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (huv : u =ᵐ[volume] v) (hu : PastAdaptedColumns Q D u) : PastAdaptedColumns Q D v := by
  intro i t
  filter_upwards [hu i t, huv] with r hr he hrt
  rw [← he]
  exact hr hrt

/-- Actual adapted columns and literal zero extension before time zero
imply past adaptedness of every actual time-L² representative. -/
theorem pastAdaptedColumns_of_adapted (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hneg : ∀ r < 0, u r = 0)
    (hu : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q) :
    PastAdaptedColumns Q D u := by
  intro i
  apply AdaptedPastAverages.pastAdapted_of_adapted Q D.filtration (fun r => (u r).ofLp i)
  · intro r hr
    rw [hneg r hr]
    rfl
  · exact fun r => hu r i

end PBGSO.FilteredBrownian
