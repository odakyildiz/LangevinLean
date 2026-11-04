import WassersteinMixing.ActualPoisson
import WassersteinMixing.ActualDefectMean
import WassersteinMixing.ConcreteComparison

/-! # The fully realized stationary ULA comparison

The Poisson source is identified with the genuine conditional defect mean.
The comparison is then a constructed value depending only on the potential,
with no additional realization, moment, curvature, or conditional-mean input.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory

namespace WassersteinMixing

variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

/-- The actual Poisson operator has exactly the integrated actual Langevin source. -/
theorem actualPoissonSource_eq_integral (f : Lp (E P.dimension) 2 (ULA.gibbsMeasure V)) :
    (actualPoissonProcess P V hV).poissonSource f =
      ∫ s in 0..P.step, f - CanonicalSemigroup.op (𝕜 := ℝ) P V hV s f := by
  change semigroupPoissonSource (actualObservableSemigroup P V hV) (actualRealEmbedding P V)
    P.step P.step_pos.le f = _
  rw [semigroupPoissonSource_eq_integral (actualObservableSemigroup P V hV)
    (actualRealEmbedding P V) (actualObservableSemigroup_preservesReal P V hV)
    P.step P.step_pos.le f]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [actualRealOp_eq_op]

/-- The true defect mean is the constructed Poisson source, proved outright. -/
theorem actualPoissonProcess_defect_mean (n : ℕ) :
    (condExpL2 (E P.dimension) ℝ ((actualPoissonProcess P V hV).filtration.le n)
      (actualDefect P V hV n) : Lp (E P.dimension) 2 (actualProbability P V)) =
        (actualPoissonProcess P V hV).eval n
          ((actualPoissonProcess P V hV).poissonSource (actualObservableScore P V hV)) := by
  rw [actualPoissonSource_eq_integral]
  exact actualDefect_conditionalMean P V hV n

/-- Every field of the complete actual-law comparison is now a theorem from
the original potential contract; none is an additional assumption. -/
def actualULAComparison :
    ULAPoissonComparison (actualPoissonProcess P V hV) (actualObservableScore P V hV) V :=
  comparisonFromActualProcess P V hV (actualPoissonProcess P V hV) rfl (fun _ ↦ rfl)
    (actualPoissonProcess_defect_mean P V hV)

end WassersteinMixing
