import WassersteinMixing.SemigroupInstance
import WassersteinMixing.ComplexRealActual
import WassersteinMixing.SemigroupProcess
import WassersteinMixing.ActualScoreObservable

/-! # The actual Langevin Poisson comparison process

The reversible semigroup, real observable space, bounded Poisson corrector,
stationary evaluations, Brownian past, and conditional Markov identity are all
constructed from the original potential assumptions in this module.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped NNReal

namespace WassersteinMixing

abbrev ComplexObservableValue (P : Parameters) :=
  EuclideanSpace ℂ (Fin (Module.finrank ℝ (E P.dimension)))

def actualObservableSemigroup (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) :
    ReversibleSemigroup (Lp (ComplexObservableValue P) 2 (ULA.gibbsMeasure V)) :=
  CanonicalSemigroup.semigroup P V hV

def actualRealEmbedding (P : Parameters) (V : E P.dimension → ℝ) :
    Lp (E P.dimension) 2 (ULA.gibbsMeasure V) →ₗᵢ[ℝ]
      Lp (ComplexObservableValue P) 2 (ULA.gibbsMeasure V) :=
  RealComplexEmbedding.coordinateLp (E P.dimension) (ULA.gibbsMeasure V)

theorem actualObservableSemigroup_preservesReal (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) :
    ComplexRealCorrector.PreservesReal (actualObservableSemigroup P V hV)
      (actualRealEmbedding P V) :=
  CanonicalSemigroup.preservesReal_of_op_eq (RealComplexEmbedding.coordinate (E P.dimension))
    P V hV (actualObservableSemigroup P V hV) (fun _ _ ↦ rfl)

theorem actualRealOp_eq_op (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) :
    ComplexRealCorrector.realOp (actualObservableSemigroup P V hV) (actualRealEmbedding P V) t =
      CanonicalSemigroup.op (𝕜 := ℝ) (F := E P.dimension) P V hV t :=
  CanonicalSemigroup.realOp_eq_op (RealComplexEmbedding.coordinate (E P.dimension))
    P V hV (actualObservableSemigroup P V hV) t rfl

theorem actualGridEvaluation_adapted (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (f : Lp (E P.dimension) 2 (ULA.gibbsMeasure V)) :
    AEStronglyMeasurable[actualFiltration P V hV n]
      (actualGridEvaluation P V hV n f) (actualProbability P V) := by
  let a : ℝ≥0 := ⟨(n : ℝ) * P.step, mul_nonneg (Nat.cast_nonneg n) P.step_pos.le⟩
  have ha := actualEvaluation_adapted_pastAt P V hV a f
  change AEStronglyMeasurable[actualPast P V hV n]
    (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV (n * P.step) f) (actualProbability P V) at ha
  rw [actualGridEvaluation_eq_global]
  change AEStronglyMeasurable[actualPast P V hV n]
    (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV (n * P.step) f) (actualProbability P V)
  exact ha

theorem actualGridEvaluation_markov (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (f : Lp (E P.dimension) 2 (ULA.gibbsMeasure V)) :
    (condExpL2 (E P.dimension) ℝ ((actualFiltration P V hV).le n)
      (actualGridEvaluation P V hV (n + 1) f) : Lp (E P.dimension) 2 (actualProbability P V)) =
        actualGridEvaluation P V hV n
          (ComplexRealCorrector.realOp (actualObservableSemigroup P V hV)
            (actualRealEmbedding P V) P.step f) := by
  let a : ℝ≥0 := ⟨(n : ℝ) * P.step, mul_nonneg (Nat.cast_nonneg n) P.step_pos.le⟩
  have hm := actualEvaluation_markov_pastAt P V hV a P.step P.step_pos.le f
  have ht : (a : ℝ) + P.step = ((n + 1 : ℕ) : ℝ) * P.step := by
    change (n : ℝ) * P.step + P.step = ((n + 1 : ℕ) : ℝ) * P.step
    push_cast
    ring
  rw [ht] at hm
  rw [actualRealOp_eq_op, actualGridEvaluation_eq_global, actualGridEvaluation_eq_global]
  exact hm

/-- The actual Poisson process, with every analytic field derived from the
potential and the ordinary Brownian Langevin construction. -/
def actualPoissonProcess (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) :
    PoissonProcess (Lp (E P.dimension) 2 (ULA.gibbsMeasure V)) (E P.dimension)
      (actualProbability P V) P.step P.step_pos :=
  semigroupPoissonProcess (actualProbability P V) (actualObservableSemigroup P V hV)
    (actualRealEmbedding P V) (actualObservableSemigroup_preservesReal P V hV)
    P.step P.step_pos (actualFiltration P V hV) (actualGridEvaluation P V hV)
    (actualGridEvaluation_adapted P V hV) (actualGridEvaluation_markov P V hV)

end WassersteinMixing
