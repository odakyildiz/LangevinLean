import WassersteinMixing.ActualAdapted
import WassersteinMixing.ActualScoreObservable
import WassersteinMixing.ComparisonTheorems

/-! # Assembling the concrete stationary comparison

Every local-error, Hessian, law, moment, and adaptedness fact comes from the
actual canonical diffusion and Gaussian ULA construction. The Poisson process
is connected through its exact evaluation and conditional-mean identities.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory

namespace WassersteinMixing

variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

/-- Combine the constructed Markov Poisson process with the already proved
actual synchronous recursion. This is used by the concrete process constructor. -/
def comparisonFromActualProcess
    (S : PoissonProcess (Lp (E P.dimension) 2 (ULA.gibbsMeasure V))
      (E P.dimension) (actualProbability P V) P.step P.step_pos)
    (hfiltration : S.filtration = actualFiltration P V hV)
    (heval : ∀ n, S.eval n = actualGridEvaluation P V hV n)
    (hmean : ∀ n,
      (condExpL2 (E P.dimension) ℝ (S.filtration.le n) (actualDefect P V hV n) :
        Lp (E P.dimension) 2 (actualProbability P V)) =
          S.eval n (S.poissonSource (actualObservableScore P V hV))) :
    ULAPoissonComparison S (actualObservableScore P V hV) V where
  reference := actualReference P V hV
  chain := actualChain P V hV
  increment := actualScoreIncrement P V hV
  curvature := actualCurvature P V hV
  score_bound := actualObservableScore_energy P V hV
  reference_stationary := fun n ↦ (actualReference_stationary P V hV n).trans
    (actualReference_stationary P V hV 0).symm
  initial_equal := actual_initial_equal P V hV
  increment_memLp := actualScoreIncrement_memLp P V hV
  increment_bound := fun n s hs ↦ actualScoreIncrement_energy P V hV n s ⟨hs.1.le, hs.2⟩
  increment_endpoint := by
    intro n
    rw [heval n, heval (n + 1), actualGridEvaluation_score, actualGridEvaluation_score]
    exact actualScoreIncrement_endpoint P V hV n
  defect_mean := hmean
  error_step := actual_curvature_error_step P V hV
  error_adapted := by
    intro n
    have hm : (S.filtration n : MeasurableSpace (ActualSpace P)) = actualPast P V hV n :=
      congrArg (fun F : Filtration ℕ
        (inferInstance : MeasurableSpace (ActualSpace P)) ↦ F n) hfiltration
    rw [hm]
    exact actualError_adapted P V hV n
  curvature_adapted := by
    intro n U hU
    have hm : (S.filtration n : MeasurableSpace (ActualSpace P)) = actualPast P V hV n :=
      congrArg (fun F : Filtration ℕ
        (inferInstance : MeasurableSpace (ActualSpace P)) ↦ F n) hfiltration
    rw [hm] at hU ⊢
    exact actualCurvature_preserves_past P V hV n U hU
  curvature_symmetric := actualCurvature_symmetric P V hV
  curvature_lower := actualCurvature_lower P V hV
  curvature_upper := actualCurvature_upper P V hV
  dimension_eq := by simp [E]
  target_law := actualReference_stationary P V hV 0
  chain_law := actualChain_law P V hV

end WassersteinMixing
