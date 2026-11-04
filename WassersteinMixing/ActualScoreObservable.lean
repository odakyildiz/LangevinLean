import WassersteinMixing.ActualLocalError
import WassersteinMixing.SemigroupGlobal

/-! # The actual Gibbs score as an observable

The score is the genuine gradient in the target's square-integrable space.
Evaluation at the actual stationary diffusion recovers its previously proved
score process exactly, including its moment estimate.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped NNReal ENNReal

namespace WassersteinMixing
variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
include hV

theorem actual_gradient_memLp : MemLp (gradient V) 2 (ULA.gibbsMeasure V) :=
  ULA.memLp_gradient_gibbsMeasure V ⟨P.beta, P.beta_pos.le⟩
    (hV.regularity.differentiable (by norm_num)) hV.gradientLipschitz
    (ULA.gibbsPartition_ne_top V P.alpha P.alpha_pos
      (hV.regularity.differentiable (by norm_num)) hV.strongConvexity)

/-- The actual score observable in the Gibbs Hilbert space. -/
def actualObservableScore : Lp (E P.dimension) 2 (ULA.gibbsMeasure V) :=
  (actual_gradient_memLp P V hV).toLp (gradient V)

theorem actualObservableScore_coe :
    actualObservableScore P V hV =ᵐ[ULA.gibbsMeasure V] gradient V :=
  (actual_gradient_memLp P V hV).coeFn_toLp

/-- Actual evaluation at a stationary diffusion grid state. -/
def actualGridEvaluation (n : ℕ) :
    Lp (E P.dimension) 2 (ULA.gibbsMeasure V) →ₗᵢ[ℝ]
      Lp (E P.dimension) 2 (actualProbability P V) :=
  StationaryObservables.evaluation (ULA.gibbsMeasure V) (actualProbability P V)
    (actualReference P V hV n) (actualReference_stationary P V hV n)

theorem actualGridEvaluation_eq_global (n : ℕ) :
    actualGridEvaluation P V hV n =
      CanonicalSemigroup.evaluation (𝕜 := ℝ) (F := E P.dimension) P V hV (n * P.step) := by
  unfold actualGridEvaluation CanonicalSemigroup.evaluation
  simp only [CanonicalSemigroup.state_grid]

/-- Evaluation of the actual target score is precisely the true SDE score. -/
theorem actualGridEvaluation_score (n : ℕ) :
    actualGridEvaluation P V hV n (actualObservableScore P V hV) = actualScore P V hV n := by
  let := actualProbability_isProbability P V hV
  let mp : MeasurePreserving (actualReference P V hV n) (actualProbability P V)
      (ULA.gibbsMeasure V) :=
    ⟨(Lp.stronglyMeasurable _).measurable, actualReference_stationary P V hV n⟩
  apply Lp.ext
  have he := Lp.coeFn_compMeasurePreserving (actualObservableScore P V hV) mp
  have hs := mp.quasiMeasurePreserving.ae_eq_comp (actualObservableScore_coe P V hV)
  have hd := ULA.lpDrift_coe (actualProbability P V) (gradient V) hV.gradientLipschitz
    (actualReference P V hV n)
  filter_upwards [he, hs, hd] with ω hω hscore hgrad
  exact hω.trans (hscore.trans hgrad.symm)

/-- The score observable has the source's sharp Gibbs second-moment bound. -/
theorem actualObservableScore_energy :
    ‖actualObservableScore P V hV‖ ^ 2 ≤ P.beta * P.dimension := by
  have h := actualScore_energy P V hV 0
  rw [← actualGridEvaluation_score P V hV 0,
    (actualGridEvaluation P V hV 0).norm_map] at h
  exact h

end WassersteinMixing
