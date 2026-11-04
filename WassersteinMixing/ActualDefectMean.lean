import WassersteinMixing.ActualMarkov
import WassersteinMixing.ActualScoreObservable
import WassersteinMixing.ConditionalDefect

/-! # The conditional mean of the genuine local defect

The actual score increment is an evaluated target observable difference.
The actual conditional Markov identity identifies its conditional mean, and
Bochner integral commutation identifies the conditional mean of the true
integrated Euler defect.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace WassersteinMixing

variable (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)

/-- Evaluating the actual target score recovers the true gradient of the
actual diffusion at every real time. -/
theorem actualEvaluation_score (t : ℝ) :
    letI := actualProbability_isProbability P V hV
    CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV t (actualObservableScore P V hV) =
      ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz
        (CanonicalSemigroup.state P V hV t) := by
  let := actualProbability_isProbability P V hV
  have mp : MeasurePreserving (CanonicalSemigroup.state P V hV t)
      (actualProbability P V) (ULA.gibbsMeasure V) :=
    ⟨(Lp.stronglyMeasurable _).measurable, CanonicalSemigroup.state_law P V hV t⟩
  apply Lp.ext
  have he := Lp.coeFn_compMeasurePreserving (actualObservableScore P V hV) mp
  have hs := mp.quasiMeasurePreserving.ae_eq_comp (actualObservableScore_coe P V hV)
  have hd := ULA.lpDrift_coe (actualProbability P V) (gradient V) hV.gradientLipschitz
    (CanonicalSemigroup.state P V hV t)
  filter_upwards [he, hs, hd] with ω hω hscore hgrad
  exact hω.trans (hscore.trans hgrad.symm)

/-- The true score increment equals the two actual score evaluations. -/
theorem actualScoreIncrement_eq_evaluation (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 P.step) :
    actualScoreIncrement P V hV n s =
      actualGridEvaluation P V hV n (actualObservableScore P V hV) -
        CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV ((n : ℝ) * P.step + s)
          (actualObservableScore P V hV) := by
  let := actualProbability_isProbability P V hV
  rw [actualGridEvaluation_score, actualEvaluation_score,
    CanonicalSemigroup.state_eq_actualSegment P V hV n s hs]
  rfl

/-- Exact conditional mean of each genuine score increment, from the actual
Brownian-past Markov theorem. -/
theorem actualScoreIncrement_conditionalMean (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 P.step) :
    (condExpL2 (E P.dimension) ℝ (actualPast_le P V hV n)
      (actualScoreIncrement P V hV n s) : Lp (E P.dimension) 2 (actualProbability P V)) =
      actualGridEvaluation P V hV n
        (actualObservableScore P V hV -
          CanonicalSemigroup.op (𝕜 := ℝ) P V hV s (actualObservableScore P V hV)) := by
  let a : ℝ≥0 := ⟨(n : ℝ) * P.step, mul_nonneg (Nat.cast_nonneg _) P.step_pos.le⟩
  have hfirst := actualEvaluation_markov_pastAt P V hV a 0 (by norm_num)
    (actualObservableScore P V hV)
  simp only [add_zero, CanonicalSemigroup.op_zero, one_apply_eq_self] at hfirst
  have hsecond := actualEvaluation_markov_pastAt P V hV a s hs.1 (actualObservableScore P V hV)
  change (condExpL2 (E P.dimension) ℝ (actualPast_le P V hV n)
    (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV ((n : ℝ) * P.step)
      (actualObservableScore P V hV)) : Lp (E P.dimension) 2 (actualProbability P V)) =
      CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV ((n : ℝ) * P.step)
        (actualObservableScore P V hV) at hfirst
  change (condExpL2 (E P.dimension) ℝ (actualPast_le P V hV n)
    (CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV ((n : ℝ) * P.step + s)
      (actualObservableScore P V hV)) : Lp (E P.dimension) 2 (actualProbability P V)) =
      CanonicalSemigroup.evaluation (𝕜 := ℝ) P V hV ((n : ℝ) * P.step)
        (CanonicalSemigroup.op (𝕜 := ℝ) P V hV s (actualObservableScore P V hV)) at hsecond
  rw [actualScoreIncrement_eq_evaluation P V hV n s hs, actualGridEvaluation_eq_global]
  simp only [map_sub, Submodule.coe_sub]
  rw [hfirst, hsecond]

/-- Conditional mean of the actual integrated Euler defect, with its exact
operator-valued time-integrated source. This is the source later identified
with the constructed Poisson corrector. -/
theorem actualDefect_conditionalMean (n : ℕ) :
    (condExpL2 (E P.dimension) ℝ (actualPast_le P V hV n)
      (actualDefect P V hV n) : Lp (E P.dimension) 2 (actualProbability P V)) =
      actualGridEvaluation P V hV n
        (∫ s in 0..P.step, actualObservableScore P V hV -
          CanonicalSemigroup.op (𝕜 := ℝ) P V hV s (actualObservableScore P V hV)) := by
  exact conditionalDefect_eq_evaluation_integral (actualProbability P V) (actualPast_le P V hV n)
    (actualGridEvaluation P V hV n) (actualScoreIncrement P V hV n)
    (fun s ↦ actualObservableScore P V hV -
      CanonicalSemigroup.op (𝕜 := ℝ) P V hV s (actualObservableScore P V hV))
    P.step P.step_pos.le ((actualScoreIncrement_continuous P V hV n).intervalIntegrable 0 P.step)
    (actualScoreIncrement_conditionalMean P V hV n)

end WassersteinMixing
