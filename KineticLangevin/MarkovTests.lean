import UnadjustedLangevin.MarkovLaw
import Mathlib.MeasureTheory.Integral.Prod

/-! # Bounded tests for actual independent-noise Markov steps

The dual transition is a concrete noise integral. It preserves measurability
and the uniform norm bound. A proved one-step weak stationarity defect at a
reference probability measure therefore accumulates at most linearly in the
number of actual Markov steps.
-/
noncomputable section
open MeasureTheory Set
namespace KineticLangevin
variable {H S : Type*} [MeasurableSpace H] [MeasurableSpace S]

/-- The actual dual transition, integrating only the independent fresh noise. -/
def markovTest (step : H → S → H) (Q : Measure S) (F : H → ℂ) (x : H) : ℂ :=
  ∫ s, F (step x s) ∂Q

variable (step : H → S → H) (hstep : Measurable (Function.uncurry step))
  (Q : Measure S) [IsProbabilityMeasure Q]

include hstep

/-- A measurable test remains measurable under the actual dual transition. -/
theorem markovTest_measurable (F : H → ℂ) (hF : Measurable F) :
    Measurable (markovTest step Q F) :=
  ((hF.comp hstep).stronglyMeasurable.integral_prod_right').measurable

omit hstep in
/-- The independent noise integral preserves a uniform test bound. -/
theorem markovTest_norm_le (F : H → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖F x‖ ≤ C) (x : H) : ‖markovTest step Q F x‖ ≤ C := by
  simpa only [markovTest,probReal_univ,one_mul,mul_one] using
    (norm_integral_le_of_norm_le_const (μ := Q) (ae_of_all Q fun s ↦ hbound (step x s)))

/-- The law transition and the dual test transition have exactly equal
integrals; this is a proved pushforward/Fubini identity. -/
theorem markovStep_integral_test (μ : Measure H) [IsProbabilityMeasure μ]
    (F : H → ℂ) (hF : Measurable F) (C : ℝ) (hbound : ∀ x, ‖F x‖ ≤ C) :
    (∫ x, F x ∂ULA.markovStep step Q μ) = ∫ x, markovTest step Q F x ∂μ := by
  have hfun : Measurable (fun p : H×S ↦ F (step p.1 p.2)) := hF.comp hstep
  have hi : Integrable (fun p : H×S ↦ F (step p.1 p.2)) (μ.prod Q) :=
    Integrable.of_bound hfun.aestronglyMeasurable C (ae_of_all _ fun p ↦ hbound _)
  unfold ULA.markovStep
  rw [integral_map hstep.aemeasurable hF.aestronglyMeasurable]
  change (∫ p : H × S, F (step p.1 p.2) ∂μ.prod Q) = _
  rw [integral_prod _ hi]
  rfl

/-- Every iterated dual transition remains measurable and bounded by the
same constant, with no growth in the iteration index. -/
theorem markovTest_iterate_properties (F : H → ℂ) (hF : Measurable F)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖F x‖ ≤ C) (n : ℕ) :
    Measurable ((markovTest step Q)^[n] F) ∧ ∀ x, ‖((markovTest step Q)^[n] F) x‖ ≤ C := by
  induction n with
  | zero => exact ⟨hF,hbound⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨markovTest_measurable step hstep Q _ ih.1,
      markovTest_norm_le step Q _ C hC ih.2⟩

/-- The actual iterated probability law is dual to the concrete iterated
noise integral. Both sides are derived from the implemented Markov recursion. -/
theorem markovLaws_integral_test (μ : Measure H) [IsProbabilityMeasure μ]
    (F : H → ℂ) (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, ‖F x‖ ≤ C) (n : ℕ) :
    (∫ x, F x ∂ULA.markovLaws step Q μ n) = ∫ x, ((markovTest step Q)^[n] F) x ∂μ := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    haveI := ULA.markovLaws_isProbability step hstep μ Q n
    rw [ULA.markovLaws,markovStep_integral_test step hstep Q _ F hF C hbound]
    rw [ih (markovTest step Q F) (markovTest_measurable step hstep Q F hF)
      (markovTest_norm_le step Q F C hC hbound)]
    rw [Function.iterate_succ_apply]

/-- A uniform one-step weak defect at the reference measure accumulates
as at most `n*delta`; no invariance or small-rejection-jump premise is used. -/
theorem markovLaws_weak_error (π : Measure H) [IsProbabilityMeasure π]
    (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hdefect : ∀ F : H → ℂ, Measurable F → (∀ x, ‖F x‖ ≤ C) →
      ‖(∫ x, F x ∂ULA.markovStep step Q π)-(∫ x, F x ∂π)‖ ≤ δ)
    (F : H → ℂ) (hF : Measurable F) (hbound : ∀ x, ‖F x‖ ≤ C) (n : ℕ) :
    ‖(∫ x, F x ∂ULA.markovLaws step Q π n)-(∫ x, F x ∂π)‖ ≤ (n : ℝ)*δ := by
  rw [markovLaws_integral_test step hstep Q π F hF C hC hbound n]
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := markovTest_iterate_properties step hstep Q F hF C hC hbound n
    have hd := hdefect ((markovTest step Q)^[n] F) hp.1 hp.2
    rw [markovStep_integral_test step hstep Q π _ hp.1 C hp.2] at hd
    have ht := norm_add_le
      ((∫ x, markovTest step Q ((markovTest step Q)^[n] F) x ∂π)-
        (∫ x, ((markovTest step Q)^[n] F) x ∂π))
      ((∫ x, ((markovTest step Q)^[n] F) x ∂π)-(∫ x, F x ∂π))
    rw [sub_add_sub_cancel] at ht
    rw [Function.iterate_succ_apply']
    push_cast
    nlinarith only [ht,hd,ih]

end KineticLangevin
