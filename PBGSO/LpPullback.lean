import PBGSO.GeneralProcess
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Change of probability space for the constructed mean-field dynamics

A measure-preserving map pulls back actual L² variables. The three primitive
maps, their Bochner expectation, and their complete mean-field vector field
commute with that pullback. Consequently a constructed integral trajectory can
be realized on an initial-coupling extension without changing either marginal
law. No equality of output laws or of mean-field forces is assumed.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace PBGSO

section Pullback
variable {Ω Ω' E K : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {Q : Measure Ω} {Q' : Measure Ω'} {f : Ω' → Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- The actual measure-preserving L² pullback as a continuous linear map. -/
def lpPullbackCLM (hf : MeasurePreserving f Q' Q) : Lp E 2 Q →L[ℝ] Lp E 2 Q' :=
  (Lp.compMeasurePreservingₗᵢ ℝ f hf).toContinuousLinearMap

theorem lpPullback_coe (hf : MeasurePreserving f Q' Q) (U : Lp E 2 Q) :
    lpPullbackCLM hf U =ᵐ[Q'] fun ω => U (f ω) :=
  Lp.coeFn_compMeasurePreserving U hf

@[simp] theorem lpPullback_norm (hf : MeasurePreserving f Q' Q) (U : Lp E 2 Q) :
    ‖lpPullbackCLM hf U‖ = ‖U‖ := Lp.norm_compMeasurePreserving U hf

/-- Pulling back twice is pullback along the composed map. -/
theorem lpPullback_comp {Ω'' : Type*} [MeasurableSpace Ω'']
    {Q'' : Measure Ω''} {g : Ω'' → Ω'}
    (hf : MeasurePreserving f Q' Q) (hg : MeasurePreserving g Q'' Q')
    (U : Lp E 2 Q) :
    lpPullbackCLM hg (lpPullbackCLM hf U) = lpPullbackCLM (hf.comp hg) U :=
  (Lp.compMeasurePreserving_comp_apply U hf hg).symm

/-- Composition of a primitive Lipschitz map commutes with pullback. -/
theorem lpPullback_liftMap [IsFiniteMeasure Q] [IsFiniteMeasure Q']
    (hf : MeasurePreserving f Q' Q) (g : E → K) {L : ℝ≥0}
    (hg : LipschitzWith L g) (U : Lp E 2 Q) :
    lpPullbackCLM hf (liftMap Q g hg U) =
      liftMap Q' g hg (lpPullbackCLM hf U) := by
  apply Lp.ext
  filter_upwards [lpPullback_coe hf (liftMap Q g hg U),
    hf.quasiMeasurePreserving.ae_eq_comp (liftMap_coe Q g hg U),
    liftMap_coe Q' g hg (lpPullbackCLM hf U), lpPullback_coe hf U]
    with ω h₁ h₂ h₃ h₄
  change (liftMap Q g hg U) (f ω) = g (U (f ω)) at h₂
  rw [h₁, h₂, h₃, h₄]

/-- Pullback preserves a Bochner expectation of an actual L² variable. -/
theorem lpPullback_integral [IsFiniteMeasure Q] [IsFiniteMeasure Q']
    (hf : MeasurePreserving f Q' Q) (U : Lp E 2 Q) :
    (∫ ω, lpPullbackCLM hf U ω ∂Q') = ∫ ω, U ω ∂Q := by
  rw [integral_congr_ae (lpPullback_coe hf U)]
  have hm : AEStronglyMeasurable (fun ω => U ω) (Q'.map f) := by
    rw [hf.map_eq]
    exact Lp.aestronglyMeasurable U
  exact (integral_map hf.measurable.aemeasurable hm).symm.trans
    (by rw [hf.map_eq])

end Pullback

section Dynamics
variable {Ω Ω' A Z G : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {Q : Measure Ω} {Q' : Measure Ω'} {f : Ω' → Ω}
  [IsProbabilityMeasure Q] [IsProbabilityMeasure Q']
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Pullback acts identically on the deterministic optimiser coordinate. -/
def jointPullbackCLM (hf : MeasurePreserving f Q' Q) :
    (A × Lp Z 2 Q) →L[ℝ] (A × Lp Z 2 Q') :=
  (ContinuousLinearMap.fst ℝ A (Lp Z 2 Q)).prod
    ((lpPullbackCLM hf).comp (ContinuousLinearMap.snd ℝ A (Lp Z 2 Q)))

@[simp] theorem jointPullback_apply (hf : MeasurePreserving f Q' Q)
    (y : A × Lp Z 2 Q) : jointPullbackCLM hf y = (y.1, lpPullbackCLM hf y.2) := rfl

/-- The observation expectation is preserved, by actual change of variables. -/
theorem expectedObservation_pullback (hf : MeasurePreserving f Q' Q)
    (L : LipschitzDynamics A Z G) (a : A) (U : Lp Z 2 Q) :
    L.expectedObservation Q' a (lpPullbackCLM hf U) =
      L.expectedObservation Q a U := by
  unfold LipschitzDynamics.expectedObservation
  rw [← lpPullback_liftMap hf]
  exact lpPullback_integral hf _

/-- The complete mean-field force commutes with a change of probability space. -/
theorem field_pullback (hf : MeasurePreserving f Q' Q)
    (L : LipschitzDynamics A Z G) (y : A × Lp Z 2 Q) :
    L.field Q' (jointPullbackCLM hf y) = jointPullbackCLM hf (L.field Q y) := by
  simp only [LipschitzDynamics.field, jointPullback_apply,
    expectedObservation_pullback hf, lpPullback_liftMap hf]

/-- Integral trajectories pull back to actual integral trajectories. The
new common input is the actual pullback of the old input. -/
theorem integral_solution_pullback (hf : MeasurePreserving f Q' Q)
    (L : LipschitzDynamics A Z G) (initial : A × Lp Z 2 Q)
    (B : ℝ → Lp Z 2 Q) (Y : ℝ → A × Lp Z 2 Q) (hY : Continuous Y)
    (T : ℝ) (heq : ∀ t ∈ Icc 0 T, Y t - initial =
      (∫ r in 0..t, L.field Q (Y r)) + (0, B t)) :
    Continuous (fun t => jointPullbackCLM hf (Y t)) ∧
      ∀ t ∈ Icc 0 T, jointPullbackCLM hf (Y t) - jointPullbackCLM hf initial =
        (∫ r in 0..t, L.field Q' (jointPullbackCLM hf (Y r))) +
          (0, lpPullbackCLM hf (B t)) := by
  refine ⟨(jointPullbackCLM hf).continuous.comp hY, ?_⟩
  intro t ht
  have hi : IntervalIntegrable (fun r => L.field Q (Y r)) volume 0 t :=
    ((L.field_lipschitz Q).continuous.comp hY).intervalIntegrable _ _
  have h := congrArg (jointPullbackCLM hf) (heq t ht)
  rw [map_sub, map_add, ← (jointPullbackCLM hf).intervalIntegral_comp_comm hi] at h
  simpa only [← field_pullback hf, jointPullback_apply] using h

end Dynamics

section Laws
variable {Ω Ω' Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {Q : Measure Ω} {Q' : Measure Ω'} {f : Ω' → Ω}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z]

/-- The actual output sampler law is unchanged by probability-space pullback. -/
theorem lpPullback_law (hf : MeasurePreserving f Q' Q) (U : Lp Z 2 Q) :
    Q'.map (lpPullbackCLM hf U) = Q.map U := by
  rw [Measure.map_congr (lpPullback_coe hf U)]
  change Q'.map ((fun ω => U ω) ∘ f) = Q.map U
  rw [← Measure.map_map (Lp.stronglyMeasurable U).measurable hf.measurable, hf.map_eq]

end Laws
end PBGSO
