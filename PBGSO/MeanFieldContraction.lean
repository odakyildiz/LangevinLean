import PBGSO.GeneralProcess
import PBGSO.AdditiveContraction

/-! # Constructed general mean-field dynamics with exponential contraction

The hypotheses are primitive global Lipschitz bounds, joint monotonicity of
the constructed drift in a specified quadratic metric, and a common continuous
L² additive sampler input. Both solutions are constructed by Picard; no
energy derivative inequality or pre-existing solution is assumed. This is an
additive-input result, not the paper's full multiplicative-noise theorem.
-/

noncomputable section
open MeasureTheory Set
namespace PBGSO.LipschitzDynamics

variable {Ω A Z G H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D : PBGSO.LipschitzDynamics A Z G)

/-- Existence and contraction of actual general mean-field integral solutions.
The optimiser receives no additive input. `C` specifies the full twisted
metric and its lower and upper comparison constants are explicit. -/
theorem exists_contracting_pair (initial other : A × Lp Z 2 Q)
    (B : ℝ → Lp Z 2 Q) (hB : Continuous B) (hB0 : B 0 = 0)
    (C : (A × Lp Z 2 Q) →L[ℝ] H) (ρ lower upper : ℝ)
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hLower : ∀ x, lower * ‖x‖ ^ 2 ≤ ‖C x‖ ^ 2)
    (hUpper : ∀ x, ‖C x‖ ^ 2 ≤ upper * ‖x‖ ^ 2)
    (hJoint : ∀ x y,
      inner ℝ (C (x - y)) (C (D.field Q x - D.field Q y)) ≤
        -ρ * ‖C (x - y)‖ ^ 2)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y W : ℝ → A × Lp Z 2 Q,
      Continuous Y ∧ Continuous W ∧ Y 0 = initial ∧ W 0 = other ∧
      (∀ t ∈ Icc 0 T, Y t - initial =
        (∫ s in 0..t, D.field Q (Y s)) + (0, B t)) ∧
      (∀ t ∈ Icc 0 T, W t - other =
        (∫ s in 0..t, D.field Q (W s)) + (0, B t)) ∧
      (∀ t ∈ Icc 0 T, ‖Y t - W t‖ ≤
        Real.sqrt (upper / lower) * Real.exp (-ρ * t) * ‖initial - other‖) := by
  obtain ⟨Y, hY, hYi, heY⟩ := D.exists_integral Q initial B hB hB0 T hT
  obtain ⟨W, hW, hWi, heW⟩ := D.exists_integral Q other B hB hB0 T hT
  refine ⟨Y, W, hY, hW, hYi, hWi, heY, heW, ?_⟩
  intro t ht
  have hg : LipschitzWith D.fieldLip (fun s => -D.field Q s) :=
    (D.field_lipschitz Q).neg
  have hm (x y : A × Lp Z 2 Q) : ρ * ‖C (x - y)‖ ^ 2 ≤
      inner ℝ (C (x - y)) (C (-D.field Q x - -D.field Q y)) := by
    have hn : -D.field Q x - -D.field Q y = -(D.field Q x - D.field Q y) := by abel
    rw [hn, map_neg, inner_neg_right]
    linarith [hJoint x y]
  have he := PBGSO.additive_integral_contraction_with_condition_number
    (fun s => -D.field Q s) D.fieldLip hg C ρ lower upper hlower hupper
    hLower hUpper hm Y W (fun s => (0, B s)) hY hW T
    (fun s hs => by simpa [hYi] using heY s hs)
    (fun s hs => by simpa [hWi] using heW s hs) t ht
  simpa only [hYi, hWi] using he

end PBGSO.LipschitzDynamics
