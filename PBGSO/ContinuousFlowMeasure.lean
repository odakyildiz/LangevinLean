import PBGSO.FlowSourceRegularity
import Mathlib.MeasureTheory.Function.Jacobian

/-! # Continuous-flow preservation of Lebesgue measure

The inverse of each time slice is derived from C¹ ODE uniqueness.
The determinant theorem is then promoted to actual pushforward-measure
preservation by the finite-dimensional change-of-variables theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace PBGSO.ContinuousFlowMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Autonomous composition is a consequence of the actual global ODE
and C¹ uniqueness, rather than a supplied flow-group axiom. -/
theorem flow_add (Φ : ℝ × E → E) (f : E → E) (hf : ContDiff ℝ 1 f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t s : ℝ) (x : E) :
    Φ (t + s, x) = Φ (s, Φ (t, x)) := by
  have hshift (u : ℝ) : HasDerivAt (fun r => Φ (t + r, x))
      (f (Φ (t + u, x))) u := by
    simpa only [zero_add, one_smul, Function.comp_def] using (hODE (t + u) x).scomp u
      ((hasDerivAt_const u t).add (hasDerivAt_id u))
  let a := min 0 s - 1
  let b := max 0 s + 1
  have hzero : (0 : ℝ) ∈ Ioo a b := by
    constructor <;> dsimp [a, b] <;>
      linarith [min_le_left (0 : ℝ) s, le_max_left (0 : ℝ) s]
  have hs : s ∈ Icc a b := by
    constructor <;> dsimp [a, b] <;>
      linarith [min_le_right (0 : ℝ) s, le_max_right (0 : ℝ) s]
  have heq := FlowSourceRegularity.trajectories_unique_Icc f hf a b 0 hzero
    (fun r => Φ (t + r, x)) (fun r => Φ (r, Φ (t, x)))
    (fun u _ => (hshift u).continuousAt.continuousWithinAt)
    (fun u _ => (hODE u (Φ (t, x))).continuousAt.continuousWithinAt)
    (fun u _ => hshift u) (fun u _ => hODE u (Φ (t, x)))
    (by simp only [add_zero, hinit])
  exact heq hs

/-- Every time slice is bijective; its inverse is the negative-time
slice, derived from uniqueness of the actual trajectories. -/
theorem flow_bijective (Φ : ℝ × E → E) (f : E → E) (hf : ContDiff ℝ 1 f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) :
    Function.Bijective (fun x => Φ (t, x)) := by
  have hinv (s : ℝ) (x : E) : Φ (-s, Φ (s, x)) = x := by
    rw [← flow_add Φ f hf hODE hinit, add_neg_cancel, hinit]
  constructor
  · intro x y hxy
    simpa only [hinv] using congrArg (fun z => Φ (-t, z)) hxy
  · intro x
    refine ⟨Φ (-t, x), ?_⟩
    simpa only [neg_neg] using hinv (-t) x

section Volume
variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- A globally defined divergence-free C¹ autonomous ODE preserves
Lebesgue measure at every real time. Joint C¹ regularity, bijectivity,
and determinant one are all derived from the primitive field and ODE. -/
theorem divergenceFree_flow_measurePreserving
    (f : (κ → ℝ) → (κ → ℝ)) (hf : ContDiff ℝ 1 f)
    (hdiv : ∀ x, (ContinuousVolume.derivativeMatrix (fderiv ℝ f x)).trace = 0)
    (Φ : ℝ × (κ → ℝ) → (κ → ℝ))
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) :
    MeasurePreserving (fun x => Φ (t, x)) volume volume := by
  have hΦ := FlowSourceRegularity.flow_contDiff Φ f hf hODE hinit
  have ht : Differentiable ℝ (fun x => Φ (t, x)) :=
    (hΦ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)
  have hb := flow_bijective Φ f hf hODE hinit t
  have hdet (x : κ → ℝ) : (fderiv ℝ (fun y => Φ (t, y)) x).det = 1 :=
    FlowSourceRegularity.divergenceFree_flow_fderiv_det_one f hf hdiv Φ hODE hinit t x
  refine ⟨ht.continuous.measurable, ?_⟩
  have hmap := map_withDensity_abs_det_fderiv_eq_addHaar (μ := (volume : Measure (κ → ℝ)))
    (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (ht x).hasFDerivAt.hasFDerivWithinAt) hb.1.injOn
  simpa only [hdet, abs_one, ENNReal.ofReal_one, Measure.restrict_univ,
    withDensity_const, one_smul, Set.image_univ_of_surjective hb.2] using hmap

/-- Literal continuous A/B-flow volume preservation for the paper's
arbitrary C¹ force. No inverse, injectivity, smooth-dependence, or
Jacobian-preservation assertion is assumed. -/
theorem phase_flow_measurePreserving_source
    (F : (ι → ℝ) → (ι → ℝ)) (hF : ContDiff ℝ 1 F)
    (Φ : ℝ × ContinuousVolume.Phase ι → ContinuousVolume.Phase ι)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x))
      (ContinuousVolume.phaseField F (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) :
    MeasurePreserving (fun x => Φ (t, x)) volume volume := by
  apply divergenceFree_flow_measurePreserving (ContinuousVolume.phaseField F)
    (ContinuousVolume.phaseField_contDiff F hF) _ Φ hODE hinit t
  intro x
  exact ContinuousVolume.phaseField_trace_zero F x (hF.differentiable (by norm_num) _)

end Volume
end PBGSO.ContinuousFlowMeasure
