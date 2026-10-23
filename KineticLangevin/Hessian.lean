import KineticLangevin.Contraction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Constructing the mean Hessian in the synchronous coupling

The matrix between the two positions is the actual Bochner integral of the
Hessian along the connecting segment.  Its symmetry, spectral bounds, and
gradient-difference identity are proved below.  These are mathematical
hypotheses on the derivative of the force, never a contraction assumption.
-/

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The averaged Hessian on the segment from `y` to `x`. -/
def averagedHessian (H : E → E →L[ℝ] E) (x y : E) : E →L[ℝ] E :=
  ∫ t in (0 : ℝ)..1, H (y + t • (x - y))

theorem averagedHessian_pairing (H : E → E →L[ℝ] E) (hH : Continuous H)
    (x y z w : E) :
    ⟪z, averagedHessian H x y w⟫ =
      ∫ t in (0 : ℝ)..1, ⟪z, H (y + t • (x - y)) w⟫ := by
  have hc : Continuous (fun t : ℝ ↦ H (y + t • (x - y))) := by fun_prop
  rw [averagedHessian, ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable _ _)]
  exact ((innerSL ℝ z).intervalIntegral_comp_comm
    ((hc.clm_apply continuous_const).intervalIntegrable _ _)).symm

/-- Integrating symmetric Hessians preserves symmetry. -/
theorem averagedHessian_symmetric (H : E → E →L[ℝ] E) (hH : Continuous H)
    (hSym : ∀ p z w, ⟪z, H p w⟫ = ⟪w, H p z⟫) (x y z w : E) :
    ⟪z, averagedHessian H x y w⟫ = ⟪w, averagedHessian H x y z⟫ := by
  rw [averagedHessian_pairing H hH, averagedHessian_pairing H hH]
  apply intervalIntegral.integral_congr
  intro t ht
  exact hSym _ _ _

/-- The lower Hessian bound passes to the explicitly constructed mean. -/
theorem averagedHessian_lower (H : E → E →L[ℝ] E) (hH : Continuous H)
    (m : ℝ) (hLower : ∀ p z, m * ‖z‖ ^ 2 ≤ ⟪z, H p z⟫) (x y z : E) :
    m * ‖z‖ ^ 2 ≤ ⟪z, averagedHessian H x y z⟫ := by
  rw [averagedHessian_pairing H hH]
  have hc : Continuous (fun t : ℝ ↦ ⟪z, H (y + t • (x - y)) z⟫) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const (c := m * ‖z‖ ^ 2)) (hc.intervalIntegrable 0 1)
    (fun t _ ↦ hLower (y + t • (x - y)) z)
  simpa using hi

/-- The upper Hessian bound passes to the explicitly constructed mean. -/
theorem averagedHessian_upper (H : E → E →L[ℝ] E) (hH : Continuous H)
    (M : ℝ) (hUpper : ∀ p z, ⟪z, H p z⟫ ≤ M * ‖z‖ ^ 2) (x y z : E) :
    ⟪z, averagedHessian H x y z⟫ ≤ M * ‖z‖ ^ 2 := by
  rw [averagedHessian_pairing H hH]
  have hc : Continuous (fun t : ℝ ↦ ⟪z, H (y + t • (x - y)) z⟫) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hc.intervalIntegrable 0 1) (intervalIntegrable_const (c := M * ‖z‖ ^ 2))
    (fun t _ ↦ hUpper (y + t • (x - y)) z)
  simpa using hi

/-- The mean Hessian represents the actual force difference by the
fundamental theorem of calculus along a segment. -/
theorem averagedHessian_force_difference (g : E → E) (H : E → E →L[ℝ] E)
    (hH : Continuous H) (hg : ∀ p, HasFDerivAt g (H p) p) (x y : E) :
    averagedHessian H x y (x - y) = g x - g y := by
  have hpath (t : ℝ) : HasDerivAt (fun s : ℝ ↦ y + s • (x - y)) (x - y) t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const (x - y)).const_add y
  have hc : Continuous (fun t : ℝ ↦ H (y + t • (x - y))) := by fun_prop
  rw [averagedHessian, ContinuousLinearMap.intervalIntegral_apply (hc.intervalIntegrable _ _)]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (f := fun t ↦ g (y + t • (x - y)))
    (fun t _ ↦ (hg (y + t • (x - y))).comp_hasDerivAt t (hpath t))
    ((hc.clm_apply continuous_const).intervalIntegrable _ _)
  simpa using he

end KineticLangevin
