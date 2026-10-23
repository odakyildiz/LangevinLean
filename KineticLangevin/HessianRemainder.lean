import KineticLangevin.Hessian
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem averagedHessian_sub_base_bound (H : E → E →L[ℝ] E) (M2 : ℝ≥0)
    (hLip : LipschitzWith M2 H) (x y : E) :
    ‖averagedHessian H x y - H y‖ ≤ (M2 : ℝ) / 2 * ‖x-y‖ := by
  have hc : Continuous (fun t : ℝ ↦ H (y + t • (x-y))) := by have hH := hLip.continuous;fun_prop
  have hid : averagedHessian H x y - H y = ∫ t in (0 : ℝ)..1, H (y + t • (x-y)) - H y := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp [averagedHessian]
  rw [hid]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, (M2 : ℝ) * t * ‖x-y‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
      · apply Filter.Eventually.of_forall
        intro t ht
        have hs := hLip.norm_sub_le (y + t • (x-y)) y
        rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1.le] at hs
        nlinarith only [hs]
      · exact (by fun_prop : Continuous (fun t : ℝ ↦ (M2 : ℝ) * t * ‖x-y‖)).intervalIntegrable _ _
    _ = _ := by rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,integral_id];norm_num <;> ring <;> simp

theorem force_taylor_remainder_bound (g : E → E) (H : E → E →L[ℝ] E) (M2 : ℝ≥0)
    (hLip : LipschitzWith M2 H) (hg : ∀ x, HasFDerivAt g (H x) x) (x y : E) :
    ‖g x - g y - H y (x-y)‖ ≤ (M2 : ℝ) / 2 * ‖x-y‖ ^ 2 := by
  have he := averagedHessian_force_difference g H hLip.continuous hg x y
  rw [← he, ← ContinuousLinearMap.sub_apply]
  calc
    _ ≤ ‖averagedHessian H x y - H y‖ * ‖x-y‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((M2 : ℝ) / 2 * ‖x-y‖) * ‖x-y‖ :=
      mul_le_mul_of_nonneg_right (averagedHessian_sub_base_bound H M2 hLip x y) (norm_nonneg _)
    _ = _ := by ring

end KineticLangevin
