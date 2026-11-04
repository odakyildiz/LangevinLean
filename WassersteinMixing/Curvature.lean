import WassersteinMixing.Parameters
import WassersteinMixing.ShiftedEnergy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The actual averaged Hessian of the potential

The gradient is continuously differentiable under the paper's `C²` hypothesis.
Its derivative is symmetric, and its average along a segment is the exact
gradient secant operator used by the synchronous coupling.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

namespace WassersteinMixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A `C²` real potential has a `C¹` gradient. -/
theorem contDiff_gradient_of_two (V : H → ℝ) (hV : ContDiff ℝ 2 V) :
    ContDiff ℝ 1 (gradient V) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  exact (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp hd

/-- The actual Hessian operator, expressed as the derivative of the gradient. -/
def hessianOperator (V : H → ℝ) (x : H) : H →L[ℝ] H := fderiv ℝ (gradient V) x

/-- The Hessian bilinear form is the genuine second derivative of `V`. -/
theorem inner_hessianOperator (V : H → ℝ) (hV : ContDiff ℝ 2 V) (x u v : H) :
    inner ℝ (hessianOperator V x u) v = fderiv ℝ (fderiv ℝ V) x u v := by
  have hd : Differentiable ℝ (fderiv ℝ V) :=
    (hV.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hc := (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.hasFDerivAt.comp x
    (hd x).hasFDerivAt
  change HasFDerivAt (gradient V)
    ((InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fderiv ℝ (fderiv ℝ V) x)) x at hc
  rw [hessianOperator, hc.fderiv]
  exact InnerProductSpace.toDual_symm_apply

/-- Symmetry of the actual Hessian follows from equality of mixed derivatives. -/
theorem hessianOperator_symmetric (V : H → ℝ) (hV : ContDiff ℝ 2 V) (x u v : H) :
    inner ℝ (hessianOperator V x u) v = inner ℝ u (hessianOperator V x v) := by
  rw [inner_hessianOperator V hV, real_inner_comm (hessianOperator V x v) u, inner_hessianOperator V hV]
  exact hV.contDiffAt.isSymmSndFDerivAt (by norm_num) u v

/-- The Hessian operator depends continuously on the state. -/
theorem hessianOperator_continuous (V : H → ℝ) (hV : ContDiff ℝ 2 V) :
    Continuous (hessianOperator V) :=
  (contDiff_gradient_of_two V hV).continuous_fderiv (by norm_num)

/-- Global gradient Lipschitzness bounds the actual Hessian operator norm. -/
theorem hessianOperator_norm_le (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (x : H) : ‖hessianOperator V x‖ ≤ P.beta := by
  exact norm_fderiv_le_of_lipschitz ℝ hV.gradientLipschitz

/-- The lower Hessian form bound is derived from strong gradient monotonicity. -/
theorem hessianOperator_lower (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (x v : H) :
    P.alpha * ‖v‖ ^ 2 ≤ inner ℝ v (hessianOperator V x v) := by
  let f : ℝ → H := fun t ↦ gradient V (x + t • v)
  have hd : HasDerivAt f (hessianOperator V x v) 0 := by
    have hl : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
    simpa only [f, Function.comp_def, hessianOperator, zero_smul, add_zero] using
      ((contDiff_gradient_of_two V hV.regularity).differentiable (by norm_num) x).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have hscalar := (hasDerivAt_const (0 : ℝ) v).inner ℝ (hd.sub_const (gradient V x))
  have hlim := hscalar.tendsto_slope_zero_right
  simp only [f, zero_smul, add_zero, sub_self, inner_zero_right, sub_zero,
    zero_add] at hlim
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  have hm := ULA.strong_gradient_monotone
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity (x + t • v) x
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_right] at hm
  rw [real_inner_comm v (gradient V (x + t • v) - gradient V x)] at hm
  simp only [smul_eq_mul, ← div_eq_inv_mul]
  apply (le_div_iff₀ ht0).mpr
  nlinarith

/-- The upper Hessian form bound follows from its actual operator norm. -/
theorem hessianOperator_upper (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (x v : H) :
    inner ℝ v (hessianOperator V x v) ≤ P.beta * ‖v‖ ^ 2 := by
  have hn := (hessianOperator V x).le_opNorm v
  have hb := hessianOperator_norm_le P V hV x
  have hi := real_inner_le_norm v (hessianOperator V x v)
  nlinarith [norm_nonneg v, norm_nonneg (hessianOperator V x v)]

/-- The literal averaged Hessian along the segment from `y` to `x`. -/
def averagedHessian (V : H → ℝ) (x y : H) : H →L[ℝ] H :=
  ∫ t in (0 : ℝ)..1, hessianOperator V (y + t • (x - y))

theorem averagedHessian_curve_continuous (V : H → ℝ) (hV : ContDiff ℝ 2 V) (x y : H) :
    Continuous (fun t : ℝ ↦ hessianOperator V (y + t • (x - y))) :=
  (hessianOperator_continuous V hV).comp (by fun_prop)

/-- Evaluation commutes with the actual averaged-operator integral. -/
theorem averagedHessian_apply (V : H → ℝ) (hV : ContDiff ℝ 2 V) (x y v : H) :
    averagedHessian V x y v = ∫ t in (0 : ℝ)..1, hessianOperator V (y + t • (x - y)) v := by
  exact ContinuousLinearMap.intervalIntegral_apply
    ((averagedHessian_curve_continuous V hV x y).intervalIntegrable _ _) v

/-- Pairing commutes with the actual averaged-operator integral. -/
theorem averagedHessian_inner (V : H → ℝ) (hV : ContDiff ℝ 2 V) (x y u v : H) :
    inner ℝ u (averagedHessian V x y v) =
      ∫ t in (0 : ℝ)..1, inner ℝ u (hessianOperator V (y + t • (x - y)) v) := by
  rw [averagedHessian_apply V hV]
  exact ((innerSL ℝ u).intervalIntegral_comp_comm
    (((averagedHessian_curve_continuous V hV x y).clm_apply continuous_const).intervalIntegrable _ _)).symm

/-- The averaged Hessian is genuinely symmetric. -/
theorem averagedHessian_symmetric (V : H → ℝ) (hV : ContDiff ℝ 2 V) (x y u v : H) :
    inner ℝ (averagedHessian V x y u) v = inner ℝ u (averagedHessian V x y v) := by
  rw [real_inner_comm v, averagedHessian_inner V hV, averagedHessian_inner V hV]
  apply intervalIntegral.integral_congr
  intro t _
  exact (real_inner_comm (hessianOperator V (y + t • (x - y)) u) v).trans
    (hessianOperator_symmetric V hV _ u v)

/-- The actual averaged Hessian retains the sharp global norm bound. -/
theorem averagedHessian_norm_le (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (x y : H) : ‖averagedHessian V x y‖ ≤ P.beta := by
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := P.beta) (f := fun t ↦ hessianOperator V (y + t • (x - y)))
    (fun t _ ↦ hessianOperator_norm_le P V hV _)
  simpa only [averagedHessian, sub_zero, abs_one, mul_one] using hn

/-- The actual averaged Hessian retains the strong-convexity lower form bound. -/
theorem averagedHessian_lower (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (x y v : H) :
    P.alpha * ‖v‖ ^ 2 ≤ inner ℝ v (averagedHessian V x y v) := by
  rw [averagedHessian_inner V hV.regularity]
  have hi : IntervalIntegrable (fun t : ℝ ↦
      inner ℝ v (hessianOperator V (y + t • (x - y)) v)) volume 0 1 :=
    (continuous_const.inner ((averagedHessian_curve_continuous V hV.regularity x y).clm_apply
      continuous_const)).intervalIntegrable _ _
  have hb := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const (b := (1 : ℝ)) (a := (0 : ℝ))) hi
    (fun t _ ↦ hessianOperator_lower P V hV _ v)
  simpa using hb

/-- The actual averaged Hessian retains the smoothness upper form bound. -/
theorem averagedHessian_upper (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) (x y v : H) :
    inner ℝ v (averagedHessian V x y v) ≤ P.beta * ‖v‖ ^ 2 := by
  have hn := (averagedHessian V x y).le_opNorm v
  have hb := averagedHessian_norm_le P V hV x y
  have hi := real_inner_le_norm v (averagedHessian V x y v)
  nlinarith [norm_nonneg v, norm_nonneg (averagedHessian V x y v)]

/-- The averaged Hessian is the exact gradient secant operator, by the
fundamental theorem of calculus along the actual line segment. -/
theorem averagedHessian_secant (V : H → ℝ) (hV : ContDiff ℝ 2 V) (x y : H) :
    averagedHessian V x y (x - y) = gradient V x - gradient V y := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ ↦ gradient V (y + s • (x - y)))
      (hessianOperator V (y + t • (x - y)) (x - y)) t := by
    have hl : HasDerivAt (fun s : ℝ ↦ y + s • (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
    exact ((contDiff_gradient_of_two V hV).differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t hl
  rw [averagedHessian_apply V hV]
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (((averagedHessian_curve_continuous V hV x y).clm_apply continuous_const).intervalIntegrable 0 1)
  simpa only [zero_smul, one_smul, add_zero, add_sub_cancel] using hi

/-- The actual secant operator is continuous jointly in both endpoints.
The fixed compact time integral uses the proved uniform Hessian norm bound. -/
theorem averagedHessian_continuous (P : Parameters) (V : H → ℝ)
    (hV : PotentialAssumptions P V) :
    Continuous (fun p : H × H ↦ averagedHessian V p.1 p.2) := by
  have heq : (fun p : H × H ↦ averagedHessian V p.1 p.2) =
      fun p ↦ ∫ t in Set.Ioc (0 : ℝ) 1, hessianOperator V (p.2 + t • (p.1 - p.2)) := by
    funext p
    exact intervalIntegral.integral_of_le (by norm_num)
  rw [heq]
  apply continuous_of_dominated (bound := fun _ : ℝ ↦ P.beta)
  · intro p
    exact (averagedHessian_curve_continuous V hV.regularity p.1 p.2).aestronglyMeasurable
  · intro p
    exact Filter.Eventually.of_forall fun t ↦ hessianOperator_norm_le P V hV _
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun t ↦
      (hessianOperator_continuous V hV.regularity).comp (by fun_prop)

end WassersteinMixing
