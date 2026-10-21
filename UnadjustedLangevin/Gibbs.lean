import UnadjustedLangevin.StrongConvexity
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

set_option linter.style.header false

/-! # Gibbs normalization and second moments from strong convexity

The potential is only assumed differentiable and strongly convex. No Hessian,
second derivative, stationary process, or concentration estimate is assumed.
Gaussian domination proves normalization and finite second moments directly.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped ENNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The unnormalized Gibbs weight. -/
def gibbsWeight (U : H → ℝ) (x : H) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-U x))

/-- The extended-valued partition function; divergent integrals stay infinite. -/
def gibbsPartition (U : H → ℝ) : ℝ≥0∞ := ∫⁻ x, gibbsWeight U x ∂volume

/-- Gibbs measure defined by its normalized Lebesgue density. -/
def gibbsMeasure (U : H → ℝ) : Measure H :=
  (gibbsPartition U)⁻¹ • volume.withDensity (gibbsWeight U)

/-- Integrability of a radial Gaussian in any finite-dimensional real Hilbert space. -/
theorem integrable_exp_neg_mul_norm_sq (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : H ↦ Real.exp (-a * ‖x‖ ^ 2)) volume := by
  have hi := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := H) (b := (a : ℂ)) (by simpa) 0 (0 : H)).re
  simpa [RCLike.re_to_complex, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_neg, ← Complex.ofReal_exp] using hi

omit [MeasurableSpace H] [BorelSpace H] in
/-- Absorbing the linear supporting-plane term gives a Gaussian tail bound. -/
theorem strongConvex_quadratic_lower_bound
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) (x : H) :
    U 0 - ‖gradient U 0‖ ^ 2 / m + m / 4 * ‖x‖ ^ 2 ≤ U x := by
  have hs := strong_first_order hdiff hsc (0 : H) x
  simp only [sub_zero] at hs
  have hip := neg_le_of_abs_le (abs_real_inner_le_norm (gradient U 0) x)
  have hy : ‖gradient U 0‖ * ‖x‖ ≤ m / 4 * ‖x‖ ^ 2 + ‖gradient U 0‖ ^ 2 / m := by
    apply (mul_le_mul_iff_right₀ hm).mp
    have hsq := sq_nonneg (m * ‖x‖ - 2 * ‖gradient U 0‖)
    nlinarith [show (‖gradient U 0‖ ^ 2 / m) * m = ‖gradient U 0‖ ^ 2 by
      exact div_mul_cancel₀ _ hm.ne']
  linarith

/-- The unnormalized Gibbs density is integrable from first-order assumptions alone. -/
theorem integrable_exp_neg_of_strongConvex
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    Integrable (fun x ↦ Real.exp (-U x)) volume := by
  let C := ‖gradient U 0‖ ^ 2 / m - U 0
  have hi := (integrable_exp_neg_mul_norm_sq (H := H) (m / 4) (by positivity)).const_mul
    (Real.exp C)
  refine hi.mono' ((Real.continuous_exp.comp hdiff.continuous.neg).aestronglyMeasurable) ?_
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := strongConvex_quadratic_lower_bound U m hm hdiff hsc x
  dsimp [C]
  linarith

/-- A quadratic factor is absorbed by half of a Gaussian's decay. -/
theorem integrable_norm_sq_mul_exp_neg_mul_norm_sq (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : H ↦ ‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) volume := by
  have hi := (integrable_exp_neg_mul_norm_sq (H := H) (a / 2) (by positivity)).const_mul
    ((a / 2)⁻¹)
  refine hi.mono' (by fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply (mul_le_mul_iff_left₀ (show 0 < a / 2 by positivity)).mp
  calc
    (‖x‖ ^ 2 * Real.exp (-a * ‖x‖ ^ 2)) * (a / 2) =
        (a / 2 * ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2) := by ring
    _ ≤ Real.exp (a / 2 * ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      linarith [Real.add_one_le_exp (a / 2 * ‖x‖ ^ 2)]
    _ = Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = ((a / 2)⁻¹ * Real.exp (-(a / 2) * ‖x‖ ^ 2)) * (a / 2) := by
      rw [mul_right_comm, inv_mul_cancel₀ (ne_of_gt (show 0 < a / 2 by positivity)), one_mul]

/-- The unnormalized Gibbs density has a finite quadratic moment. -/
theorem integrable_norm_sq_mul_exp_neg_of_strongConvex
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    Integrable (fun x ↦ ‖x‖ ^ 2 * Real.exp (-U x)) volume := by
  let C := ‖gradient U 0‖ ^ 2 / m - U 0
  have hi := (integrable_norm_sq_mul_exp_neg_mul_norm_sq (H := H) (m / 4)
    (by positivity)).const_mul (Real.exp C)
  refine hi.mono'
    (((continuous_norm.pow 2).mul
      (Real.continuous_exp.comp hdiff.continuous.neg)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ‖x‖ ^ 2 * Real.exp (-U x) ≤
        ‖x‖ ^ 2 * Real.exp (C + -(m / 4) * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Real.exp_le_exp.mpr
      have hs := strongConvex_quadratic_lower_bound U m hm hdiff hsc x
      dsimp [C]
      linarith
    _ = Real.exp C * (‖x‖ ^ 2 * Real.exp (-(m / 4) * ‖x‖ ^ 2)) := by
      rw [Real.exp_add]
      ring

/-- The Gibbs partition function is strictly positive. -/
theorem gibbsPartition_pos (U : H → ℝ) (hdiff : Differentiable ℝ U) :
    0 < gibbsPartition U := by
  unfold gibbsPartition gibbsWeight
  apply (lintegral_pos_iff_support (μ := (volume : Measure H))
    (f := fun x ↦ ENNReal.ofReal (Real.exp (-U x)))
    (Real.continuous_exp.comp hdiff.continuous.neg).measurable.ennreal_ofReal).mpr
  have hs : Function.support (fun x ↦ ENNReal.ofReal (Real.exp (-U x))) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  rw [hs]
  exact Measure.measure_univ_pos.mpr (NeZero.ne _)

/-- Strong convexity makes the Gibbs partition finite. -/
theorem gibbsPartition_ne_top
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    gibbsPartition U ≠ ⊤ := by
  have hi := integrable_exp_neg_of_strongConvex U m hm hdiff hsc
  exact ne_of_lt ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).mp
    hi.hasFiniteIntegral)

/-- The partition agrees with the ordinary integral, with its finiteness proved. -/
theorem gibbsPartition_eq_ofReal_integral
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    gibbsPartition U = ENNReal.ofReal (∫ x, Real.exp (-U x) ∂volume) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_neg_of_strongConvex U m hm hdiff hsc)
    (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).symm

/-- The ordinary real partition is strictly positive as well. -/
theorem integral_exp_neg_pos
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    0 < ∫ x, Real.exp (-U x) ∂volume :=
  integral_exp_pos (integrable_exp_neg_of_strongConvex U m hm hdiff hsc)

/-- Normalization of the Gibbs density is proved from first-order assumptions. -/
theorem isProbabilityMeasure_gibbsMeasure
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    IsProbabilityMeasure (gibbsMeasure U) := by
  constructor
  rw [gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]
  exact ENNReal.inv_mul_cancel (ne_of_gt (gibbsPartition_pos U hdiff))
    (gibbsPartition_ne_top U m hm hdiff hsc)

/-- The normalized Gibbs law has finite second moment. -/
theorem integrable_norm_sq_gibbsMeasure
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    Integrable (fun x : H ↦ ‖x‖ ^ 2) (gibbsMeasure U) := by
  have hi : Integrable (fun x : H ↦ ‖x‖ ^ 2) (volume.withDensity (gibbsWeight U)) := by
    change Integrable (fun x : H ↦ ‖x‖ ^ 2)
      (volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-U x))))
    apply (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure H))
      (f := fun x ↦ ENNReal.ofReal (Real.exp (-U x)))
      (Real.continuous_exp.comp hdiff.continuous.neg).measurable.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr
    simpa only [smul_eq_mul, mul_comm,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
      integrable_norm_sq_mul_exp_neg_of_strongConvex U m hm hdiff hsc
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr (ne_of_gt (gibbsPartition_pos U hdiff)))

/-- The identity random variable is square integrable under the Gibbs law. -/
theorem memLp_id_gibbsMeasure
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    MemLp (fun x : H ↦ x) 2 (gibbsMeasure U) := by
  exact (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr
    (integrable_norm_sq_gibbsMeasure U m hm hdiff hsc)

/-- Any fixed centering preserves the finite second moment of the Gibbs law. -/
theorem memLp_sub_const_gibbsMeasure
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) (z : H) :
    MemLp (fun x : H ↦ x - z) 2 (gibbsMeasure U) := by
  have := isProbabilityMeasure_gibbsMeasure U m hm hdiff hsc
  exact (memLp_id_gibbsMeasure U m hm hdiff hsc).sub (memLp_const z)

end ULA
