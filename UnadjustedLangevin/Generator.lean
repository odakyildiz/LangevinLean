import UnadjustedLangevin.Gibbs
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Laplacian

set_option linter.style.header false

/-! # Infinitesimal Gibbs invariance by integration of the Langevin generator

The identity is proved for compactly supported `C²` test functions by ordinary
integration by parts. Only the first derivative of the potential occurs. In
particular, Lipschitz continuity of its gradient suffices; there is no Hessian
assumption on the potential. Infinitesimal invariance and invariance of a
diffusion semigroup are distinct assertions.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The contribution of a direction to the overdamped Langevin generator. -/
def directionalGenerator (U φ : H → ℝ) (v x : H) : ℝ :=
  fderiv ℝ (fun z ↦ fderiv ℝ φ z v) x v -
    inner ℝ (gradient U x) v * fderiv ℝ φ x v

/-- The generator `∆φ - ⟪∇U,∇φ⟫`, expressed using the standard orthonormal basis. -/
def langevinGenerator (U φ : H → ℝ) (x : H) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ H),
    directionalGenerator U φ (stdOrthonormalBasis ℝ H i) x

/-- Conversion from the normalized Gibbs integral to its weighted Lebesgue integral. -/
theorem integral_gibbs_eq_weighted (U : H → ℝ) (hdiff : Differentiable ℝ U)
    (f : H → ℝ) :
    (∫ x, f x ∂gibbsMeasure U) = (gibbsPartition U)⁻¹.toReal *
      (∫ x, Real.exp (-U x) * f x ∂volume) := by
  rw [gibbsMeasure, integral_smul_measure]
  unfold gibbsWeight
  have hw : Measurable (fun x ↦ ENNReal.ofReal (Real.exp (-U x))) := by
    have hUc := hdiff.continuous
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- Continuous compactly supported functions are genuinely integrable under
Gibbs normalization. This rules out use of the total-integral default value. -/
theorem integrable_gibbs_of_continuous_hasCompactSupport
    (U : H → ℝ) (hdiff : Differentiable ℝ U) (f : H → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable f (gibbsMeasure U) := by
  have hw : Measurable (gibbsWeight U) := by
    exact (Real.continuous_exp.comp hdiff.continuous.neg).measurable.ennreal_ofReal
  have hi : Integrable f (volume.withDensity (gibbsWeight U)) := by
    apply (integrable_withDensity_iff_integrable_smul' hw
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr
    have hcw : Continuous (fun x ↦ Real.exp (-U x)) :=
      Real.continuous_exp.comp hdiff.continuous.neg
    simp only [gibbsWeight, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]
    exact (hcw.mul hf).integrable_of_hasCompactSupport hc.mul_left
  exact hi.smul_measure
    (ENNReal.inv_ne_top.mpr (ne_of_gt (gibbsPartition_pos U hdiff)))

omit [MeasurableSpace H] [BorelSpace H] in
/-- The Gibbs weight requires only one derivative of the potential. -/
theorem fderiv_exp_neg_apply (U : H → ℝ) (hdiff : Differentiable ℝ U) (x v : H) :
    fderiv ℝ (fun z ↦ Real.exp (-U z)) x v =
      -Real.exp (-U x) * inner ℝ (gradient U x) v := by
  have hd : HasFDerivAt (fun z ↦ Real.exp (-U z))
      (Real.exp (-U x) • (-fderiv ℝ U x)) x :=
    (hdiff x).hasFDerivAt.neg.exp
  rw [hd.fderiv]
  simp [inner_gradient_left]

/-- Weighted directional integration by parts, with all integrability conditions
derived from compact support of the test function. -/
theorem integral_weighted_directionalGenerator_eq_zero
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (v : H) :
    (∫ x, Real.exp (-U x) * directionalGenerator U φ v x ∂volume) = 0 := by
  let g : H → ℝ := fun x ↦ fderiv ℝ φ x v
  have hg : ContDiff ℝ 1 g :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hgc : HasCompactSupport g := hc.fderiv_apply ℝ v
  have hgd : Continuous (fun x ↦ fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hw : Continuous (fun x ↦ Real.exp (-U x)) :=
    Real.continuous_exp.comp hdiff.continuous.neg
  have hs : Continuous (fun x ↦ -Real.exp (-U x) * inner ℝ (gradient U x) v) :=
    hw.neg.mul (hLip.continuous.inner continuous_const)
  have hi₁ : Integrable (fun x ↦ fderiv ℝ (fun z ↦ Real.exp (-U z)) x v * g x)
      volume := by
    simp_rw [fderiv_exp_neg_apply U hdiff]
    exact (hs.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hi₂ : Integrable (fun x ↦ Real.exp (-U x) * fderiv ℝ g x v) volume :=
    (hw.mul hgd).integrable_of_hasCompactSupport (hgc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun x ↦ Real.exp (-U x) * g x) volume :=
    (hw.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun x _ ↦ (hdiff x).neg.exp) (fun x _ ↦ hg.differentiable (by norm_num) x)
  have hi₄ : Integrable (fun x ↦ Real.exp (-U x) *
      (inner ℝ (gradient U x) v * g x)) volume :=
    (hw.mul ((hLip.continuous.inner continuous_const).mul hg.continuous))
      |>.integrable_of_hasCompactSupport hgc.mul_left.mul_left
  simp_rw [fderiv_exp_neg_apply U hdiff] at hibp
  change (∫ x, Real.exp (-U x) *
    (fderiv ℝ g x v - inner ℝ (gradient U x) v * g x) ∂volume) = 0
  simp_rw [mul_sub]
  rw [integral_sub hi₂ hi₄]
  have heq : (fun x ↦ -Real.exp (-U x) * inner ℝ (gradient U x) v * g x) =
      (fun x ↦ -(Real.exp (-U x) * (inner ℝ (gradient U x) v * g x))) := by
    funext x
    ring
  rw [heq, integral_neg, neg_neg] at hibp
  exact sub_eq_zero.mpr hibp

/-- Every compactly supported `C²` test has zero directional generator integral
under the normalized Gibbs measure. -/
theorem integral_directionalGenerator_gibbs_eq_zero
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (v : H) :
    (∫ x, directionalGenerator U φ v x ∂gibbsMeasure U) = 0 := by
  rw [integral_gibbs_eq_weighted U hdiff,
    integral_weighted_directionalGenerator_eq_zero U L hdiff hLip φ hφ hc v,
    mul_zero]

omit [MeasurableSpace H] [BorelSpace H] in
/-- The directional generator is continuous under first-order regularity of `U`. -/
theorem continuous_directionalGenerator
    (U : H → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (v : H) :
    Continuous (directionalGenerator U φ v) := by
  have hg : ContDiff ℝ 1 (fun x ↦ fderiv ℝ φ x v) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).sub
    ((hLip.continuous.inner continuous_const).mul hg.continuous)

omit [MeasurableSpace H] [BorelSpace H] in
/-- Taking a generator preserves compact support of a test function. -/
theorem hasCompactSupport_directionalGenerator (U φ : H → ℝ)
    (hc : HasCompactSupport φ) (v : H) :
    HasCompactSupport (directionalGenerator U φ v) :=
  ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v).sub (hc.fderiv_apply ℝ v).mul_left

/-- Absolute integrability of each directional generator under Gibbs measure. -/
theorem integrable_directionalGenerator_gibbsMeasure
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (v : H) :
    Integrable (directionalGenerator U φ v) (gibbsMeasure U) :=
  integrable_gibbs_of_continuous_hasCompactSupport U hdiff _
    (continuous_directionalGenerator U L hLip φ hφ v)
    (hasCompactSupport_directionalGenerator U φ hc v)

/-- Absolute integrability of the entire Langevin generator under Gibbs measure. -/
theorem integrable_langevinGenerator_gibbsMeasure
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Integrable (langevinGenerator U φ) (gibbsMeasure U) := by
  exact integrable_finsetSum Finset.univ (fun _ _ ↦
    integrable_directionalGenerator_gibbsMeasure U L hdiff hLip φ hφ hc _)

/-- The full finite-dimensional generator has zero weighted Lebesgue integral. -/
theorem integral_weighted_langevinGenerator_eq_zero
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, Real.exp (-U x) * langevinGenerator U φ x ∂volume) = 0 := by
  have hi (v : H) : Integrable
      (fun x ↦ Real.exp (-U x) * directionalGenerator U φ v x) volume :=
    ((Real.continuous_exp.comp hdiff.continuous.neg).mul
      (continuous_directionalGenerator U L hLip φ hφ v))
        |>.integrable_of_hasCompactSupport
          (hasCompactSupport_directionalGenerator U φ hc v).mul_left
  simp_rw [langevinGenerator, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hi _)]
  simp only [integral_weighted_directionalGenerator_eq_zero U L hdiff hLip φ hφ hc,
    Finset.sum_const_zero]

/-- Gibbs infinitesimal invariance: `∫ (∆φ - ⟪∇U,∇φ⟫) dπ = 0`. -/
theorem integral_langevinGenerator_gibbs_eq_zero
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, langevinGenerator U φ x ∂gibbsMeasure U) = 0 := by
  rw [integral_gibbs_eq_weighted U hdiff,
    integral_weighted_langevinGenerator_eq_zero U L hdiff hLip φ hφ hc, mul_zero]

omit [MeasurableSpace H] [BorelSpace H] in
/-- Exact correspondence between the basis definition and the usual Laplacian
minus the gradient drift; no second derivative of `U` occurs. -/
theorem langevinGenerator_eq_laplacian_sub_inner (U φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (x : H) :
    langevinGenerator U φ x =
      Laplacian.laplacian φ x - inner ℝ (gradient U x) (gradient φ x) := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsecond (v : H) : fderiv ℝ (fun z ↦ fderiv ℝ φ z v) x v =
      iteratedFDeriv ℝ 2 φ x ![v, v] := by
    rw [fderiv_clm_apply (hd x) (differentiableAt_const v)]
    simp [iteratedFDeriv_two_apply, ContinuousLinearMap.flip_apply]
  unfold langevinGenerator directionalGenerator
  simp_rw [hsecond, Finset.sum_sub_distrib, ← inner_gradient_left]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  congr 1
  simpa only [real_inner_comm (gradient φ x)] using
    (stdOrthonormalBasis ℝ H).sum_inner_mul_inner (gradient U x) (gradient φ x)

/-- The standard mathematical generator formula has zero Gibbs integral. -/
theorem integral_laplacian_sub_gradient_gibbs_eq_zero
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (φ : H → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, Laplacian.laplacian φ x - inner ℝ (gradient U x) (gradient φ x)
      ∂gibbsMeasure U) = 0 := by
  simp_rw [← langevinGenerator_eq_laplacian_sub_inner U φ hφ]
  exact integral_langevinGenerator_gibbs_eq_zero U L hdiff hLip φ hφ hc

end ULA
