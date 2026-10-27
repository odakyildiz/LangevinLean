import AverageLMC.Assumptions
import UnadjustedLangevin.GibbsScore
import UnadjustedLangevin.Generator
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gibbs score moments with the exact average coordinate smoothness

Translation in a single coordinate yields a sub-Gaussian bound for that
coordinate of the actual Gibbs score, with the literal supremum `M_j`.
Summing its second moments gives the paper's `p M_av` bound without any
second differentiability requirement.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AverageLMC

theorem coordinate_score_lmgf_le {p : ℕ}
    (f : State p → ℝ) (M : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f)) (hZ : ULA.gibbsPartition f ≠ ⊤)
    (j : Fin p) (a : ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-a * (gradient f x) j))
      ∂ULA.gibbsMeasure f) ≤
      ENNReal.ofReal (Real.exp (coordinateSmoothness f j / 2 * a ^ 2)) := by
  have hw : Measurable (ULA.gibbsWeight f) :=
    (Real.continuous_exp.comp hdiff.continuous.neg).measurable.ennreal_ofReal
  have hc : Continuous (fun x ↦ (gradient f x) j) :=
    (EuclideanSpace.proj j).continuous.comp hLip.continuous
  have hg : Measurable (fun x ↦ ENNReal.ofReal
      (Real.exp (-a * (gradient f x) j))) :=
    (Real.continuous_exp.comp (continuous_const.mul hc)).measurable.ennreal_ofReal
  have hpoint (x : State p) :
      ULA.gibbsWeight f x * ENNReal.ofReal (Real.exp (-a * (gradient f x) j)) ≤
      ENNReal.ofReal (Real.exp (coordinateSmoothness f j / 2 * a ^ 2)) *
        ULA.gibbsWeight f (x + a • coordinateVector j) := by
    have h := coordinate_upper_bound f M hdiff hLip j x a
    unfold ULA.gibbsWeight
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  have ht : (∫⁻ x, ULA.gibbsWeight f (x + a • coordinateVector j) ∂volume) =
      ULA.gibbsPartition f :=
    lintegral_add_right_eq_self (ULA.gibbsWeight f) (a • coordinateVector j)
  rw [ULA.gibbsMeasure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul volume hw hg]
  change (ULA.gibbsPartition f)⁻¹ *
    (∫⁻ x, ULA.gibbsWeight f x *
      ENNReal.ofReal (Real.exp (-a * (gradient f x) j)) ∂volume) ≤ _
  calc
    _ ≤ (ULA.gibbsPartition f)⁻¹ *
        (∫⁻ x, ENNReal.ofReal (Real.exp (coordinateSmoothness f j / 2 * a ^ 2)) *
          ULA.gibbsWeight f (x + a • coordinateVector j) ∂volume) :=
      mul_le_mul_right (lintegral_mono hpoint) _
    _ = _ := by
      rw [lintegral_const_mul _ (by fun_prop), ht, mul_left_comm,
        ENNReal.inv_mul_cancel (ne_of_gt (ULA.gibbsPartition_pos f hdiff)) hZ, mul_one]

theorem coordinate_score_subgaussian {p : ℕ}
    (f : State p → ℝ) (M : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f)) (hZ : ULA.gibbsPartition f ≠ ⊤)
    (j : Fin p) (hj : 0 ≤ coordinateSmoothness f j) :
    HasSubgaussianMGF (fun x ↦ (gradient f x) j)
      ⟨coordinateSmoothness f j, hj⟩ (ULA.gibbsMeasure f) := by
  have he (t : ℝ) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (t * (gradient f x) j))
        ∂ULA.gibbsMeasure f) ≤
        ENNReal.ofReal (Real.exp (coordinateSmoothness f j * t ^ 2 / 2)) := by
    have h := coordinate_score_lmgf_le f M hdiff hLip hZ j (-t)
    simpa only [neg_neg, neg_sq, div_mul_eq_mul_div] using h
  have hi (t : ℝ) : Integrable (fun x ↦ Real.exp (t * (gradient f x) j))
      (ULA.gibbsMeasure f) := by
    refine ⟨(Real.continuous_exp.comp (continuous_const.mul
      ((EuclideanSpace.proj j).continuous.comp hLip.continuous))).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ ↦ Real.exp_nonneg _)).mpr
      (lt_of_le_of_lt (he t) ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  intro t
  change (∫ x, Real.exp (t * (gradient f x) j) ∂ULA.gibbsMeasure f) ≤
    Real.exp (coordinateSmoothness f j * t ^ 2 / 2)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ Real.exp_nonneg _)
    (hi t).aestronglyMeasurable]
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (he t)
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _), NNReal.coe_mk] using h

/-- The sharp score moment bound from the paper's potential assumptions,
with its exact `M_av`, proved without assuming a score or Laplacian bound. -/
theorem integral_norm_sq_gradient_gibbs_le {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (m : ℝ) (M : ℝ≥0) (hm : 0 < m)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) :
    (∫ x, ‖gradient f x‖ ^ 2 ∂ULA.gibbsMeasure f) ≤
      (p : ℝ) * averageSmoothness f := by
  have hZ := ULA.gibbsPartition_ne_top f m hm hdiff hsc
  letI : IsProbabilityMeasure (ULA.gibbsMeasure f) := by
    constructor
    rw [ULA.gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ULA.gibbsPartition_pos f hdiff)) hZ
  have hj (j : Fin p) : 0 ≤ coordinateSmoothness f j :=
    hm.le.trans (strongConvex_le_coordinateSmoothness f m M hdiff hsc hLip j)
  have hi (j : Fin p) :
      Integrable (fun x ↦ (gradient f x) j ^ 2) (ULA.gibbsMeasure f) := by
    have hs := coordinate_score_subgaussian f M hdiff hLip hZ j (hj j)
    exact (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp (hs.memLp 2)
  have hb (j : Fin p) :
      (∫ x, (gradient f x) j ^ 2 ∂ULA.gibbsMeasure f) ≤ coordinateSmoothness f j :=
    ULA.integral_sq_le_of_subgaussian (ULA.gibbsMeasure f)
      (fun x ↦ (gradient f x) j) ⟨coordinateSmoothness f j, hj j⟩
      (coordinate_score_subgaussian f M hdiff hLip hZ j (hj j))
  calc
    _ = ∫ x, ∑ j : Fin p, (gradient f x) j ^ 2 ∂ULA.gibbsMeasure f := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by simp [EuclideanSpace.norm_sq_eq]
    _ = ∑ j : Fin p, ∫ x, (gradient f x) j ^ 2 ∂ULA.gibbsMeasure f :=
      integral_finsetSum Finset.univ (fun j _ ↦ hi j)
    _ ≤ ∑ j : Fin p, coordinateSmoothness f j := Finset.sum_le_sum fun j _ ↦ hb j
    _ = _ := by
      unfold averageSmoothness
      field_simp

private theorem integrable_gibbs_weighted {p : ℕ}
    (f : State p → ℝ) (hf : Differentiable ℝ f) (hZ : ULA.gibbsPartition f ≠ ⊤)
    (g : State p → ℝ) : Integrable g (ULA.gibbsMeasure f) ↔
      Integrable (fun x ↦ Real.exp (-f x) * g x) volume := by
  rw [ULA.gibbsMeasure, integrable_inv_smul_measure
    (ne_of_gt (ULA.gibbsPartition_pos f hf)) hZ]
  unfold ULA.gibbsWeight
  have hw : Measurable (fun x ↦ ENNReal.ofReal (Real.exp (-f x))) :=
    (Real.continuous_exp.comp hf.continuous.neg).measurable.ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul' hw
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- The derivative of the actual coordinate score is the corresponding
diagonal entry of the actual Hessian. -/
theorem fderiv_coordinate_score {p : ℕ} (f : State p → ℝ)
    (hf : ContDiff ℝ 2 f) (x : State p) (j : Fin p) :
    fderiv ℝ (fun y ↦ (gradient f y) j) x (coordinateVector j) = hessian f x j j := by
  have heq : (fun y ↦ (gradient f y) j) =
      fun y ↦ fderiv ℝ f y (coordinateVector j) := by
    funext y
    simp only [← inner_gradient_left, inner_coordinateVector]
  rw [heq, fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
    (differentiableAt_const _)]
  simp [hessian, iteratedFDeriv_two_apply]

private theorem coordinate_score_contDiff {p : ℕ} (f : State p → ℝ)
    (hf : ContDiff ℝ 2 f) (j : Fin p) :
    ContDiff ℝ 1 (fun y ↦ (gradient f y) j) := by
  have heq : (fun y ↦ (gradient f y) j) =
      fun y ↦ fderiv ℝ f y (coordinateVector j) := by
    funext y
    simp only [← inner_gradient_left, inner_coordinateVector]
  rw [heq]
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

private theorem coordinate_score_lipschitz {p : ℕ} (f : State p → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (j : Fin p) :
    LipschitzWith M (fun x ↦ (gradient f x) j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  exact (show ‖(gradient f x) j - (gradient f y) j‖ ≤
    ‖gradient f x - gradient f y‖ from by simpa using PiLp.norm_apply_le (gradient f x - gradient f y) j).trans (hLip.norm_sub_le x y)

/-- Integration by parts for the genuine Gibbs score, with all integrability
derived from first-order smoothness and finite normalization. -/
theorem integral_coordinate_score_sq_eq_hessian {p : ℕ}
    (f : State p → ℝ) (M : ℝ≥0) (hf : ContDiff ℝ 2 f)
    (hLip : LipschitzWith M (gradient f)) (hZ : ULA.gibbsPartition f ≠ ⊤)
    (j : Fin p) :
    (∫ x, (gradient f x) j ^ 2 ∂ULA.gibbsMeasure f) =
      ∫ x, hessian f x j j ∂ULA.gibbsMeasure f := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  letI : IsProbabilityMeasure (ULA.gibbsMeasure f) := by
    constructor
    rw [ULA.gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ULA.gibbsPartition_pos f hdiff)) hZ
  let ψ : State p → ℝ := fun x ↦ (gradient f x) j
  have hψ := coordinate_score_contDiff f hf j
  have hψLp : MemLp ψ 2 (ULA.gibbsMeasure f) :=
    (ULA.memLp_gradient_gibbsMeasure f M hdiff hLip hZ).eval_piLp j
  have hiψ : Integrable ψ (ULA.gibbsMeasure f) := hψLp.integrable (by norm_num)
  have hiψ2 : Integrable (fun x ↦ ψ x ^ 2) (ULA.gibbsMeasure f) :=
    (memLp_two_iff_integrable_sq hψLp.aestronglyMeasurable).mp hψLp
  have hD : Integrable (fun x ↦ fderiv ℝ ψ x (coordinateVector j))
      (ULA.gibbsMeasure f) := by
    apply (integrable_const (M : ℝ)).mono'
      ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable
    apply ae_of_all
    intro x
    calc
      _ ≤ ‖fderiv ℝ ψ x‖ * ‖coordinateVector j‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M : ℝ) := by
        rw [norm_coordinateVector, mul_one]
        exact (hψ.differentiable (by norm_num) x).hasFDerivAt.le_of_lipschitz
          (coordinate_score_lipschitz f M hLip j)
  have hw (x : State p) : fderiv ℝ (fun y ↦ Real.exp (-f y)) x (coordinateVector j) =
      -(Real.exp (-f x) * ψ x) := by
    have hd : HasFDerivAt (fun z ↦ Real.exp (-f z))
        (Real.exp (-f x) • (-fderiv ℝ f x)) x :=
      (hdiff x).hasFDerivAt.neg.exp
    rw [hd.fderiv]
    simp only [smul_apply, neg_apply,
      smul_eq_mul, ← inner_gradient_left, inner_coordinateVector, ψ]
    ring
  have h₁ : Integrable (fun x ↦ fderiv ℝ ψ x (coordinateVector j) * Real.exp (-f x))
      volume := by
    simpa only [mul_comm] using (integrable_gibbs_weighted f hdiff hZ _).mp hD
  have h₂ : Integrable (fun x ↦ ψ x * fderiv ℝ (fun y ↦ Real.exp (-f y)) x
      (coordinateVector j)) volume := by
    have hi := ((integrable_gibbs_weighted f hdiff hZ _).mp hiψ2).neg
    convert hi using 1
    funext x
    rw [hw]
    simp only [Pi.neg_apply]
    ring
  have h₃ : Integrable (fun x ↦ ψ x * Real.exp (-f x)) volume := by
    simpa only [mul_comm] using (integrable_gibbs_weighted f hdiff hZ _).mp hiψ
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃
    (fun x _ ↦ hψ.differentiable (by norm_num) x) (fun x _ ↦ hdiff.neg.exp x)
  have heq : (∫ x, Real.exp (-f x) * ψ x ^ 2 ∂volume) =
      ∫ x, Real.exp (-f x) * fderiv ℝ ψ x (coordinateVector j) ∂volume := by
    simp only [hw, mul_neg, integral_neg] at hibp
    have heq1 (x : State p) : ψ x * (Real.exp (-f x) * ψ x) =
        Real.exp (-f x) * ψ x ^ 2 := by ring
    simpa only [heq1, mul_comm, neg_inj] using hibp
  rw [ULA.integral_gibbs_eq_weighted f hdiff,
    ULA.integral_gibbs_eq_weighted f hdiff]
  simp_rw [← fderiv_coordinate_score f hf]
  exact congrArg (fun a ↦ (ULA.gibbsPartition f)⁻¹.toReal * a) heq

/-- The C² Gibbs score identity in Lemma 7. Both integrals are finite;
normalization finiteness follows from the stated potential assumptions. -/
theorem integral_norm_sq_gradient_eq_laplacian_of_partition {p : ℕ}
    (f : State p → ℝ) (M : ℝ≥0) (hf : ContDiff ℝ 2 f)
    (hLip : LipschitzWith M (gradient f)) (hZ : ULA.gibbsPartition f ≠ ⊤) :
    (∫ x, ‖gradient f x‖ ^ 2 ∂ULA.gibbsMeasure f) =
      ∫ x, laplacian f x ∂ULA.gibbsMeasure f := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  letI : IsProbabilityMeasure (ULA.gibbsMeasure f) := by
    constructor
    rw [ULA.gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ULA.gibbsPartition_pos f hdiff)) hZ
  have hscore (j : Fin p) : Integrable (fun x ↦ (gradient f x) j ^ 2)
      (ULA.gibbsMeasure f) :=
    (memLp_two_iff_integrable_sq
      ((ULA.memLp_gradient_gibbsMeasure f M hdiff hLip hZ).eval_piLp j).aestronglyMeasurable).mp
      ((ULA.memLp_gradient_gibbsMeasure f M hdiff hLip hZ).eval_piLp j)
  have hH (j : Fin p) : Integrable (fun x ↦ hessian f x j j) (ULA.gibbsMeasure f) := by
    have hDc := ((coordinate_score_contDiff f hf j).continuous_fderiv (by norm_num)).clm_apply (continuous_const : Continuous (fun _ : State p ↦ coordinateVector j))
    have hD (x : State p) : ‖fderiv ℝ (fun y ↦ (gradient f y) j) x (coordinateVector j)‖ ≤
        (M : ℝ) := by
      have ho := ((coordinate_score_contDiff f hf j).differentiable (by norm_num) x).hasFDerivAt.le_of_lipschitz (coordinate_score_lipschitz f M hLip j)
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by simpa using ho)
    simp_rw [← fderiv_coordinate_score f hf]
    exact (integrable_const (M : ℝ)).mono' hDc.aestronglyMeasurable (ae_of_all _ hD)
  calc
    _ = ∫ x, ∑ j : Fin p, (gradient f x) j ^ 2 ∂ULA.gibbsMeasure f := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by simp [EuclideanSpace.norm_sq_eq]
    _ = ∑ j : Fin p, ∫ x, (gradient f x) j ^ 2 ∂ULA.gibbsMeasure f :=
      integral_finsetSum _ (fun j _ ↦ hscore j)
    _ = ∑ j : Fin p, ∫ x, hessian f x j j ∂ULA.gibbsMeasure f := by
      congr 1
      funext j
      exact integral_coordinate_score_sq_eq_hessian f M hf hLip hZ j
    _ = ∫ x, ∑ j : Fin p, hessian f x j j ∂ULA.gibbsMeasure f :=
      (integral_finsetSum _ (fun j _ ↦ hH j)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x ↦ by simpa [Matrix.trace] using trace_hessian f x

/-- The C² score identity under the paper's strongly convex potential assumptions. -/
theorem integral_norm_sq_gradient_eq_laplacian {p : ℕ}
    (f : State p → ℝ) (m : ℝ) (M : ℝ≥0) (hm : 0 < m)
    (hf : ContDiff ℝ 2 f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) :
    (∫ x, ‖gradient f x‖ ^ 2 ∂ULA.gibbsMeasure f) =
      ∫ x, laplacian f x ∂ULA.gibbsMeasure f :=
  integral_norm_sq_gradient_eq_laplacian_of_partition f M hf hLip
    (ULA.gibbsPartition_ne_top f m hm (hf.differentiable (by norm_num)) hsc)

/-- Differentiating the two opposite coordinate upper models bounds the
actual diagonal Hessian by the exact coordinate Taylor supremum. -/
theorem hessian_diagonal_le_coordinateSmoothness {p : ℕ}
    (f : State p → ℝ) (M : ℝ≥0) (hf : ContDiff ℝ 2 f)
    (hLip : LipschitzWith M (gradient f)) (x : State p) (j : Fin p) :
    hessian f x j j ≤ coordinateSmoothness f j := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hψ := coordinate_score_contDiff f hf j
  have hline : HasDerivAt (fun a : ℝ ↦ x + a • coordinateVector j)
      (coordinateVector j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector j)).const_add x
  have hd : HasDerivAt (fun a : ℝ ↦ (gradient f (x + a • coordinateVector j)) j)
      (hessian f x j j) 0 := by
    have h := (hψ.differentiable (by norm_num) x).hasFDerivAt.comp_hasDerivAt_of_eq 0
      hline (by simp)
    simpa only [Function.comp_def, fderiv_coordinate_score f hf] using h
  have hb (a : ℝ) (ha : 0 < a) :
      ((gradient f (x + a • coordinateVector j)) j - (gradient f x) j) / a ≤
        coordinateSmoothness f j := by
    have hu := coordinate_upper_bound f M hdiff hLip j x a
    have hv := coordinate_upper_bound f M hdiff hLip j (x + a • coordinateVector j) (-a)
    have heq : (x + a • coordinateVector j) + (-a) • coordinateVector j = x := by module
    rw [heq, neg_sq] at hv
    apply (div_le_iff₀ ha).mpr
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith
  have hlim := hd.tendsto_slope_zero_right
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul, ← div_eq_inv_mul] at hlim
  apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact hb a ha

theorem laplacian_le_averageSmoothness {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hf : ContDiff ℝ 2 f)
    (hLip : LipschitzWith M (gradient f)) (x : State p) :
    laplacian f x ≤ (p : ℝ) * averageSmoothness f := by
  rw [← trace_hessian]
  change (∑ j : Fin p, hessian f x j j) ≤ (p : ℝ) * averageSmoothness f
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ ↦ hessian_diagonal_le_coordinateSmoothness f M hf hLip x j)
  calc
    _ ≤ ∑ j : Fin p, coordinateSmoothness f j := h
    _ = _ := by
      unfold averageSmoothness
      field_simp

/-- Strong convexity also bounds the actual diagonal Hessian from below. -/
theorem strongConvex_le_hessian_diagonal {p : ℕ}
    (f : State p → ℝ) (m : ℝ) (hf : ContDiff ℝ 2 f)
    (hsc : StrongConvexOn Set.univ m f) (x : State p) (j : Fin p) :
    m ≤ hessian f x j j := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hψ := coordinate_score_contDiff f hf j
  have hline : HasDerivAt (fun a : ℝ ↦ x + a • coordinateVector j)
      (coordinateVector j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector j)).const_add x
  have hd : HasDerivAt (fun a : ℝ ↦ (gradient f (x + a • coordinateVector j)) j)
      (hessian f x j j) 0 := by
    have h := (hψ.differentiable (by norm_num) x).hasFDerivAt.comp_hasDerivAt_of_eq 0
      hline (by simp)
    simpa only [Function.comp_def, fderiv_coordinate_score f hf] using h
  have hb (a : ℝ) (ha : 0 < a) : m ≤
      ((gradient f (x + a • coordinateVector j)) j - (gradient f x) j) / a := by
    have h := ULA.strong_gradient_monotone hdiff hsc (x + a • coordinateVector j) x
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, norm_coordinateVector,
      mul_one, sq_abs, inner_smul_right, inner_coordinateVector] at h
    change m * a ^ 2 ≤ a * ((gradient f (x + a • coordinateVector j)) j -
      (gradient f x) j) at h
    apply (le_div_iff₀ ha).mpr
    apply (mul_le_mul_iff_right₀ ha).mp
    nlinarith
  have hlim := hd.tendsto_slope_zero_right
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul, ← div_eq_inv_mul] at hlim
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact hb a ha

/-- Convexity makes the C² Laplacian nonnegative. -/
theorem laplacian_nonneg_of_convex {p : ℕ}
    (f : State p → ℝ) (hf : ContDiff ℝ 2 f) (hconv : ConvexOn ℝ Set.univ f)
    (x : State p) : 0 ≤ laplacian f x := by
  rw [← trace_hessian]
  change 0 ≤ ∑ j : Fin p, hessian f x j j
  apply Finset.sum_nonneg
  intro j hj
  exact strongConvex_le_hessian_diagonal f 0 hf (strongConvexOn_zero.mpr hconv) x j

/-- Exactly `M_{1,Δ}` in Lemma 7: the supremum of the actual Laplacian,
divided by dimension. -/
def averageLaplacianSmoothness {p : ℕ} (f : State p → ℝ) : ℝ :=
  sSup (Set.range (laplacian f)) / (p : ℝ)

theorem averageLaplacianSmoothness_le_averageSmoothness {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hf : ContDiff ℝ 2 f)
    (hLip : LipschitzWith M (gradient f)) :
    averageLaplacianSmoothness f ≤ averageSmoothness f := by
  unfold averageLaplacianSmoothness
  apply (div_le_iff₀ (by exact_mod_cast hp : (0 : ℝ) < p)).mpr
  apply csSup_le (Set.range_nonempty _)
  rintro q ⟨x, rfl⟩
  simpa only [mul_comm] using laplacian_le_averageSmoothness hp f M hf hLip x

/-- The nonnegative Laplacian is bounded by its genuine supremum. -/
theorem laplacian_le_averageLaplacianSmoothness {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hf : ContDiff ℝ 2 f)
    (hLip : LipschitzWith M (gradient f)) (x : State p) :
    laplacian f x ≤ (p : ℝ) * averageLaplacianSmoothness f := by
  have hb : BddAbove (Set.range (laplacian f)) :=
    ⟨(p : ℝ) * averageSmoothness f, by
      rintro q ⟨y, rfl⟩
      exact laplacian_le_averageSmoothness hp f M hf hLip y⟩
  have h := le_csSup hb (Set.mem_range_self x)
  convert h using 1
  unfold averageLaplacianSmoothness
  field_simp

theorem continuous_laplacian {p : ℕ} (f : State p → ℝ) (hf : ContDiff ℝ 2 f) :
    Continuous (laplacian f) := by
  have heq : laplacian f = fun x ↦ ∑ j : Fin p,
      fderiv ℝ (fun y ↦ (gradient f y) j) x (coordinateVector j) := by
    funext x
    simp_rw [fderiv_coordinate_score f hf]
    simpa [Matrix.trace] using (trace_hessian f x).symm
  rw [heq]
  exact continuous_finsetSum _ fun j _ ↦
    ((coordinate_score_contDiff f hf j).continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- Lemma 7 with the true Hessian, true Laplacian, exact Laplacian supremum,
and exact average coordinate Taylor supremum. Finiteness of the normalizing
partition is explicit, as required for `π` to denote a probability law. -/
theorem score_laplacian_identity_and_bounds {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hf : ContDiff ℝ 2 f)
    (hconv : ConvexOn ℝ Set.univ f) (hLip : LipschitzWith M (gradient f))
    (hZ : ULA.gibbsPartition f ≠ ⊤) :
    (∫ x, ‖gradient f x‖ ^ 2 ∂ULA.gibbsMeasure f) =
        (∫ x, |laplacian f x| ∂ULA.gibbsMeasure f) ∧
      (∫ x, |laplacian f x| ∂ULA.gibbsMeasure f) ≤
        (p : ℝ) * averageLaplacianSmoothness f ∧
      (p : ℝ) * averageLaplacianSmoothness f ≤ (p : ℝ) * averageSmoothness f := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  letI : IsProbabilityMeasure (ULA.gibbsMeasure f) := by
    constructor
    rw [ULA.gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ULA.gibbsPartition_pos f hdiff)) hZ
  have hn (x : State p) := laplacian_nonneg_of_convex f hf hconv x
  have habs : (fun x ↦ |laplacian f x|) = laplacian f :=
    funext fun x ↦ abs_of_nonneg (hn x)
  rw [habs]
  have hi : Integrable (laplacian f) (ULA.gibbsMeasure f) := by
    apply (integrable_const ((p : ℝ) * averageSmoothness f)).mono'
      (continuous_laplacian f hf).aestronglyMeasurable
    exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
      exact laplacian_le_averageSmoothness hp f M hf hLip x
  refine ⟨integral_norm_sq_gradient_eq_laplacian_of_partition f M hf hLip hZ, ?_, ?_⟩
  · have h := integral_mono hi (integrable_const ((p : ℝ) * averageLaplacianSmoothness f))
      (fun x ↦ laplacian_le_averageLaplacianSmoothness hp f M hf hLip x)
    simpa only [integral_const, probReal_univ, one_smul] using h
  · exact mul_le_mul_of_nonneg_left
      (averageLaplacianSmoothness_le_averageSmoothness hp f M hf hLip) (Nat.cast_nonneg p)

end AverageLMC
