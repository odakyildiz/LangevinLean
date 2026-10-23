import AverageLMC.LaplacianGaussianTaylor
import UnadjustedLangevin.Analysis.Smooth
import UnadjustedLangevin.Generator

set_option linter.style.header false

/-!
# Weak Euler estimates without a third moment of the initialization

The drift is expanded separately from the Gaussian increment. Thus only the
Gaussian noise enters the cubic Taylor remainder; the initial drift needs
only a second moment. This is the approximation used to pass to Dynkin's
formula for the constructed `L²` solution.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff

namespace AverageLMC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The global Hessian bound of a compact smooth test supplies an actual
Lipschitz constant for its gradient. -/
theorem compactSmooth_gradient_lipschitz
    (φ : H → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ L : ℝ≥0, LipschitzWith L (gradient φ) := by
  obtain ⟨C, hC, hb⟩ := hc.exists_bound_iteratedFDeriv hφ 2
  let L : ℝ≥0 := ⟨C, hC⟩
  have hDdiff : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by simp)).differentiable (by norm_num)
  have hDlip : LipschitzWith L (fderiv ℝ φ) := by
    apply lipschitzWith_of_nnnorm_fderiv_le hDdiff
    intro x
    change ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ C
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hb 2 le_rfl x
  refine ⟨L, LipschitzWith.of_dist_le_mul (fun x y ↦ ?_)⟩
  simpa only [gradient, LinearIsometryEquiv.dist_map] using hDlip.dist_le_mul x y

/-- The absolute first-order remainder from the ordinary Lipschitz gradient
assumption. This is applied only to the compact test, not to the potential. -/
theorem firstOrder_remainder_abs_le
    (φ : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ φ)
    (hLip : LipschitzWith L (gradient φ)) (x d : H) :
    |φ (x + d) - φ x - fderiv ℝ φ x d| ≤ (L : ℝ) / 2 * ‖d‖ ^ 2 := by
  have hneg (z : H) : gradient (fun x ↦ -φ x) z = -gradient φ z := by
    simp only [gradient, fderiv_fun_neg, map_neg]
  have hLipNeg : LipschitzWith L (gradient (fun x ↦ -φ x)) := by
    have heq : gradient (fun x ↦ -φ x) = fun x ↦ -gradient φ x := funext hneg
    rw [heq]
    exact hLip.neg
  have hu := ULA.Analysis.smooth_upper_bound φ L hdiff hLip x (x + d)
  have hl := ULA.Analysis.smooth_upper_bound (fun x ↦ -φ x) L hdiff.neg hLipNeg
    x (x + d)
  simp only [add_sub_cancel_left, inner_gradient_left] at hu
  simp only [add_sub_cancel_left, hneg, inner_neg_left, inner_gradient_left] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Expanding the drift after the noise needs only a quadratic drift term.
The mixed term has order `h^(3/2)` after Gaussian averaging. -/
theorem shifted_firstOrder_remainder_abs_le
    (φ : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ φ)
    (hLip : LipschitzWith L (gradient φ)) (x w d : H) :
    |φ (x + w + d) - φ (x + w) - fderiv ℝ φ x d| ≤
      (L : ℝ) / 2 * ‖d‖ ^ 2 + (L : ℝ) * ‖w‖ * ‖d‖ := by
  have hr := firstOrder_remainder_abs_le φ L hdiff hLip (x + w) d
  have hD : |fderiv ℝ φ (x + w) d - fderiv ℝ φ x d| ≤
      (L : ℝ) * ‖w‖ * ‖d‖ := by
    simp only [← inner_gradient_left, ← inner_sub_left]
    apply (abs_real_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [add_sub_cancel_left] using hLip.norm_sub_le (x + w) x
  have heq : φ (x + w + d) - φ (x + w) - fderiv ℝ φ x d =
      (φ (x + w + d) - φ (x + w) - fderiv ℝ φ (x + w) d) +
        (fderiv ℝ φ (x + w) d - fderiv ℝ φ x d) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hr hD)

/-- Weak Gaussian Euler consistency with only a second moment of the drift.
All constants depend on the compact test and the Gaussian law, while `x`,
`v`, and `h` are arbitrary. This form is suitable for bounded past-measurable
weights and refinement of a Brownian Euler partition. -/
theorem compactSmooth_gaussian_weak_step
    (φ : H → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x v : H) (h : ℝ), 0 ≤ h → h ≤ 1 →
      |(∫ z : H, φ (x + h • v + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
        φ x - h * (fderiv ℝ φ x v + Laplacian.laplacian φ x)| ≤
          K * h * Real.sqrt h * (1 + ‖v‖ ^ 2) := by
  obtain ⟨L, hLip⟩ := compactSmooth_gradient_lipschitz φ hφ hc
  obtain ⟨C, hC, hrem⟩ := ULA.compactSmooth_secondOrderExpansion_remainder φ hφ hc
  obtain ⟨C₀, hC₀, hb⟩ := hc.exists_bound_iteratedFDeriv hφ 0
  have hφbound (y : H) : ‖φ y‖ ≤ C₀ := by
    simpa only [norm_iteratedFDeriv_zero] using hb 0 le_rfl y
  have hz1 : Integrable (fun z : H ↦ ‖z‖) (stdGaussian H) :=
    IsGaussian.integrable_id.norm
  have hz3 : Integrable (fun z : H ↦ ‖z‖ ^ 3) (stdGaussian H) :=
    (IsGaussian.memLp_id (stdGaussian H) 3 (by norm_num)).integrable_norm_pow
      (by norm_num : (3 : ℕ) ≠ 0)
  let G₁ := ∫ z : H, ‖z‖ ∂stdGaussian H
  let G₃ := ∫ z : H, ‖z‖ ^ 3 ∂stdGaussian H
  let K := (L : ℝ) / 2 + (L : ℝ) * Real.sqrt 2 * G₁ +
    C * (Real.sqrt 2) ^ 3 * G₃
  have hG₁ : 0 ≤ G₁ := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hG₃ : 0 ≤ G₃ := integral_nonneg (fun _ ↦ by positivity)
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro x v h hh hh1
  let s := Real.sqrt (2 * h)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hbounded (T : H → H) (hT : Continuous T) :
      Integrable (fun z ↦ φ (T z)) (stdGaussian H) := by
    apply (MemLp.of_bound (hφ.continuous.comp hT).aestronglyMeasurable C₀
      (ae_of_all _ (fun z ↦ hφbound (T z))) : MemLp _ 1 _).integrable le_rfl
  have hnoise : Integrable (fun z : H ↦ φ (x + s • z)) (stdGaussian H) :=
    hbounded _ (by fun_prop)
  have hstep : Integrable (fun z : H ↦ φ (x + s • z + h • v)) (stdGaussian H) :=
    hbounded _ (by fun_prop)
  let R : H → ℝ := fun z ↦ φ (x + s • z) - ULA.secondOrderExpansion φ x (s • z)
  have hRpoint (z : H) : |R z| ≤ (C * s ^ 3) * ‖z‖ ^ 3 := by
    simpa only [R, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, mul_pow,
      mul_assoc] using hrem x (s • z)
  have hR : Integrable R (stdGaussian H) := by
    apply (hz3.const_mul (C * s ^ 3)).mono'
      (show AEStronglyMeasurable R (stdGaussian H) by
        apply Continuous.aestronglyMeasurable
        dsimp [R, ULA.secondOrderExpansion]
        fun_prop)
    exact ae_of_all _ (fun z ↦ by simpa only [Real.norm_eq_abs] using hRpoint z)
  have hpoly : Integrable (fun z : H ↦ ULA.secondOrderExpansion φ x (s • z))
      (stdGaussian H) := by
    have he : (fun z : H ↦ ULA.secondOrderExpansion φ x (s • z)) =
        fun z ↦ φ (x + s • z) - R z := by funext z; dsimp [R]; ring
    rw [he]
    exact hnoise.sub hR
  have hRint : |(∫ z : H, φ (x + s • z) ∂stdGaussian H) -
      φ x - h * Laplacian.laplacian φ x| ≤ C * s ^ 3 * G₃ := by
    have hi := integral_sub hnoise hpoly
    have hp := integral_gaussian_secondOrderExpansion φ x 0 h hh
    have hzero : iteratedFDeriv ℝ 2 φ x (fun _ ↦ 0) = 0 :=
      (iteratedFDeriv ℝ 2 φ x).map_coord_zero (0 : Fin 2) rfl
    simp only [smul_zero, zero_add, map_zero, hzero, mul_zero, add_zero] at hp
    change (∫ z : H, ULA.secondOrderExpansion φ x (s • z) ∂stdGaussian H) =
      φ x + h * Laplacian.laplacian φ x at hp
    rw [hp] at hi
    have he : (∫ z : H, R z ∂stdGaussian H) =
        (∫ z : H, φ (x + s • z) ∂stdGaussian H) -
          φ x - h * Laplacian.laplacian φ x := by dsimp [R]; rw [hi]; ring
    rw [← he]
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ z : H, (C * s ^ 3) * ‖z‖ ^ 3 ∂stdGaussian H :=
        integral_mono hR.abs (hz3.const_mul _) hRpoint
      _ = _ := by rw [integral_const_mul]
  let D : H → ℝ := fun z ↦
    φ (x + s • z + h • v) - φ (x + s • z) - h * fderiv ℝ φ x v
  have hD : Integrable D (stdGaussian H) := (hstep.sub hnoise).sub (integrable_const _)
  have hDpoint (z : H) : |D z| ≤
      (L : ℝ) / 2 * h ^ 2 * ‖v‖ ^ 2 +
        ((L : ℝ) * s * h * ‖v‖) * ‖z‖ := by
    have hb := shifted_firstOrder_remainder_abs_le φ L
      (hφ.differentiable (by simp)) hLip x (s • z) (h • v)
    simpa only [D, map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hs, abs_of_nonneg hh, mul_pow, mul_assoc, mul_comm,
      mul_left_comm] using hb
  have hDint : |(∫ z : H, φ (x + s • z + h • v) ∂stdGaussian H) -
      (∫ z : H, φ (x + s • z) ∂stdGaussian H) - h * fderiv ℝ φ x v| ≤
        (L : ℝ) / 2 * h ^ 2 * ‖v‖ ^ 2 + (L : ℝ) * s * h * ‖v‖ * G₁ := by
    have hi := integral_sub (hstep.sub hnoise) (integrable_const (h * fderiv ℝ φ x v))
    simp only [Pi.sub_apply, integral_sub hstep hnoise, integral_const,
      probReal_univ, one_smul] at hi
    rw [← hi]
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ z : H, (L : ℝ) / 2 * h ^ 2 * ‖v‖ ^ 2 +
          ((L : ℝ) * s * h * ‖v‖) * ‖z‖ ∂stdGaussian H :=
        integral_mono hD.abs
          ((integrable_const _).add (hz1.const_mul _)) hDpoint
      _ = _ := by
        rw [integral_add (integrable_const _) (hz1.const_mul _)]
        simp only [integral_const, probReal_univ, one_smul, integral_const_mul, G₁]
  have htotal : |(∫ z : H, φ (x + h • v + s • z) ∂stdGaussian H) -
      φ x - h * (fderiv ℝ φ x v + Laplacian.laplacian φ x)| ≤
        (L : ℝ) / 2 * h ^ 2 * ‖v‖ ^ 2 +
          (L : ℝ) * s * h * ‖v‖ * G₁ + C * s ^ 3 * G₃ := by
    have he : (∫ z : H, φ (x + h • v + s • z) ∂stdGaussian H) -
        φ x - h * (fderiv ℝ φ x v + Laplacian.laplacian φ x) =
        ((∫ z : H, φ (x + s • z + h • v) ∂stdGaussian H) -
          (∫ z : H, φ (x + s • z) ∂stdGaussian H) - h * fderiv ℝ φ x v) +
        ((∫ z : H, φ (x + s • z) ∂stdGaussian H) -
          φ x - h * Laplacian.laplacian φ x) := by
      simp only [add_right_comm x (h • v) (s • _)]
      ring
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add hDint hRint)
  have hroot : Real.sqrt h ≤ 1 := (Real.sqrt_le_one).mpr hh1
  have hhroot : h ≤ Real.sqrt h := by
    nlinarith [Real.sq_sqrt hh, Real.sqrt_nonneg h]
  have hv : ‖v‖ ≤ 1 + ‖v‖ ^ 2 := by nlinarith [sq_nonneg (‖v‖ - 1)]
  have hsform : s = Real.sqrt 2 * Real.sqrt h := Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) h
  have hscube : s ^ 3 = (Real.sqrt 2) ^ 3 * h * Real.sqrt h := by
    calc
      s ^ 3 = (Real.sqrt 2) ^ 3 * (Real.sqrt h) ^ 2 * Real.sqrt h := by
        rw [hsform]; ring
      _ = _ := by rw [Real.sq_sqrt hh]
  apply htotal.trans
  rw [hscube, hsform]
  have h1 := mul_le_mul_of_nonneg_left hhroot
    (by positivity : 0 ≤ (L : ℝ) / 2 * h * ‖v‖ ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hv
    (by positivity : 0 ≤ (L : ℝ) * Real.sqrt 2 * Real.sqrt h * h * G₁)
  have h3 : 0 ≤ C * (Real.sqrt 2) ^ 3 * h * Real.sqrt h * G₃ * ‖v‖ ^ 2 := by positivity
  have h4 : 0 ≤ (L : ℝ) / 2 * h * Real.sqrt h := by positivity
  dsimp [K]
  nlinarith

/-- The Laplacian of a compact smooth test is continuous, by the actual
finite sum of second derivatives. -/
theorem compactSmooth_continuous_laplacian
    (φ : H → ℝ) (hφ : ContDiff ℝ ∞ φ) : Continuous (Laplacian.laplacian φ) := by
  have hDD : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 2) (by simp)).continuous_fderiv (by norm_num)
  have he : Laplacian.laplacian φ = fun x ↦
      ∑ i : Fin (Module.finrank ℝ H), fderiv ℝ (fderiv ℝ φ) x
        (stdOrthonormalBasis ℝ H i) (stdOrthonormalBasis ℝ H i) := by
    funext x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp only [iteratedFDeriv_two_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  rw [he]
  exact continuous_finset_sum _ (fun i _ ↦
    (hDD.clm_apply continuous_const).clm_apply continuous_const)

/-- Gaussian weak consistency remains valid after averaging with a bounded
past-measurable weight and a square-integrable random drift. Only the
ordinary product integral occurs here, so independence can be discharged
by identifying the Brownian increment's joint law with this product law. -/
theorem compactSmooth_gaussian_weighted_weak_step
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : H → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (x v : Ω → H) (w : Ω → ℝ) (A : ℝ)
    (hx : Measurable x) (hv : Measurable v) (hw : Measurable w)
    (hv₂ : MemLp v 2 P) (hA : 0 ≤ A) (hwA : ∀ a, |w a| ≤ A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      |∫ a, w a * ((∫ z : H,
        φ (x a + h • v a + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
          φ (x a) - h * (fderiv ℝ φ (x a) (v a) +
            Laplacian.laplacian φ (x a))) ∂P| ≤
        A * K * h * Real.sqrt h * (1 + ∫ a, ‖v a‖ ^ 2 ∂P) := by
  obtain ⟨K, hK, hbound⟩ := compactSmooth_gaussian_weak_step φ hφ hc
  refine ⟨K, hK, ?_⟩
  intro h hh hh1
  let r : Ω → ℝ := fun a ↦ w a * ((∫ z : H,
    φ (x a + h • v a + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
      φ (x a) - h * (fderiv ℝ φ (x a) (v a) + Laplacian.laplacian φ (x a)))
  have hφm := hφ.continuous.measurable
  have hjoint : Measurable (fun p : Ω × H ↦
      φ (x p.1 + h • v p.1 + Real.sqrt (2 * h) • p.2)) := by
    fun_prop
  have hint : Measurable (fun a ↦ ∫ z : H,
      φ (x a + h • v a + Real.sqrt (2 * h) • z) ∂stdGaussian H) :=
    hjoint.stronglyMeasurable.integral_prod_right.measurable
  have hD : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hLap := compactSmooth_continuous_laplacian φ hφ
  have hDm := hD.measurable
  have hLapm := hLap.measurable
  have hrmeas : AEStronglyMeasurable r P := by
    apply Measurable.aestronglyMeasurable
    dsimp [r]
    fun_prop
  have hpoint (a : Ω) : |r a| ≤
      (A * K * h * Real.sqrt h) * (1 + ‖v a‖ ^ 2) := by
    dsimp [r]
    rw [abs_mul]
    calc
      _ ≤ A * (K * h * Real.sqrt h * (1 + ‖v a‖ ^ 2)) :=
        mul_le_mul (hwA a) (hbound (x a) (v a) h hh hh1)
          (abs_nonneg _) hA
      _ = _ := by ring
  have hnorm : Integrable (fun a ↦ 1 + ‖v a‖ ^ 2) P :=
    (integrable_const (1 : ℝ)).add
      (hv₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hr : Integrable r P :=
    (hnorm.const_mul (A * K * h * Real.sqrt h)).mono' hrmeas
      (ae_of_all _ (fun a ↦ by simpa only [Real.norm_eq_abs] using hpoint a))
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ a, (A * K * h * Real.sqrt h) * (1 + ‖v a‖ ^ 2) ∂P :=
      integral_mono hr.abs (hnorm.const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ))
        (hv₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
      simp only [integral_const, probReal_univ, one_smul]

end AverageLMC
