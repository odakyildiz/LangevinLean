import AverageLMC.LaplacianWeakStep
import Mathlib.Topology.UniformSpace.HeineCantor

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ContDiff

namespace AverageLMC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The C² Taylor remainder is the difference of actual second derivatives
at the base point and one point on the displacement segment. -/
theorem secondOrderExpansion_remainder_eq_second_difference
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (x v : H) :
    ∃ u ∈ Ioo (0 : ℝ) 1,
      φ (x + v) - ULA.secondOrderExpansion φ x v =
        (1 / 2 : ℝ) * ((iteratedFDeriv ℝ 2 φ (x + u • v) -
          iteratedFDeriv ℝ 2 φ x) (fun _ ↦ v)) := by
  let line : ℝ → H := fun t ↦ x + t • v
  let q : ℝ → ℝ := fun t ↦ φ (line t)
  have hline : ContDiff ℝ 2 line := by dsimp [line]; fun_prop
  have hq : ContDiff ℝ 2 q := hφ.comp hline
  have hlineD : deriv line = fun _ ↦ v := by
    funext t
    simpa [line] using (((hasDerivAt_id t).smul_const v).const_add x).deriv
  have hline2 : iteratedDeriv 2 line = fun _ ↦ 0 := by
    simp only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ', hlineD]
    funext t
    exact deriv_const t v
  have hqD (t : ℝ) : HasDerivAt q (fderiv ℝ φ (line t) v) t := by
    have hl : HasDerivAt line v t := by
      simpa only [line, one_smul, id_eq] using (((hasDerivAt_id t).smul_const v).const_add x)
    exact (hφ.differentiable (by norm_num) (line t)).hasFDerivAt.comp_hasDerivAt t hl
  have hq2 (t : ℝ) : iteratedDeriv 2 q t =
      iteratedFDeriv ℝ 2 φ (line t) (fun _ ↦ v) := by
    simpa only [Function.comp_def, hlineD, hline2, map_zero, add_zero] using
      iteratedDeriv_vcomp_two hφ.contDiffAt hline.contDiffAt (x := t)
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc (by norm_num)
  have hq1at : iteratedDerivWithin 1 q (uIcc 0 1) 0 = fderiv ℝ φ x v := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hq.of_le (by norm_num)).contDiffAt
      (by norm_num), iteratedDeriv_one, (hqD 0).deriv]
    simp [line]
  have hpoly : taylorWithinEval q 1 (uIcc 0 1) 0 1 = φ x + fderiv ℝ φ x v := by
    rw [taylorWithinEval_succ q 0 (uIcc 0 1) 0 1, taylor_within_zero_eval, hq1at]
    norm_num [q, line, smul_eq_mul]
  obtain ⟨u, hu, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := q) (n := 1) (x₀ := 0) (x := 1) (by norm_num) hq.contDiffOn
  refine ⟨u, by simpa using hu, ?_⟩
  rw [hpoly, hq2] at he
  norm_num [q, line] at he
  simp only [ULA.secondOrderExpansion, sub_apply]
  linarith

/-- Every compactly supported C² test has a uniformly small quadratic
Taylor remainder plus a cubic term. No third derivative is assumed. -/
theorem compactC2_secondOrderExpansion_remainder
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x v,
      |φ (x + v) - ULA.secondOrderExpansion φ x v| ≤
        η * ‖v‖ ^ 2 + C * ‖v‖ ^ 3 := by
  have hHc : Continuous (iteratedFDeriv ℝ 2 φ) := hφ.continuous_iteratedFDeriv'
  have hHuc := (hc.iteratedFDeriv (𝕜 := ℝ) 2).uniformContinuous_of_continuous hHc
  obtain ⟨B₀, hB₀⟩ := hHc.bounded_above_of_compact_support (hc.iteratedFDeriv 2)
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound (x : H) : ‖iteratedFDeriv ℝ 2 φ x‖ ≤ B := (hB₀ x).trans (le_max_left _ _)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp hHuc (2 * η) (by positivity)
  refine ⟨B / δ, div_nonneg hB hδ.le, ?_⟩
  intro x v
  obtain ⟨u, hu, he⟩ := secondOrderExpansion_remainder_eq_second_difference φ hφ x v
  have hop : |φ (x + v) - ULA.secondOrderExpansion φ x v| ≤
      (1 / 2 : ℝ) * ‖iteratedFDeriv ℝ 2 φ (x + u • v) - iteratedFDeriv ℝ 2 φ x‖ *
        ‖v‖ ^ 2 := by
    rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), ← Real.norm_eq_abs]
    have h := (iteratedFDeriv ℝ 2 φ (x + u • v) - iteratedFDeriv ℝ 2 φ x).le_opNorm
      (fun _ ↦ v)
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    nlinarith
  by_cases hv : ‖v‖ < δ
  · have hd : dist (x + u • v) x < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hu.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) hu.2.le).trans_lt hv
    have hsmall := hclose hd
    rw [dist_eq_norm] at hsmall
    have hs := mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg ‖v‖)
    have hlarge : 0 ≤ B / δ * ‖v‖ ^ 3 := by positivity
    nlinarith
  · have hv' : δ ≤ ‖v‖ := le_of_not_gt hv
    have hnorm : ‖iteratedFDeriv ℝ 2 φ (x + u • v) - iteratedFDeriv ℝ 2 φ x‖ ≤ 2 * B :=
      (norm_sub_le _ _).trans (by linarith [hbound (x + u • v), hbound x])
    have hquad := mul_le_mul_of_nonneg_right hnorm (sq_nonneg ‖v‖)
    have hlin : B * ‖v‖ ^ 2 ≤ B / δ * ‖v‖ ^ 3 := by
      apply (mul_le_mul_iff_right₀ hδ).mp
      have h := mul_le_mul_of_nonneg_left hv' (mul_nonneg hB (sq_nonneg ‖v‖))
      calc
        δ * (B * ‖v‖ ^ 2) = B * ‖v‖ ^ 2 * δ := by ring
        _ ≤ B * ‖v‖ ^ 2 * ‖v‖ := h
        _ = δ * (B / δ * ‖v‖ ^ 3) := by
          rw [← mul_assoc, mul_comm δ (B / δ), div_mul_cancel₀ _ hδ.ne']
          ring
    nlinarith [mul_nonneg hη.le (sq_nonneg ‖v‖)]

/-- Compact C² regularity already supplies the bounded Hessian needed for
the first-order drift part of the weak expansion. -/
theorem compactC2_gradient_lipschitz
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    ∃ L : ℝ≥0, LipschitzWith L (gradient φ) := by
  obtain ⟨C₀, hb⟩ := hφ.continuous_iteratedFDeriv'.bounded_above_of_compact_support
    (hc.iteratedFDeriv (𝕜 := ℝ) 2)
  let C := max C₀ 0
  let L : ℝ≥0 := ⟨C, le_max_right _ _⟩
  have hDdiff : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hDlip : LipschitzWith L (fderiv ℝ φ) := by
    apply lipschitzWith_of_nnnorm_fderiv_le hDdiff
    intro x
    change ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ C
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact (hb x).trans (le_max_left _ _)
  refine ⟨L, LipschitzWith.of_dist_le_mul (fun x y ↦ ?_)⟩
  simpa only [gradient, LinearIsometryEquiv.dist_map] using hDlip.dist_le_mul x y

/-- Uniform weak Gaussian consistency for compact C² tests, with a freely
small order-h coefficient and no third derivative assumption. -/
theorem compactC2_gaussian_weak_step
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (x v : H) (h : ℝ), 0 ≤ h → h ≤ 1 →
      |(∫ z : H, φ (x + h • v + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
        φ x - h * (fderiv ℝ φ x v + Laplacian.laplacian φ x)| ≤
          h * (ε + K * Real.sqrt h) * (1 + ‖v‖ ^ 2) := by
  obtain ⟨L, hLip⟩ := compactC2_gradient_lipschitz φ hφ hc
  have hz2 : Integrable (fun z : H ↦ ‖z‖ ^ 2) (stdGaussian H) :=
    (IsGaussian.memLp_id (stdGaussian H) 2 (by norm_num)).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)
  let G₂ := ∫ z : H, ‖z‖ ^ 2 ∂stdGaussian H
  have hG₂ : 0 ≤ G₂ := integral_nonneg (fun _ ↦ sq_nonneg _)
  let η := ε / (2 * (G₂ + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨C, hC, hrem⟩ := compactC2_secondOrderExpansion_remainder φ hφ hc η hη
  obtain ⟨C₀, hφbound⟩ := hφ.continuous.bounded_above_of_compact_support hc
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
  have hRpoint (z : H) : |R z| ≤ (η * s ^ 2) * ‖z‖ ^ 2 + (C * s ^ 3) * ‖z‖ ^ 3 := by
    simpa only [R, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, mul_pow,
      mul_assoc] using hrem x (s • z)
  have hR : Integrable R (stdGaussian H) := by
    apply ((hz2.const_mul (η * s ^ 2)).add (hz3.const_mul (C * s ^ 3))).mono'
      (show AEStronglyMeasurable R (stdGaussian H) by
        apply Continuous.aestronglyMeasurable
        dsimp [R, ULA.secondOrderExpansion]
        fun_prop)
    exact ae_of_all _ (fun z ↦ by simpa only [Real.norm_eq_abs, Pi.add_apply] using hRpoint z)
  have hpoly : Integrable (fun z : H ↦ ULA.secondOrderExpansion φ x (s • z))
      (stdGaussian H) := by
    have he : (fun z : H ↦ ULA.secondOrderExpansion φ x (s • z)) =
        fun z ↦ φ (x + s • z) - R z := by funext z; dsimp [R]; ring
    rw [he]
    exact hnoise.sub hR
  have hRint : |(∫ z : H, φ (x + s • z) ∂stdGaussian H) -
      φ x - h * Laplacian.laplacian φ x| ≤ η * s ^ 2 * G₂ + C * s ^ 3 * G₃ := by
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
      _ ≤ ∫ z : H, (η * s ^ 2) * ‖z‖ ^ 2 + (C * s ^ 3) * ‖z‖ ^ 3 ∂stdGaussian H :=
        integral_mono hR.abs ((hz2.const_mul _).add (hz3.const_mul _)) hRpoint
      _ = _ := by rw [integral_add (hz2.const_mul _) (hz3.const_mul _), integral_const_mul,
        integral_const_mul]
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
          (L : ℝ) * s * h * ‖v‖ * G₁ + (η * s ^ 2 * G₂ + C * s ^ 3 * G₃) := by
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
  have hsquare : s ^ 2 = 2 * h := Real.sq_sqrt (by positivity)
  rw [hscube, hsquare, hsform]
  have h1 := mul_le_mul_of_nonneg_left hhroot
    (by positivity : 0 ≤ (L : ℝ) / 2 * h * ‖v‖ ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hv
    (by positivity : 0 ≤ (L : ℝ) * Real.sqrt 2 * Real.sqrt h * h * G₁)
  have h3 : 0 ≤ C * (Real.sqrt 2) ^ 3 * h * Real.sqrt h * G₃ * ‖v‖ ^ 2 := by positivity
  have h4 : 0 ≤ (L : ℝ) / 2 * h * Real.sqrt h := by positivity
  have hηG : η * 2 * G₂ ≤ ε := by
    have heq : η * (2 * (G₂ + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith [hη.le]
  have hεscale := mul_le_mul_of_nonneg_right hηG hh
  have hεnorm : 0 ≤ h * ε * ‖v‖ ^ 2 := by positivity
  dsimp [K]
  nlinarith


theorem compactC2_continuous_laplacian
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) : Continuous (Laplacian.laplacian φ) := by
  have hDD : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
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


/-- The C² weak Euler expansion with a bounded measurable past weight;
its weight bound is required only almost everywhere. -/
theorem compactC2_gaussian_weighted_weak_step
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (x v : Ω → H) (w : Ω → ℝ) (A : ℝ)
    (hx : Measurable x) (hv : Measurable v) (hw : Measurable w)
    (hv₂ : MemLp v 2 P) (hA : 0 ≤ A) (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      |∫ a, w a * ((∫ z : H,
        φ (x a + h • v a + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
          φ (x a) - h * (fderiv ℝ φ (x a) (v a) +
            Laplacian.laplacian φ (x a))) ∂P| ≤
        A * h * (ε + K * Real.sqrt h) * (1 + ∫ a, ‖v a‖ ^ 2 ∂P) := by
  obtain ⟨K, hK, hbound⟩ := compactC2_gaussian_weak_step φ hφ hc ε hε
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
  have hLap := compactC2_continuous_laplacian φ hφ
  have hDm := hD.measurable
  have hLapm := hLap.measurable
  have hrmeas : AEStronglyMeasurable r P := by
    apply Measurable.aestronglyMeasurable
    dsimp [r]
    fun_prop
  have hpoint : ∀ᵐ a ∂P, |r a| ≤
      (A * h * (ε + K * Real.sqrt h)) * (1 + ‖v a‖ ^ 2) := by
    filter_upwards [hwA] with a hwa
    dsimp [r]
    rw [abs_mul]
    calc
      _ ≤ A * (h * (ε + K * Real.sqrt h) * (1 + ‖v a‖ ^ 2)) :=
        mul_le_mul hwa (hbound (x a) (v a) h hh hh1)
          (abs_nonneg _) hA
      _ = _ := by ring
  have hnorm : Integrable (fun a ↦ 1 + ‖v a‖ ^ 2) P :=
    (integrable_const (1 : ℝ)).add
      (hv₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hr : Integrable r P :=
    (hnorm.const_mul (A * h * (ε + K * Real.sqrt h))).mono' hrmeas
      (by filter_upwards [hpoint] with a ha; simpa only [Real.norm_eq_abs] using ha)
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ a, (A * h * (ε + K * Real.sqrt h)) * (1 + ‖v a‖ ^ 2) ∂P :=
      integral_mono_ae hr.abs (hnorm.const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ))
        (hv₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
      simp only [integral_const, probReal_univ, one_smul]

/-- A pointwise weak expansion lifts to a bounded past weight with the same
constant K, uniformly over the random centers and drifts. -/
theorem gaussian_weighted_weak_step_of_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x v : Ω → H) (w : Ω → ℝ) (A : ℝ)
    (hx : Measurable x) (hv : Measurable v) (hw : Measurable w)
    (hv₂ : MemLp v 2 P) (hA : 0 ≤ A) (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ (x v : H) (h : ℝ), 0 ≤ h → h ≤ 1 →
      |(∫ z : H, φ (x + h • v + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
        φ x - h * (fderiv ℝ φ x v + Laplacian.laplacian φ x)| ≤
          h * (ε + K * Real.sqrt h) * (1 + ‖v‖ ^ 2)) :
    ∀ h : ℝ, 0 ≤ h → h ≤ 1 →
      |∫ a, w a * ((∫ z : H,
        φ (x a + h • v a + Real.sqrt (2 * h) • z) ∂stdGaussian H) -
          φ (x a) - h * (fderiv ℝ φ (x a) (v a) +
            Laplacian.laplacian φ (x a))) ∂P| ≤
        A * h * (ε + K * Real.sqrt h) * (1 + ∫ a, ‖v a‖ ^ 2 ∂P) := by
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
  have hLap := compactC2_continuous_laplacian φ hφ
  have hDm := hD.measurable
  have hLapm := hLap.measurable
  have hrmeas : AEStronglyMeasurable r P := by
    apply Measurable.aestronglyMeasurable
    dsimp [r]
    fun_prop
  have hpoint : ∀ᵐ a ∂P, |r a| ≤
      (A * h * (ε + K * Real.sqrt h)) * (1 + ‖v a‖ ^ 2) := by
    filter_upwards [hwA] with a hwa
    dsimp [r]
    rw [abs_mul]
    calc
      _ ≤ A * (h * (ε + K * Real.sqrt h) * (1 + ‖v a‖ ^ 2)) :=
        mul_le_mul hwa (hbound (x a) (v a) h hh hh1)
          (abs_nonneg _) hA
      _ = _ := by ring
  have hnorm : Integrable (fun a ↦ 1 + ‖v a‖ ^ 2) P :=
    (integrable_const (1 : ℝ)).add
      (hv₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  have hr : Integrable r P :=
    (hnorm.const_mul (A * h * (ε + K * Real.sqrt h))).mono' hrmeas
      (by filter_upwards [hpoint] with a ha; simpa only [Real.norm_eq_abs] using ha)
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ a, (A * h * (ε + K * Real.sqrt h)) * (1 + ‖v a‖ ^ 2) ∂P :=
      integral_mono_ae hr.abs (hnorm.const_mul _) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ))
        (hv₂.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))]
      simp only [integral_const, probReal_univ, one_smul]

end AverageLMC
