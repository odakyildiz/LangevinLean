import ProximalLangevin.SplittingL2Energy
import UnadjustedLangevin.LSI.GaussianDrift

set_option linter.style.header false

/-! # The parameter noise removed by MYPGD

The mask is an actual orthogonal coordinate projection. Its Gaussian mean is
zero and its second moment is exactly the parameter dimension.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace BigOperators
namespace ProximalLangevin

/-- Retain the parameter coordinates and erase the latent coordinates. -/
def parameterNoiseCLM {N dθ dx : ℕ} : IPLA.State N dθ dx →L[ℝ] IPLA.State N dθ dx :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (Sum.elim (fun j => z (Sum.inl j)) (fun _ => 0))
      map_add' := by intro x y; ext i; cases i <;> simp
      map_smul' := by intro a x; ext i; cases i <;> simp }

@[simp] theorem parameterNoiseCLM_parameter {N dθ dx : ℕ}
    (z : IPLA.State N dθ dx) (j : Fin dθ) :
    parameterNoiseCLM z (Sum.inl j) = z (Sum.inl j) := rfl

@[simp] theorem parameterNoiseCLM_particle {N dθ dx : ℕ}
    (z : IPLA.State N dθ dx) (j : Fin N × Fin dx) :
    parameterNoiseCLM z (Sum.inr j) = 0 := rfl

/-- Retain precisely the latent noise of the original particle scheme. -/
def latentNoiseCLM {N dθ dx : ℕ} : IPLA.State N dθ dx →L[ℝ] IPLA.State N dθ dx :=
  ContinuousLinearMap.id ℝ _ - parameterNoiseCLM

@[simp] theorem latentNoiseCLM_parameter {N dθ dx : ℕ}
    (z : IPLA.State N dθ dx) (j : Fin dθ) :
    latentNoiseCLM z (Sum.inl j) = 0 := by simp [latentNoiseCLM]

@[simp] theorem latentNoiseCLM_particle {N dθ dx : ℕ}
    (z : IPLA.State N dθ dx) (j : Fin N × Fin dx) :
    latentNoiseCLM z (Sum.inr j) = z (Sum.inr j) := by simp [latentNoiseCLM]

theorem parameterNoise_norm_sq {N dθ dx : ℕ} (z : IPLA.State N dθ dx) :
    ‖parameterNoiseCLM z‖ ^ 2 = ∑ j : Fin dθ, (z (Sum.inl j)) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]

theorem parameterNoise_lipschitz {N dθ dx : ℕ} :
    LipschitzWith 1 (@parameterNoiseCLM N dθ dx) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, NNReal.coe_one, one_mul, ← map_sub]
  have hs : ‖parameterNoiseCLM (x - y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [parameterNoise_norm_sq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (parameterNoiseCLM (x-y)), norm_nonneg (x-y)]

theorem integral_parameterNoise_stdGaussian {N dθ dx : ℕ} :
    (∫ z : IPLA.State N dθ dx, parameterNoiseCLM z ∂stdGaussian _) = 0 := by
  have h := (@parameterNoiseCLM N dθ dx).integral_comp_comm
    (μ := stdGaussian (IPLA.State N dθ dx)) (φ := fun z => z) IsGaussian.integrable_id
  simpa only [integral_id_stdGaussian, map_zero] using h

theorem integral_parameterNoise_sq_stdGaussian {N dθ dx : ℕ} :
    (∫ z : IPLA.State N dθ dx, ‖parameterNoiseCLM z‖ ^ 2 ∂stdGaussian _) = (dθ : ℝ) := by
  have hz : MemLp (fun z : IPLA.State N dθ dx => z) 2 (stdGaussian _) :=
    IsGaussian.memLp_id _ 2 (by norm_num)
  have hi (j : Fin dθ) : Integrable
      (fun z : IPLA.State N dθ dx => (z (Sum.inl j)) ^ 2) (stdGaussian _) := by
    simpa only [EuclideanSpace.inner_single_left, one_mul, conj_trivial] using
      (hz.const_inner (EuclideanSpace.single (Sum.inl j) 1)).integrable_sq
  have hm (j : Fin dθ) :
      (∫ z : IPLA.State N dθ dx, (z (Sum.inl j)) ^ 2 ∂stdGaussian _) = 1 := by
    have hv := variance_dual_stdGaussian
      (innerSL ℝ (EuclideanSpace.single (Sum.inl j) (1 : ℝ) : IPLA.State N dθ dx))
    rw [variance_eq_integral (by fun_prop), integral_strongDual_stdGaussian] at hv
    simpa only [innerSL_apply_apply, EuclideanSpace.inner_single_left, one_mul, conj_trivial,
      sub_zero, innerSL_apply_norm, PiLp.norm_single, norm_one, one_pow] using hv
  simp_rw [parameterNoise_norm_sq]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Exact independent-noise identity, for an arbitrary square-integrable source.
The mixed term vanishes by the actual product Gaussian law. -/
theorem integral_add_parameterNoise_sq
    {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    {N dθ dx : ℕ} (g : A → IPLA.State N dθ dx) (hg : MemLp g 2 μ) (b : ℝ) :
    (∫ p : A × IPLA.State N dθ dx, ‖g p.1 + b • parameterNoiseCLM p.2‖ ^ 2
      ∂μ.prod (stdGaussian _)) = (∫ x, ‖g x‖ ^ 2 ∂μ) + b ^ 2 * (dθ : ℝ) := by
  have hz : MemLp (fun z : IPLA.State N dθ dx => parameterNoiseCLM z) 2 (stdGaussian _) :=
    (@parameterNoiseCLM N dθ dx).comp_memLp' (IsGaussian.memLp_id _ 2 (by norm_num))
  have hg1 := hg.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hz1 := hz.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hgsq := (hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).comp_fst
    (stdGaussian (IPLA.State N dθ dx))
  have hzsq := (hz.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).comp_snd μ
  have hcross : Integrable
      (fun p : A × IPLA.State N dθ dx => ⟪g p.1, parameterNoiseCLM p.2⟫)
      (μ.prod (stdGaussian _)) :=
    hg1.op_fst_snd (by fun_prop)
      ⟨1, by intro x y; simpa using norm_inner_le_norm (𝕜 := ℝ) x y⟩ hz1
  have hzero : (∫ p : A × IPLA.State N dθ dx, ⟪g p.1, parameterNoiseCLM p.2⟫
      ∂μ.prod (stdGaussian _)) = 0 := by
    have h := integral_prod_bilin (innerSL ℝ) hg1 hz1
    change (∫ p : A × IPLA.State N dθ dx, ⟪g p.1, parameterNoiseCLM p.2⟫
      ∂μ.prod (stdGaussian _)) = ⟪∫ x, g x ∂μ, ∫ z, parameterNoiseCLM z ∂stdGaussian _⟫ at h
    simpa only [integral_parameterNoise_stdGaussian, inner_zero_right] using h
  have hexpand (p : A × IPLA.State N dθ dx) :
      ‖g p.1 + b • parameterNoiseCLM p.2‖ ^ 2 =
        ‖g p.1‖ ^ 2 + 2*b*⟪g p.1, parameterNoiseCLM p.2⟫ +
        b^2*‖parameterNoiseCLM p.2‖^2 := by
    simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right]
    ring
  simp_rw [hexpand]
  rw [integral_add (f := fun p : A × IPLA.State N dθ dx =>
      ‖g p.1‖ ^ 2 + 2*b*⟪g p.1, parameterNoiseCLM p.2⟫)
      (g := fun p => b^2*‖parameterNoiseCLM p.2‖^2)
      (hgsq.add (hcross.const_mul (2*b))) (hzsq.const_mul (b^2)),
    integral_add (f := fun p : A × IPLA.State N dθ dx => ‖g p.1‖ ^ 2)
      (g := fun p => 2*b*⟪g p.1, parameterNoiseCLM p.2⟫) hgsq (hcross.const_mul (2*b))]
  simp only [integral_const_mul, hzero, mul_zero, add_zero]
  have hfst := integral_fun_fst (μ := μ) (ν := stdGaussian (IPLA.State N dθ dx))
    (fun x => ‖g x‖ ^ 2)
  have hsnd := integral_fun_snd (μ := μ) (ν := stdGaussian (IPLA.State N dθ dx))
    (fun z => ‖parameterNoiseCLM z‖ ^ 2)
  simpa only [probReal_univ, one_smul, integral_parameterNoise_sq_stdGaussian] using
    congrArg₂ (fun x y : ℝ => x + b^2*y) hfst hsnd

end ProximalLangevin
