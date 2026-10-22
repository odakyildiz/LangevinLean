import UnadjustedLangevin.LSI.GaussianEntropy
import UnadjustedLangevin.GaussianProposalPairDensity
import UnadjustedLangevin.LSI.GaussianTimeDerivative
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option linter.style.header false

/-! # The Gaussian component flux and spatial integration by parts

The frozen-drift Gaussian time derivative is the divergence of a concrete
flux. The flux differentiates only the Gaussian kernel; it does not require
second derivatives of the potential. Global bounded entropy tests will be
admitted using square integrability of the Gaussian noise and the actual
relative score.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ULA.LSI
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The spatial flux whose divergence is the frozen Gaussian time derivative.
Its integral over the mixing law is `∇p + p E[∇U(X) | Y]`. -/
def frozenGaussianFlux (U : E → ℝ) (t : ℝ) (x y : E) : E :=
  realGaussianKernel (1 / (4 * t)) (x - t • gradient U x) y •
    (gradient U x - (1 / (2 * t)) • (y - (x - t • gradient U x)))

/-- The flux coordinate has an explicit directional derivative. The
potential gradient at the frozen initial state is constant in this spatial
derivative. -/
theorem fderiv_frozenGaussianFlux_coord (U : E → ℝ) (t : ℝ) (x y v : E) :
    fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t x y) v) y v =
      realGaussianKernel (1 / (4 * t)) (x - t • gradient U x) y *
        ((inner ℝ (y - (x - t • gradient U x)) v) ^ 2 / (4 * t ^ 2) -
          (inner ℝ (y - (x - t • gradient U x)) v) * (inner ℝ (gradient U x) v) /
            (2 * t) - ‖v‖ ^ 2 / (2 * t)) := by
  let c := x - t • gradient U x
  have hlin := (hasFDerivAt_const (𝕜 := ℝ) (gradient U x) y).sub
    (((hasFDerivAt_id (𝕜 := ℝ) y).sub_const c).const_smul (1 / (2 * t)))
  have hi := hlin.inner ℝ (hasFDerivAt_const (𝕜 := ℝ) v y)
  have hd := (hasFDerivAt_realGaussianKernel (1 / (4 * t)) c y).mul hi
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, id_eq] at hd
  have heq : (fun y ↦ inner ℝ (frozenGaussianFlux U t x y) v) =
      fun y ↦ realGaussianKernel (1 / (4 * t)) c y *
        inner ℝ (gradient U x - (1 / (2 * t)) • (y - c)) v := by
    funext y
    simp only [frozenGaussianFlux, real_inner_smul_left, c]
  rw [heq]
  change (fderiv ℝ (realGaussianKernel (1 / (4 * t)) c *
    (fun y ↦ inner ℝ (gradient U x - (1 / (2 * t)) • (y - c)) v)) y) v = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul,
    realGaussianKernelDeriv, inner_sub_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, id_eq, c,
    ContinuousLinearMap.prod_apply, fderivInnerCLM_apply, inner_zero_right,
    zero_add, Prod.fst, Prod.snd, zero_sub, inner_neg_left]
  ring

/-- The Gaussian flux divergence is the explicit time-derivative coefficient.
Summing over an orthonormal basis removes all coordinate dependence. -/
theorem sum_fderiv_frozenGaussianFlux (U : E → ℝ) (t : ℝ) (ht : t ≠ 0) (x y : E) :
    (∑ i : Fin (Module.finrank ℝ E),
      fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t x y)
        (stdOrthonormalBasis ℝ E i)) y (stdOrthonormalBasis ℝ E i)) =
      realGaussianKernel (1 / (4 * t)) (x - t • gradient U x) y *
        (-(Module.finrank ℝ E : ℝ) / (2 * t) +
          ‖y - x‖ ^ 2 / (4 * t ^ 2) - ‖gradient U x‖ ^ 2 / 4) := by
  let b := stdOrthonormalBasis ℝ E
  let r := y - (x - t • gradient U x)
  have hsq : (∑ i, (inner ℝ r (b i)) ^ 2) = ‖r‖ ^ 2 := b.sum_sq_inner_left r
  have hcross : (∑ i, inner ℝ r (b i) * inner ℝ (gradient U x) (b i)) =
      inner ℝ r (gradient U x) := by
    simpa only [real_inner_comm] using b.sum_inner_mul_inner r (gradient U x)
  have hres : r = y - x + t • gradient U x := by dsimp [r]; abel
  have hnorm := norm_add_sq_real (y - x) (t • gradient U x)
  simp only [real_inner_smul_left, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs] at hnorm
  simp_rw [fderiv_frozenGaussianFlux_coord]
  change (∑ i, realGaussianKernel (1 / (4 * t)) (x - t • gradient U x) y *
      ((inner ℝ r (b i)) ^ 2 / (4 * t ^ 2) -
        inner ℝ r (b i) * inner ℝ (gradient U x) (b i) / (2 * t) -
        ‖b i‖ ^ 2 / (2 * t))) = _
  simp_rw [b.orthonormal.1, one_pow]
  rw [← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, hsq, hcross,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hres, hnorm, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp
  ring

/-- The frozen initial/output pair has the displayed real Gaussian density.
This identity transfers square integrability from independent noise to the
Lebesgue pair integrals used in the weak equation. -/
theorem frozenGaussianJointLaw_eq_density (U : E → ℝ) (μ : Measure E)
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U)) (t : ℝ) (ht : 0 < t) :
    (μ.prod (stdGaussian E)).map (fun z : E × E ↦
      (z.1, ULA.malaProposal U t z.1 z.2)) =
      (μ.prod volume).withDensity (fun z : E × E ↦ ENNReal.ofReal
        (realGaussianKernel (1 / (4 * t)) (z.1 - t • gradient U z.1) z.2)) := by
  change (μ.prod (stdGaussian E)).map (fun z : E × E ↦
    (z.1, z.1 - t • gradient U z.1 + Real.sqrt (2 * t) • z.2)) = _
  rw [ULA.gaussian_proposal_pair_density μ (fun x ↦ x - t • gradient U x)
    (measurable_id.sub (hLip.continuous.measurable.const_smul t)) t ht]
  congr 1
  funext z
  unfold ULA.gaussianProposalDensity ULA.gaussianProposalNormalizer realGaussianKernel
  congr 2
  congr 1
  ring

/-- A finite-energy test gradient is admissible against every coordinate of
the actual Gaussian flux. Both square-integrable factors are constructed on
the independent initial/noise law and then transported to the pair density. -/
theorem frozenGaussianFlux_mul_integrable (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t)
    (φ : E → ℝ) (hφ : Continuous φ)
    (hφLp : MemLp φ 2 (interpolationLaw U μ t)) (v : E) :
    Integrable (fun z : E × E ↦ inner ℝ (frozenGaussianFlux U t z.1 z.2) v *
      φ z.2) (μ.prod volume) := by
  let P := μ.prod (stdGaussian E)
  let T : E × E → E × E := fun z ↦ (z.1, ULA.malaProposal U t z.1 z.2)
  let F : E × E → ℝ := fun z ↦
    inner ℝ (gradient U z.1 - (1 / (2 * t)) •
      (z.2 - (z.1 - t • gradient U z.1))) v * φ z.2
  have hY := ULA.malaProposal_measurable U t L hLip
  have hT : Measurable T := measurable_fst.prodMk hY
  have hF : AEStronglyMeasurable F (P.map T) := by
    have hg := hLip.continuous
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hnoise : MemLp (fun z : E ↦ z) 2 (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)
  have hflux : MemLp (fun z : E × E ↦ inner ℝ
      (gradient U z.1 - (1 / (2 * t)) •
        (ULA.malaProposal U t z.1 z.2 - (z.1 - t • gradient U z.1))) v) 2 P := by
    have hm := (hgrad.comp_fst (stdGaussian E)).sub
      ((hnoise.comp_snd μ).const_smul ((1 / (2 * t)) * Real.sqrt (2 * t)))
    have hv := hm.inner_const (𝕜 := ℝ) v
    simpa only [ULA.malaProposal, add_sub_cancel_left, smul_smul, Pi.sub_apply,
      Pi.smul_apply, mul_comm] using hv
  have htest : MemLp (fun z : E × E ↦ φ
      (ULA.malaProposal U t z.1 z.2)) 2 P := by
    exact (memLp_map_measure_iff hφLp.aestronglyMeasurable hY.aemeasurable).mp hφLp
  have hprod : MemLp (fun z : E × E ↦
      inner ℝ (gradient U z.1 - (1 / (2 * t)) •
        (ULA.malaProposal U t z.1 z.2 - (z.1 - t • gradient U z.1))) v *
        φ (ULA.malaProposal U t z.1 z.2)) 1 P := hflux.mul htest
  have hint : Integrable F (P.map T) :=
    (integrable_map_measure hF hT.aemeasurable).mpr (hprod.integrable (by norm_num))
  change Integrable F ((μ.prod (stdGaussian E)).map T) at hint
  rw [frozenGaussianJointLaw_eq_density U μ L hLip t ht] at hint
  have hqmeas : Measurable (fun z : E × E ↦ ENNReal.ofReal
      (realGaussianKernel (1 / (4 * t)) (z.1 - t • gradient U z.1) z.2)) := by
    unfold realGaussianKernel
    have hg := hLip.continuous.measurable
    fun_prop
  have hqnonneg (z : E × E) : 0 ≤
      realGaussianKernel (1 / (4 * t)) (z.1 - t • gradient U z.1) z.2 :=
    mul_nonneg (ULA.radialGaussianNormalizer_pos _ (by positivity)).le (Real.exp_nonneg _)
  have hw := (integrable_withDensity_iff_integrable_smul' hqmeas
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hint
  simpa only [ENNReal.toReal_ofReal (hqnonneg _), smul_eq_mul, F,
    frozenGaussianFlux, real_inner_smul_left, mul_assoc] using hw

/-- Every C1 test with square-integrable gradient is admissible against the
Gaussian flux in the weak equation. -/
theorem frozenGaussianFlux_test_gradient_integrable (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hψgrad : MemLp (gradient ψ) 2 (interpolationLaw U μ t)) (v : E) :
    Integrable (fun z : E × E ↦ inner ℝ (frozenGaussianFlux U t z.1 z.2) v *
      fderiv ℝ ψ z.2 v) (μ.prod volume) := by
  apply frozenGaussianFlux_mul_integrable U μ L hLip hgrad t ht
    (fun y ↦ fderiv ℝ ψ y v)
    ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const) _ v
  simpa only [inner_gradient_left] using hψgrad.inner_const (𝕜 := ℝ) v

/-- Bounded continuous tests satisfy the flux/test integrability premise of
global integration by parts. -/
theorem frozenGaussianFlux_bounded_test_integrable (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t)
    (ψ : E → ℝ) (hψ : Continuous ψ) (M : ℝ) (hM : ∀ y, ‖ψ y‖ ≤ M) (v : E) :
    Integrable (fun z : E × E ↦ inner ℝ (frozenGaussianFlux U t z.1 z.2) v *
      ψ z.2) (μ.prod volume) := by
  letI := interpolationLaw_isProbability U μ L hLip t
  exact frozenGaussianFlux_mul_integrable U μ L hLip hgrad t ht ψ hψ
    (MemLp.of_bound hψ.aestronglyMeasurable M (ae_of_all _ hM)) v

/-- The divergence calculation matches the actual component time derivative. -/
theorem frozenGaussianKernelDot_eq_sum_fderiv_flux (U : E → ℝ) (t : ℝ)
    (ht : 0 < t) (x y : E) :
    frozenGaussianKernelDot U t x y =
      ∑ i : Fin (Module.finrank ℝ E),
        fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t x y)
          (stdOrthonormalBasis ℝ E i)) y (stdOrthonormalBasis ℝ E i) := by
  rw [sum_fderiv_frozenGaussianFlux U t ht.ne' x y]
  unfold frozenGaussianKernelDot
  rw [frozenGaussianKernel_eq_realGaussianKernel]

/-- Each unit coordinate of the flux derivative has an integrable Gaussian
quadratic envelope. No fourth moment of the initial gradient is needed. -/
theorem norm_fderiv_frozenGaussianFlux_coord_le_energy (U : E → ℝ)
    (t : ℝ) (ht : 0 < t) (x y v : E) (hv : ‖v‖ = 1) :
    ‖fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t x y) v) y v‖ ≤
      (1 / (4 * t ^ 2) + 1 / (2 * t)) * frozenGaussianEnergy U t x y := by
  let r := y - (x - t • gradient U x)
  have hi : |inner ℝ r v| ≤ ‖r‖ := by
    simpa only [Real.norm_eq_abs, hv, mul_one] using norm_inner_le_norm (𝕜 := ℝ) r v
  have hg : |inner ℝ (gradient U x) v| ≤ ‖gradient U x‖ := by
    simpa only [Real.norm_eq_abs, hv, mul_one] using
      norm_inner_le_norm (𝕜 := ℝ) (gradient U x) v
  have hsq : (inner ℝ r v) ^ 2 ≤ ‖r‖ ^ 2 := by
    nlinarith [sq_abs (inner ℝ r v), sq_le_sq₀ (abs_nonneg (inner ℝ r v))
      (norm_nonneg r) |>.mpr hi]
  have hcross : |inner ℝ r v * inner ℝ (gradient U x) v| ≤
      ‖r‖ ^ 2 + ‖gradient U x‖ ^ 2 := by
    rw [abs_mul]
    have h := mul_le_mul hi hg (abs_nonneg _) (norm_nonneg _)
    nlinarith [sq_nonneg (‖r‖ - ‖gradient U x‖)]
  have hA := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 4 * t ^ 2)
  have hB : |inner ℝ r v * inner ℝ (gradient U x) v / (2 * t)| ≤
      (‖r‖ ^ 2 + ‖gradient U x‖ ^ 2) / (2 * t) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2 * t)]
    exact div_le_div_of_nonneg_right hcross (by positivity)
  have hbound : |(inner ℝ r v) ^ 2 / (4 * t ^ 2) -
      inner ℝ r v * inner ℝ (gradient U x) v / (2 * t) - 1 / (2 * t)| ≤
      (1 / (4 * t ^ 2) + 1 / (2 * t)) *
        (1 + ‖gradient U x‖ ^ 2 + ‖r‖ ^ 2) := by
    have hnonneg : 0 ≤ (inner ℝ r v) ^ 2 / (4 * t ^ 2) := by positivity
    have hC : 0 ≤ 1 / (2 * t) := by positivity
    have htriangle : |(inner ℝ r v) ^ 2 / (4 * t ^ 2) -
        inner ℝ r v * inner ℝ (gradient U x) v / (2 * t) - 1 / (2 * t)| ≤
        ‖r‖ ^ 2 / (4 * t ^ 2) +
          (‖r‖ ^ 2 + ‖gradient U x‖ ^ 2) / (2 * t) + 1 / (2 * t) := by
      have hl := neg_abs_le (inner ℝ r v * inner ℝ (gradient U x) v / (2 * t))
      have hu := le_abs_self (inner ℝ r v * inner ℝ (gradient U x) v / (2 * t))
      apply abs_le.mpr
      constructor <;> nlinarith
    apply htriangle.trans
    have hd : 0 ≤ (1 + ‖gradient U x‖ ^ 2) / (4 * t ^ 2) := by positivity
    simp only [div_eq_mul_inv] at *
    nlinarith
  have hK : 0 ≤ realGaussianKernel (1 / (4 * t)) (x - t • gradient U x) y :=
    mul_nonneg (ULA.radialGaussianNormalizer_pos _ (by positivity)).le (Real.exp_nonneg _)
  rw [fderiv_frozenGaussianFlux_coord, Real.norm_eq_abs, abs_mul, abs_of_nonneg hK,
    hv, one_pow]
  have h := mul_le_mul_of_nonneg_left hbound hK
  rw [frozenGaussianEnergy, frozenGaussianKernel_eq_realGaussianKernel]
  dsimp only [r] at h
  nlinarith

/-- Coordinate flux derivatives are jointly integrable under the original
finite-gradient-energy assumption. -/
theorem integrable_fderiv_frozenGaussianFlux_coord (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) (v : E) (hv : ‖v‖ = 1) :
    Integrable (fun z : E × E ↦
      fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t z.1 y) v) z.2 v)
      (μ.prod volume) := by
  have hE := integrable_frozenGaussianEnergy U μ L hLip
    (hgrad.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) t ht
  apply (hE.const_mul (1 / (4 * t ^ 2) + 1 / (2 * t))).mono'
  · have heq : (fun z : E × E ↦
        fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t z.1 y) v) z.2 v) =
        fun z : E × E ↦ realGaussianKernel (1 / (4 * t))
          (z.1 - t • gradient U z.1) z.2 *
            ((inner ℝ (z.2 - (z.1 - t • gradient U z.1)) v) ^ 2 / (4 * t ^ 2) -
              (inner ℝ (z.2 - (z.1 - t • gradient U z.1)) v) *
                (inner ℝ (gradient U z.1) v) / (2 * t) - ‖v‖ ^ 2 / (2 * t)) := by
      funext z
      exact fderiv_frozenGaussianFlux_coord U t z.1 z.2 v
    rw [heq]
    have hg := hLip.continuous
    unfold realGaussianKernel
    fun_prop
  · exact ae_of_all _ fun z ↦
      norm_fderiv_frozenGaussianFlux_coord_le_energy U t ht z.1 z.2 v hv

/-- Global spatial integration by parts for one coordinate of the actual
Gaussian flux. Boundedness controls the boundary product; square integrability
of the test gradient controls the flux-gradient pairing. -/
theorem frozenGaussianFlux_coord_weak_identity (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 1 ψ) (M : ℝ) (hM : ∀ y, ‖ψ y‖ ≤ M)
    (hψgrad : MemLp (gradient ψ) 2 (interpolationLaw U μ t)) (v : E) (hv : ‖v‖ = 1) :
    (∫ z : E × E,
      fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t z.1 y) v) z.2 v * ψ z.2
      ∂μ.prod volume) =
      -(∫ z : E × E, inner ℝ (frozenGaussianFlux U t z.1 z.2) v *
        fderiv ℝ ψ z.2 v ∂μ.prod volume) := by
  have hD := integrable_fderiv_frozenGaussianFlux_coord U μ L hLip hgrad t ht v hv
  have hDf := hD.mul_bdd (hψ.continuous.comp continuous_snd).aestronglyMeasurable
    (ae_of_all _ fun z : E × E ↦ hM z.2)
  change Integrable (fun z : E × E ↦
    fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t z.1 y) v) z.2 v * ψ z.2)
    (μ.prod volume) at hDf
  have hFg := frozenGaussianFlux_test_gradient_integrable U μ L hLip hgrad t ht
    ψ hψ hψgrad v
  have hFf := frozenGaussianFlux_bounded_test_integrable U μ L hLip hgrad t ht
    ψ hψ.continuous M hM v
  have heq : ∀ᵐ x ∂μ,
      (∫ y, fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t x y) v) y v * ψ y) =
      -(∫ y, inner ℝ (frozenGaussianFlux U t x y) v * fderiv ℝ ψ y v) := by
    filter_upwards [hDf.prod_right_ae, hFg.prod_right_ae, hFf.prod_right_ae]
      with x hxD hxG hxF
    have hf : Differentiable ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t x y) v) := by
      have hq : Differentiable ℝ (realGaussianKernel (1 / (4 * t))
          (x - t • gradient U x)) := fun y ↦
        (hasFDerivAt_realGaussianKernel _ _ y).differentiableAt
      have hl : Differentiable ℝ (fun y : E ↦ gradient U x -
          (1 / (2 * t)) • (y - (x - t • gradient U x))) := by fun_prop
      exact (hq.smul hl).inner ℝ (differentiable_const v)
    have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := fun y ↦ inner ℝ (frozenGaussianFlux U t x y) v) (g := ψ) (v := v) hxD hxG hxF
      (fun y _ ↦ hf y) (fun y _ ↦ hψ.differentiable (by norm_num) y)
    linarith
  rw [integral_prod _ hDf, integral_prod _ hFg, ← integral_neg]
  exact integral_congr_ae heq

/-- The actual Gaussian interpolation satisfies its weak equation for every
bounded C1 test with finite gradient energy. The equation is proved from the
component density and global integration by parts; it is not an assumption
about an interpolation path. -/
theorem interpolationLebesgueDensity_weak_identity (U : E → ℝ) (μ : Measure E)
    [IsProbabilityMeasure μ] (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 1 ψ) (M : ℝ) (hM : ∀ y, ‖ψ y‖ ≤ M)
    (hψgrad : MemLp (gradient ψ) 2 (interpolationLaw U μ t)) :
    (∫ y, interpolationLebesgueDensityTimeDerivative U μ t y * ψ y) =
      -(∫ z : E × E, inner ℝ (frozenGaussianFlux U t z.1 z.2)
        (gradient ψ z.2) ∂μ.prod volume) := by
  let b := stdOrthonormalBasis ℝ E
  let A : Fin (Module.finrank ℝ E) → E × E → ℝ := fun i z ↦
    fderiv ℝ (fun y ↦ inner ℝ (frozenGaussianFlux U t z.1 y) (b i)) z.2 (b i) * ψ z.2
  let B : Fin (Module.finrank ℝ E) → E × E → ℝ := fun i z ↦
    inner ℝ (frozenGaussianFlux U t z.1 z.2) (b i) * fderiv ℝ ψ z.2 (b i)
  have hA (i : Fin (Module.finrank ℝ E)) : Integrable (A i) (μ.prod volume) := by
    have h := (integrable_fderiv_frozenGaussianFlux_coord U μ L hLip hgrad t ht
      (b i) (b.orthonormal.1 i)).mul_bdd
      (hψ.continuous.comp continuous_snd).aestronglyMeasurable
      (ae_of_all _ fun z : E × E ↦ hM z.2)
    exact h
  have hB (i : Fin (Module.finrank ℝ E)) : Integrable (B i) (μ.prod volume) :=
    frozenGaussianFlux_test_gradient_integrable U μ L hLip hgrad t ht ψ hψ hψgrad (b i)
  have hEq (i : Fin (Module.finrank ℝ E)) :
      (∫ z, A i z ∂μ.prod volume) = -(∫ z, B i z ∂μ.prod volume) :=
    frozenGaussianFlux_coord_weak_identity U μ L hLip hgrad t ht ψ hψ M hM hψgrad
      (b i) (b.orthonormal.1 i)
  have hDot := (integrable_frozenGaussianKernelDot U μ L hLip
    (hgrad.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) t ht).mul_bdd
    (hψ.continuous.comp continuous_snd).aestronglyMeasurable
    (ae_of_all _ fun z : E × E ↦ hM z.2)
  change Integrable (fun z : E × E ↦ frozenGaussianKernelDot U t z.1 z.2 * ψ z.2)
    (μ.prod volume) at hDot
  have hsumA (z : E × E) : frozenGaussianKernelDot U t z.1 z.2 * ψ z.2 = ∑ i, A i z := by
    rw [frozenGaussianKernelDot_eq_sum_fderiv_flux U t ht z.1 z.2, Finset.sum_mul]
  have hsumB (z : E × E) :
      inner ℝ (frozenGaussianFlux U t z.1 z.2) (gradient ψ z.2) = ∑ i, B i z := by
    rw [← b.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [← real_inner_comm (b i) (gradient ψ z.2), inner_gradient_left]
  calc
    _ = ∫ z : E × E, frozenGaussianKernelDot U t z.1 z.2 * ψ z.2 ∂μ.prod volume := by
      unfold interpolationLebesgueDensityTimeDerivative
      simp_rw [← integral_mul_const]
      rw [← integral_integral_swap hDot, ← integral_prod _ hDot]
    _ = ∫ z, ∑ i, A i z ∂μ.prod volume := by simp_rw [hsumA]
    _ = ∑ i, ∫ z, A i z ∂μ.prod volume :=
      integral_finsetSum _ (fun i _ ↦ hA i)
    _ = -(∑ i, ∫ z, B i z ∂μ.prod volume) := by simp_rw [hEq]; rw [Finset.sum_neg_distrib]
    _ = -(∫ z, ∑ i, B i z ∂μ.prod volume) := by
      rw [integral_finsetSum _ (fun i _ ↦ hB i)]
    _ = _ := by simp_rw [← hsumB]

end ULA.LSI
