import PBGSO.HigherOrderMethod
import KineticLangevin.VectorSegmentEquations

/-!
# Actual jointly Gaussian innovations for HOL-MYPGD

The three response kernels are the implementation's `μ13, μ23, μ33`,
multiplied by `sqrt(2α)`. A fourth constant kernel couples them to the actual
Brownian increment on the same interval. Their joint law is constructed from
the canonical Brownian source and has the genuine integral Gram covariance.
No supplied covariance or noise-matching bound is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace PBGSO.Methods
open KineticLangevin KineticLangevin.BrownianConvolution

/-- The three implemented Gaussian response kernels and the coupled
unfiltered Brownian kernel, in the order `(x,u,v,B)`. -/
def holNoiseKernels (α γ : ℝ) : Fin 4 → ℝ → ℝ := fun i t =>
  Real.sqrt (2 * α) *
    ![(holCoefficients α γ t).μ13, (holCoefficients α γ t).μ23,
      (holCoefficients α γ t).μ33, 1] i

theorem continuous_holNoiseKernels (α γ : ℝ) (i : Fin 4) :
    Continuous (holNoiseKernels α γ i) := by
  fin_cases i
  · change Continuous (fun t => Real.sqrt (2 * α) * (holCoefficients α γ t).μ13)
    unfold holCoefficients
    fun_prop
  · change Continuous (fun t => Real.sqrt (2 * α) * (holCoefficients α γ t).μ23)
    unfold holCoefficients
    fun_prop
  · change Continuous (fun t => Real.sqrt (2 * α) * (holCoefficients α γ t).μ33)
    unfold holCoefficients
    fun_prop
  · change Continuous (fun _ : ℝ => Real.sqrt (2 * α) * 1)
    exact continuous_const

/-- The four responses on one actual canonical Brownian segment. -/
def holScalarNoise (α γ : ℝ) (a h : ℝ≥0) (i : Fin 4) : Lp ℝ 2 probability :=
  segmentConvolutionLp (holNoiseKernels α γ i) (continuous_holNoiseKernels α γ i) a h

/-- The constructed responses are jointly Gaussian with their actual
Gram covariance. This includes their coupling to the Brownian increment. -/
theorem holScalarNoise_jointLaw (α γ : ℝ) (a h : ℝ≥0) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => holScalarNoise α γ a h i ω))
      (kernelGaussian (holNoiseKernels α γ) h) probability :=
  segmentConvolutionLp_jointLaw (holNoiseKernels α γ)
    (continuous_holNoiseKernels α γ) a h

/-- Every covariance entry is a verified integral of the response kernels. -/
theorem holScalarNoise_covariance (α γ : ℝ) (a h : ℝ≥0) (i j : Fin 4) :
    cov[holScalarNoise α γ a h i, holScalarNoise α γ a h j; probability] =
      ∫ s in 0..(h : ℝ), holNoiseKernels α γ i s * holNoiseKernels α γ j s :=
  segmentConvolutionLp_covariance _ _ _ _ _ _

/-- The Brownian isometry computes the exact second moment of a response. -/
theorem segmentConvolution_norm_sq (k : ℝ → ℝ) (hk : Continuous k) (a h : ℝ≥0) :
    ‖segmentConvolutionLp k hk a h‖ ^ 2 = ∫ s in 0..(h : ℝ), k s ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, segmentConvolutionLp,
    (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).inner_map_map,
    segmentKernelLp_inner]
  simp only [pow_two]

/-- Kernel subtraction is subtraction of the actual coupled responses. -/
theorem segmentConvolution_sub (k l : ℝ → ℝ) (hk : Continuous k) (hl : Continuous l)
    (a h : ℝ≥0) :
    segmentConvolutionLp k hk a h - segmentConvolutionLp l hl a h =
      segmentConvolutionLp (fun s => k s - l s) (hk.sub hl) a h := by
  unfold segmentConvolutionLp
  rw [← map_sub]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (segmentKernelLp k hk a h) (segmentKernelLp l hl a h),
    segmentKernelLp_coe k hk a h, segmentKernelLp_coe l hl a h,
    segmentKernelLp_coe (fun s => k s - l s) (hk.sub hl) a h] with r hs hk hl hkl
  rw [hs, Pi.sub_apply, hk, hl, hkl]
  by_cases hr : r ∈ Ioc (a : ℝ) ((a : ℝ) + (h : ℝ)) <;> simp [hr]

/-- Scaling a deterministic response scales its coupled Wiener integral. -/
theorem segmentConvolution_smul (k : ℝ → ℝ) (hk : Continuous k) (c : ℝ)
    (a h : ℝ≥0) :
    segmentConvolutionLp (fun s => c * k s) (continuous_const.mul hk) a h =
      c • segmentConvolutionLp k hk a h := by
  unfold segmentConvolutionLp
  rw [← map_smul]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul c (segmentKernelLp k hk a h),
    segmentKernelLp_coe k hk a h,
    segmentKernelLp_coe (fun s => c * k s) (continuous_const.mul hk) a h]
    with r hs hk hck
  rw [hs, Pi.smul_apply, hk, hck]
  by_cases hr : r ∈ Ioc (a : ℝ) ((a : ℝ) + (h : ℝ)) <;> simp [hr]

/-- The fourth innovation is precisely the scaled actual Brownian
increment; it is not merely an independently chosen Gaussian with the
same marginal variance. -/
theorem holScalarNoise_brownian (α γ : ℝ) (a h : ℝ≥0) :
    holScalarNoise α γ a h 3 = Real.sqrt (2 * α) • segmentBrownianLp a h := by
  unfold holScalarNoise
  change segmentConvolutionLp (fun _ => Real.sqrt (2 * α) * (1 : ℝ)) _ a h = _
  simpa only [segmentConvolutionLp_one] using
    segmentConvolution_smul (fun _ => 1) continuous_const (Real.sqrt (2 * α)) a h

/-- A bounded kernel gives a derived `sqrt(h)` response norm bound. -/
theorem segmentConvolution_norm_le (k : ℝ → ℝ) (hk : Continuous k) (a h : ℝ≥0)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ∈ Icc 0 (h : ℝ), |k s| ≤ C) :
    ‖segmentConvolutionLp k hk a h‖ ≤ C * Real.sqrt (h : ℝ) := by
  have hi : (∫ s in 0..(h : ℝ), k s ^ 2) ≤ C ^ 2 * (h : ℝ) := by
    calc
      _ ≤ ∫ _s in 0..(h : ℝ), C ^ 2 := by
        apply intervalIntegral.integral_mono_on h.coe_nonneg
          ((hk.pow 2).intervalIntegrable _ _) intervalIntegrable_const
        intro s hs
        have hb := hbound s hs
        change k s ^ 2 ≤ C ^ 2
        exact (sq_abs (k s)) ▸ ((sq_le_sq₀ (abs_nonneg (k s)) hC).mpr hb)
      _ = _ := by simp [mul_comm]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt h.coe_nonneg, segmentConvolution_norm_sq]
  exact hi

/-- The exact spatial dimension factor follows from the real coordinate
second moments and the product source's marginal measures. -/
theorem spatialLift_norm_sq (ι : Type*) [Fintype ι] [DecidableEq ι]
    (X : Lp ℝ 2 probability) :
    ‖spatialLift ι X‖ ^ 2 = (Fintype.card ι : ℝ) * ‖X‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hs : (fun ω => inner ℝ (spatialLift ι X ω) (spatialLift ι X ω)) =ᵐ[
      ULA.CanonicalBrownian.vectorProbability ι]
      (fun ω => ∑ i : ι, X (ω i) ^ 2) := by
    filter_upwards [spatialLift_coe ι X] with ω hω
    rw [hω]
    rw [real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
  rw [integral_congr_ae hs]
  have hi (i : ι) : Integrable (fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      X (ω i) ^ 2) (ULA.CanonicalBrownian.vectorProbability ι) := by
    exact (measurePreserving_eval_infinitePi (fun _ : ι => probability) i).integrable_comp_of_integrable
      (Lp.memLp X).integrable_sq
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have he (i : ι) : (∫ ω : ULA.CanonicalBrownian.VectorSample ι, X (ω i) ^ 2
      ∂ULA.CanonicalBrownian.vectorProbability ι) = ‖X‖ ^ 2 := by
    have hp : MeasurePreserving (fun ω : ULA.CanonicalBrownian.VectorSample ι => ω i)
        (ULA.CanonicalBrownian.vectorProbability ι) probability :=
      measurePreserving_eval_infinitePi (fun _ : ι => probability) i
    have hm : AEStronglyMeasurable (fun x => X x ^ 2)
        ((ULA.CanonicalBrownian.vectorProbability ι).map (fun ω => ω i)) := by
      simpa only [hp.map_eq] using (Lp.memLp X).integrable_sq.aestronglyMeasurable
    have hint := integral_map hp.measurable.aemeasurable hm
    rw [hp.map_eq] at hint
    rw [← hint]
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with ω
    simp [pow_two]
  simp_rw [he]
  simp

/-- Vector response norm from its scalar response, with exact `sqrt(d)`. -/
theorem spatialLift_norm (ι : Type*) [Fintype ι] [DecidableEq ι]
    (X : Lp ℝ 2 probability) :
    ‖spatialLift ι X‖ = Real.sqrt (Fintype.card ι : ℝ) * ‖X‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), spatialLift_norm_sq]

/-- Actual vector innovations, with independent spatial Brownian sources. -/
def holVectorNoise (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α γ : ℝ) (a h : ℝ≥0) (i : Fin 4) :
    Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) :=
  spatialLift ι (holScalarNoise α γ a h i)

/-- The reference increment used in the vector noise budget is the actual
scaled coordinatewise Brownian increment on the same time segment. -/
theorem holVectorNoise_brownian (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α γ : ℝ) (a h : ℝ≥0) :
    holVectorNoise ι α γ a h 3 =
      Real.sqrt (2 * α) • vectorBrownianIncrementLp ι a h := by
  unfold holVectorNoise vectorBrownianIncrementLp
  rw [holScalarNoise_brownian, map_smul]

/-- Independent full Gaussian blocks over all iterations and all spatial
coordinates. The four coordinates inside each block retain their proved
correlations. -/
theorem holNoiseArray_independent (ι : Type*) (α γ : ℝ) (h : ℝ≥0) :
    iIndepFun (fun p : (n : ℕ) × ι => fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      vectorGridBlock ι (holNoiseKernels α γ) (continuous_holNoiseKernels α γ)
        h p.fst ω p.snd) (ULA.CanonicalBrownian.vectorProbability ι) :=
  vectorGridBlock_array_independent ι (holNoiseKernels α γ)
    (continuous_holNoiseKernels α γ) h

/-- The complete independent Brownian innovation array has exactly the
product of the verified four-coordinate Gaussian block laws. -/
theorem holNoiseArray_law (ι : Type*) (α γ : ℝ) (h : ℝ≥0) :
    HasLaw (fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      fun p : (n : ℕ) × ι =>
        vectorGridBlock ι (holNoiseKernels α γ) (continuous_holNoiseKernels α γ)
          h p.fst ω p.snd)
      (Measure.infinitePi (fun _ : (n : ℕ) × ι => kernelGaussian (holNoiseKernels α γ) h))
      (ULA.CanonicalBrownian.vectorProbability ι) :=
  vectorGridBlock_array_law ι (holNoiseKernels α γ)
    (continuous_holNoiseKernels α γ) h

end PBGSO.Methods
