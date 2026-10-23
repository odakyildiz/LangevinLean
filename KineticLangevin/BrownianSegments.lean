import KineticLangevin.BrownianConvolution
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence

/-!
# Brownian convolution innovations on disjoint intervals

Translation in deterministic L² time is an isometry. Translating the response
kernel to `(a,a+t]` constructs an innovation on that interval using the same
canonical Brownian source. Disjoint supports are orthogonal, hence the jointly
Gaussian innovations are independent.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace KineticLangevin.BrownianConvolution

/-- Translation of deterministic time kernels, as a real linear isometry. -/
def timeShift (a : ℝ) : TimeHilbert →ₗᵢ[ℝ] TimeHilbert :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun r : ℝ => r - a) (measurePreserving_sub_right volume a)

/-- A response kernel supported on the Brownian interval `(a,a+t]`. -/
def segmentKernelLp (k : ℝ → ℝ) (hk : Continuous k) (a t : ℝ≥0) : TimeHilbert :=
  timeShift a (timeKernelLp k hk t)

theorem segmentKernelLp_coe (k : ℝ → ℝ) (hk : Continuous k) (a t : ℝ≥0) :
    segmentKernelLp k hk a t =ᵐ[volume]
      (Ioc (a : ℝ) ((a : ℝ) + (t : ℝ))).indicator
        (fun r => k ((a : ℝ) + (t : ℝ) - r)) := by
  have hf := measurePreserving_sub_right (volume : Measure ℝ) (a : ℝ)
  have hcoe := Lp.coeFn_compMeasurePreserving (timeKernelLp k hk t) hf
  have hp := hf.quasiMeasurePreserving.ae_eq_comp (timeKernelLp_coe k hk t)
  filter_upwards [hcoe, hp] with r hr hp
  dsimp only [Function.comp_apply] at hr hp
  change segmentKernelLp k hk a t r = _
  rw [show segmentKernelLp k hk a t r = timeKernelLp k hk t (r - a) from hr, hp]
  by_cases hmem : r ∈ Ioc (a : ℝ) ((a : ℝ) + (t : ℝ))
  · have hmem' : r - (a : ℝ) ∈ Ioc 0 (t : ℝ) := by constructor <;> linarith [hmem.1, hmem.2]
    simp only [timeKernel, indicator_of_mem hmem, indicator_of_mem hmem']
    congr 1
    ring
  · have hmem' : r - (a : ℝ) ∉ Ioc 0 (t : ℝ) := by
      intro hh
      exact hmem ⟨by linarith [hh.1], by linarith [hh.2]⟩
    simp [timeKernel, hmem, hmem']

/-- Translation preserves every within-step covariance. -/
theorem segmentKernelLp_inner (k l : ℝ → ℝ) (hk : Continuous k) (hl : Continuous l)
    (a t : ℝ≥0) :
    inner ℝ (segmentKernelLp k hk a t) (segmentKernelLp l hl a t) =
      ∫ s in 0..(t : ℝ), k s * l s := by
  rw [segmentKernelLp, segmentKernelLp, (timeShift (a : ℝ)).inner_map_map,
    timeKernelLp_inner]

/-- Disjoint Brownian time supports are orthogonal in deterministic L². -/
theorem segmentKernelLp_inner_zero (k l : ℝ → ℝ) (hk : Continuous k) (hl : Continuous l)
    (a t b u : ℝ≥0) (hab : a + t ≤ b) :
    inner ℝ (segmentKernelLp k hk a t) (segmentKernelLp l hl b u) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [segmentKernelLp_coe k hk a t, segmentKernelLp_coe l hl b u] with r hr hs
  rw [hr, hs]
  by_cases hmem : r ∈ Ioc (a : ℝ) ((a : ℝ) + (t : ℝ))
  · have hnot : r ∉ Ioc (b : ℝ) ((b : ℝ) + (u : ℝ)) := by
      intro hh
      have hh' : (a : ℝ) + (t : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      linarith [hmem.2, hh.1]
    simp [hnot]
  · simp [hmem]

/-- A Wiener response to Brownian fluctuations on one specified time segment. -/
def segmentConvolutionLp (k : ℝ → ℝ) (hk : Continuous k) (a t : ℝ≥0) :
    Lp ℝ 2 probability :=
  ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis (segmentKernelLp k hk a t)

theorem segmentConvolutionLp_mean (k : ℝ → ℝ) (hk : Continuous k) (a t : ℝ≥0) :
    (∫ ω, segmentConvolutionLp k hk a t ω ∂probability) = 0 :=
  ULA.GaussianHilbert.isonormal_mean _ _

theorem segmentConvolutionLp_jointlyGaussian {ι : Type*} [Fintype ι]
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i)) (a t : ℝ≥0) :
    HasGaussianLaw (fun ω i => segmentConvolutionLp (kernels i) (hc i) a t ω) probability :=
  ULA.hasGaussianLaw_pi_of_linearMap_Lp probability
    ((ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).toLinearMap.comp
      (timeShift a).toLinearMap)
    (fun x => ULA.GaussianHilbert.isonormal_hasGaussianLaw _ _)
    (fun i => timeKernelLp (kernels i) (hc i) t)

theorem segmentConvolutionLp_covariance (k l : ℝ → ℝ) (hk : Continuous k)
    (hl : Continuous l) (a t : ℝ≥0) :
    cov[segmentConvolutionLp k hk a t, segmentConvolutionLp l hl a t; probability] =
      ∫ s in 0..(t : ℝ), k s * l s := by
  rw [segmentConvolutionLp, segmentConvolutionLp,
    ULA.GaussianHilbert.isonormal_covariance, segmentKernelLp_inner]

theorem segmentConvolutionLp_covariance_zero (k l : ℝ → ℝ) (hk : Continuous k)
    (hl : Continuous l) (a t b u : ℝ≥0) (hab : a + t ≤ b) :
    cov[segmentConvolutionLp k hk a t, segmentConvolutionLp l hl b u; probability] = 0 := by
  rw [segmentConvolutionLp, segmentConvolutionLp,
    ULA.GaussianHilbert.isonormal_covariance, segmentKernelLp_inner_zero k l hk hl a t b u hab]

theorem segmentConvolutionLp_jointLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i)) (a t : ℝ≥0) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => segmentConvolutionLp (kernels i) (hc i) a t ω))
      (kernelGaussian kernels t) probability := by
  let F : Sample → EuclideanSpace ℝ ι :=
    fun ω => WithLp.toLp 2 (fun i => segmentConvolutionLp (kernels i) (hc i) a t ω)
  have hFmem : MemLp F 2 probability :=
    MemLp.of_eval_piLp (fun i => Lp.memLp (segmentConvolutionLp (kernels i) (hc i) a t))
  have hg : HasGaussianLaw F probability :=
    HasGaussianLaw.map_of_measurable
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap
      (segmentConvolutionLp_jointlyGaussian kernels hc a t) (by fun_prop)
  refine ⟨hg.aemeasurable, ?_⟩
  letI : IsGaussian (probability.map F) := hg.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map hg.aemeasurable (by fun_prop)]
    simp only [id_eq]
    rw [kernelGaussian_mean]
    apply PiLp.ext
    intro i
    change (EuclideanSpace.proj i) (∫ ω, F ω ∂probability) = 0
    rw [← ContinuousLinearMap.integral_comp_comm _ (hFmem.integrable (by norm_num))]
    exact segmentConvolutionLp_mean _ _ _ _
  · apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    change covarianceBilin (probability.map F) x y =
      covarianceBilin (kernelGaussian kernels t) x y
    rw [covarianceBilin_apply_pi
      (fun i => Lp.memLp (segmentConvolutionLp (kernels i) (hc i) a t))]
    rw [show covarianceBilin (kernelGaussian kernels t) x y =
      dotProduct (x : ι → ℝ) ((gramCovariance kernels t).mulVec y) from
      covarianceBilin_multivariateGaussian (gramCovariance_posSemidef kernels hc t.coe_nonneg) x y]
    simp_rw [segmentConvolutionLp_covariance]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, gramCovariance]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring


/-- All kernel coordinates on one interval of a uniform Brownian time grid. -/
def gridConvolutionLp {ι : Type*} (kernels : ι → ℝ → ℝ)
    (hc : ∀ i, Continuous (kernels i)) (h : ℝ≥0) (n : ℕ) (i : ι) :
    Lp ℝ 2 probability :=
  segmentConvolutionLp (kernels i) (hc i) ((n : ℝ≥0) * h) h

set_option maxHeartbeats 1000000

/-- The entire family over every grid interval and kernel coordinate is Gaussian. -/
theorem gridConvolutionLp_isGaussianProcess {ι : Type*}
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i)) (h : ℝ≥0) :
    IsGaussianProcess (fun p : (n : ℕ) × ι => fun ω => gridConvolutionLp kernels hc h p.1 p.2 ω)
      probability :=
  ULA.isGaussianProcess_of_linearMap_Lp (Ω := Sample) (H := TimeHilbert)
    (Time := (n : ℕ) × ι) probability
    (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).toLinearMap
    (ULA.GaussianHilbert.isonormal_hasGaussianLaw ULA.CanonicalBrownian.basis)
    (fun p => segmentKernelLp (kernels p.2) (hc p.2) ((p.1 : ℝ≥0) * h) h)

/-- The jointly Gaussian blocks on different Brownian grid intervals are
independent; independence is derived from the actual disjoint time supports. -/
theorem gridConvolutionLp_independent {ι : Type*}
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i)) (h : ℝ≥0) :
    iIndepFun (fun n ω i => gridConvolutionLp kernels hc h n i ω) probability := by
  apply IsGaussianProcess.iIndepFun_of_covariance_eq_zero
    (X := fun n i ω => gridConvolutionLp kernels hc h n i ω)
    (gridConvolutionLp_isGaussianProcess kernels hc h)
    (fun n i => (Lp.aestronglyMeasurable _).aemeasurable)
  intro n m hnm i j
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have hnm' : (n : ℝ≥0) + 1 ≤ (m : ℝ≥0) := by exact_mod_cast Nat.succ_le_of_lt hlt
    have hseg : (n : ℝ≥0) * h + h ≤ (m : ℝ≥0) * h := by
      calc
        (n : ℝ≥0) * h + h = ((n : ℝ≥0) + 1) * h := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hnm' (show 0 ≤ h from zero_le)
    exact segmentConvolutionLp_covariance_zero _ _ _ _ _ _ _ _ hseg
  · have hmn' : (m : ℝ≥0) + 1 ≤ (n : ℝ≥0) := by exact_mod_cast Nat.succ_le_of_lt hgt
    have hseg : (m : ℝ≥0) * h + h ≤ (n : ℝ≥0) * h := by
      calc
        (m : ℝ≥0) * h + h = ((m : ℝ≥0) + 1) * h := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hmn' (show 0 ≤ h from zero_le)
    rw [covariance_comm]
    exact segmentConvolutionLp_covariance_zero _ _ _ _ _ _ _ _ hseg

/-- Packing the scalar responses into Euclidean blocks preserves time independence. -/
theorem gridConvolutionLp_euclidean_independent {ι : Type*} [Fintype ι]
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i)) (h : ℝ≥0) :
    iIndepFun (fun n ω => WithLp.toLp 2 (fun i => gridConvolutionLp kernels hc h n i ω))
      probability :=
  (gridConvolutionLp_independent kernels hc h).comp (fun _ => WithLp.toLp 2)
    (fun _ => WithLp.measurable_toLp 2 _)

/-- Every actual Brownian grid block has the same Gram-Gaussian law. -/
theorem gridConvolutionLp_jointLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i)) (h : ℝ≥0) (n : ℕ) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => gridConvolutionLp kernels hc h n i ω))
      (kernelGaussian kernels h) probability :=
  segmentConvolutionLp_jointLaw kernels hc _ _

end KineticLangevin.BrownianConvolution
