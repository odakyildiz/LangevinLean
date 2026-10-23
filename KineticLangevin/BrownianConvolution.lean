import KineticLangevin.Gaussian
import UnadjustedLangevin.CanonicalBrownian
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Brownian convolutions on the constructed Gaussian source

A continuous deterministic response kernel on `[0,t]` is square-integrable.
Applying the existing isonormal map to its time reversal constructs its Wiener
integral on the same source as `ULA.CanonicalBrownian.process`. Inner products
of kernels give the exact Brownian covariance, rather than a matching-law
hypothesis supplied to the numerical method.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace KineticLangevin.BrownianConvolution

abbrev TimeHilbert := ULA.CanonicalBrownian.TimeHilbert
abbrev Sample := ULA.CanonicalBrownian.Sample
abbrev probability := ULA.CanonicalBrownian.probability

/-- Reverse a deterministic response on its finite Brownian time interval. -/
def timeKernel (k : ℝ → ℝ) (t : ℝ≥0) : ℝ → ℝ :=
  (Ioc 0 (t : ℝ)).indicator (fun s => k ((t : ℝ) - s))

theorem timeKernel_memLp (k : ℝ → ℝ) (hk : Continuous k) (t : ℝ≥0) :
    MemLp (timeKernel k t) 2 (volume : Measure ℝ) := by
  apply (memLp_indicator_iff_restrict measurableSet_Ioc).mpr
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hk.comp (continuous_const.sub continuous_id)).continuousOn
  apply MemLp.of_bound (by fun_prop) C
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  exact ae_of_all _ fun s hs => hC s ⟨hs.1.le, hs.2⟩

/-- The time kernel as an element of the real Hilbert space `L²(ds)`. -/
def timeKernelLp (k : ℝ → ℝ) (hk : Continuous k) (t : ℝ≥0) : TimeHilbert :=
  (timeKernel_memLp k hk t).toLp (timeKernel k t)

theorem timeKernelLp_coe (k : ℝ → ℝ) (hk : Continuous k) (t : ℝ≥0) :
    timeKernelLp k hk t =ᵐ[volume] timeKernel k t :=
  (timeKernel_memLp k hk t).coeFn_toLp

/-- The Brownian isometry reduces all cross moments to ordinary kernel integrals. -/
theorem timeKernelLp_inner (k l : ℝ → ℝ) (hk : Continuous k) (hl : Continuous l)
    (t : ℝ≥0) :
    inner ℝ (timeKernelLp k hk t) (timeKernelLp l hl t) =
      ∫ s in 0..(t : ℝ), k s * l s := by
  rw [L2.inner_def]
  have he : (fun s => inner ℝ (timeKernelLp k hk t s) (timeKernelLp l hl t s)) =ᵐ[volume]
      (Ioc 0 (t : ℝ)).indicator (fun s => k ((t : ℝ)-s) * l ((t : ℝ)-s)) := by
    filter_upwards [timeKernelLp_coe k hk t, timeKernelLp_coe l hl t] with s hs ht
    rw [hs, ht]
    by_cases hst : s ∈ Ioc 0 (t : ℝ) <;> simp [timeKernel, hst, real_inner_comm, mul_comm]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le t.coe_nonneg]
  simpa only [sub_self, sub_zero] using intervalIntegral.integral_comp_sub_left
    (fun s => k s * l s) (t : ℝ) (a := 0) (b := (t : ℝ))

theorem timeKernel_tendsto (k : ℝ → ℝ) (hk : Continuous k) (t : ℝ≥0) {r : ℝ} (hr : r ≠ (t : ℝ)) :
    Tendsto (fun s : ℝ≥0 => timeKernel k s r) (𝓝 t) (𝓝 (timeKernel k t r)) := by
  by_cases hpos : 0 < r
  · rcases lt_or_gt_of_ne hr with hlt | hgt
    · have hev : ∀ᶠ s : ℝ≥0 in 𝓝 t, r ≤ (s : ℝ) :=
        ((continuous_subtype_val.tendsto t).eventually (eventually_gt_nhds hlt)).mono
          (fun _ hs => hs.le)
      have hl : Tendsto (fun s : ℝ≥0 => k ((s : ℝ)-r)) (𝓝 t) (𝓝 (k ((t : ℝ)-r))) :=
        (hk.comp (continuous_subtype_val.sub continuous_const)).tendsto t
      have he : (fun s : ℝ≥0 => timeKernel k s r) =ᶠ[𝓝 t]
          (fun s : ℝ≥0 => k ((s : ℝ)-r)) := by
        filter_upwards [hev] with s hs
        simp [timeKernel, hpos, hs]
      simpa [timeKernel, hpos, hlt.le] using hl.congr' he.symm
    · have hev : ∀ᶠ s : ℝ≥0 in 𝓝 t, (s : ℝ) < r :=
        (continuous_subtype_val.tendsto t).eventually (eventually_lt_nhds hgt)
      have he : (fun s : ℝ≥0 => timeKernel k s r) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
        filter_upwards [hev] with s hs
        simp [timeKernel, hpos, not_le.mpr hs]
      simpa [timeKernel, hpos, not_le.mpr hgt] using tendsto_const_nhds.congr' he.symm
  · have he : (fun s : ℝ≥0 => timeKernel k s r) = (fun _ => (0 : ℝ)) := by
      funext s
      simp [timeKernel, hpos]
    simp only [he]
    simpa [timeKernel, hpos] using tendsto_const_nhds

theorem timeKernelLp_norm_sub_sq (k : ℝ → ℝ) (hk : Continuous k) (t s : ℝ≥0) :
    ‖timeKernelLp k hk t - timeKernelLp k hk s‖ ^ 2 =
      ∫ r, (timeKernel k t r - timeKernel k s r) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (timeKernelLp k hk t) (timeKernelLp k hk s),
    timeKernelLp_coe k hk t, timeKernelLp_coe k hk s] with r hr ht hs
  rw [hr]
  change ((timeKernelLp k hk t r) - (timeKernelLp k hk s r)) *
    ((timeKernelLp k hk t r) - (timeKernelLp k hk s r)) = _
  rw [ht, hs]
  ring

theorem continuous_timeKernelLp (k : ℝ → ℝ) (hk : Continuous k) : Continuous (timeKernelLp k hk) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let T : ℝ := (t : ℝ) + 1
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn hk.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg (k 0)).trans (hC 0 ⟨le_rfl, hT⟩)
  have hknorm (q : ℝ≥0) (hq : (q : ℝ) ≤ T) (r : ℝ) : |timeKernel k q r| ≤ C := by
    by_cases hr : r ∈ Ioc 0 (q : ℝ)
    · rw [timeKernel, indicator_of_mem hr]
      exact hC _ ⟨sub_nonneg.mpr hr.2, (sub_le_self _ hr.1.le).trans hq⟩
    · simpa only [timeKernel, indicator_of_notMem hr, abs_zero] using hC0
  let bound : ℝ → ℝ := (Ioc 0 T).indicator (fun _ => 4 * C ^ 2)
  have hbound : Integrable bound (volume : Measure ℝ) := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact integrable_const _
  have hnear : ∀ᶠ q : ℝ≥0 in 𝓝 t, (q : ℝ) ≤ T :=
    ((continuous_subtype_val.tendsto t).eventually (eventually_lt_nhds (by dsimp [T]; linarith))).mono
      (fun _ hq => hq.le)
  have hdom : ∀ᶠ q : ℝ≥0 in 𝓝 t, ∀ᵐ r : ℝ ∂volume,
      ‖(timeKernel k q r - timeKernel k t r) ^ 2‖ ≤ bound r := by
    filter_upwards [hnear] with q hq
    apply ae_of_all
    intro r
    by_cases hr : r ∈ Ioc 0 T
    · rw [show bound r = 4 * C ^ 2 by simp [bound, hr], Real.norm_of_nonneg (sq_nonneg _)]
      have ht : (t : ℝ) ≤ T := by dsimp [T]; linarith
      have hd := (abs_sub (timeKernel k q r) (timeKernel k t r)).trans
        (add_le_add (hknorm q hq r) (hknorm t ht r))
      have hs := (sq_le_sq₀ (abs_nonneg (timeKernel k q r - timeKernel k t r))
        (by positivity : 0 ≤ C + C)).mpr hd
      simpa only [sq_abs] using hs.trans_eq (by ring)
    · have hqr : r ∉ Ioc 0 (q : ℝ) := fun hh => hr ⟨hh.1, hh.2.trans hq⟩
      have ht : (t : ℝ) ≤ T := by dsimp [T]; linarith
      have htr : r ∉ Ioc 0 (t : ℝ) := fun hh => hr ⟨hh.1, hh.2.trans ht⟩
      simp [timeKernel, hqr, htr, bound, hr]
  have hlim : ∀ᵐ r : ℝ ∂volume, Tendsto
      (fun q : ℝ≥0 => (timeKernel k q r - timeKernel k t r) ^ 2) (𝓝 t) (𝓝 (0 : ℝ)) := by
    have hne : ∀ᵐ r : ℝ ∂volume, r ≠ (t : ℝ) := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with r hr
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      ((timeKernel_tendsto k hk t hr).sub_const (timeKernel k t r)).pow 2
  have hi := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall (fun q : ℝ≥0 =>
      ((timeKernel_memLp k hk q).aestronglyMeasurable.sub
        (timeKernel_memLp k hk t).aestronglyMeasurable).pow 2)) hdom hbound hlim
  change Tendsto (fun q : ℝ≥0 => ∫ r, (timeKernel k q r - timeKernel k t r) ^ 2)
    (𝓝 t) (𝓝 (∫ _ : ℝ, (0 : ℝ))) at hi
  have hsq : Tendsto (fun q : ℝ≥0 => ‖timeKernelLp k hk q - timeKernelLp k hk t‖ ^ 2)
      (𝓝 t) (𝓝 (0 : ℝ)) := by
    simpa only [timeKernelLp_norm_sub_sq, integral_zero] using hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  change Tendsto (fun q : ℝ≥0 => Real.sqrt (‖timeKernelLp k hk q - timeKernelLp k hk t‖ ^ 2))
    (𝓝 t) (𝓝 (Real.sqrt (0 : ℝ))) at hsqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

lemma inner_timeKernelLp (f : TimeHilbert) (k : ℝ → ℝ) (hk : Continuous k) (s : ℝ≥0) :
    inner ℝ f (timeKernelLp k hk s) =
      ∫ r in Ioc 0 (s : ℝ), f r * k ((s : ℝ)-r) := by
  rw [L2.inner_def]
  have he : (fun r => inner ℝ (f r) (timeKernelLp k hk s r)) =ᵐ[volume]
      (Ioc 0 (s : ℝ)).indicator (fun r => f r * k ((s : ℝ)-r)) := by
    filter_upwards [timeKernelLp_coe k hk s] with r hr
    rw [hr]
    by_cases hs : r ∈ Ioc 0 (s : ℝ) <;> simp [timeKernel, hs, mul_comm]
  rw [integral_congr_ae he, integral_indicator measurableSet_Ioc]

lemma primitive_integrand_left (γ t s : ℝ) (hs : s ∈ Ioc 0 t) (f : ℝ → ℝ) :
    (∫ r in Ioc 0 t, (if r ≤ s then Real.exp (-γ*(s-r)) else 0) * f r) =
      ∫ r in Ioc 0 s, f r * Real.exp (-γ*(s-r)) := by
  have he : (fun r => (if r ≤ s then Real.exp (-γ*(s-r)) else 0) * f r) =
      (Iic s).indicator (fun r => f r * Real.exp (-γ*(s-r))) := by
    funext r
    by_cases hr : r ≤ s <;> simp [hr, mul_comm]
  rw [he, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic s ∩ Ioc 0 t = Ioc 0 s := by
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · rintro ⟨hrs, hr0, _⟩
      exact ⟨hr0, hrs⟩
    · rintro ⟨hr0, hrs⟩
      exact ⟨hrs, hr0, hrs.trans hs.2⟩
  rw [hset]

lemma primitive_integrand_right (γ t r : ℝ) (hr : r ∈ Ioc 0 t) (f : ℝ → ℝ) :
    (∫ s in Ioc 0 t, (if r ≤ s then Real.exp (-γ*(s-r)) else 0) * f r) =
      f r * psi γ 1 (t-r) := by
  have he : (fun s => (if r ≤ s then Real.exp (-γ*(s-r)) else 0) * f r) =
      (Ici r).indicator (fun s => Real.exp (-γ*(s-r)) * f r) := by
    funext s
    by_cases hs : r ≤ s <;> simp [hs]
  rw [he, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici r ∩ Ioc 0 t = Icc r t := by
    ext s
    simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨hrs, _, hst⟩
      exact ⟨hrs, hst⟩
    · rintro ⟨hrs, hst⟩
      exact ⟨hrs, hr.1.trans_le hrs, hst⟩
  rw [hset, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hr.2, intervalIntegral.integral_mul_const]
  have hi : (∫ s in r..t, Real.exp (-γ*(s-r))) = psi γ 1 (t-r) := by
    simpa only [sub_self, psi_succ, psi_zero] using
      (intervalIntegral.integral_comp_sub_right (psi γ 0) r (a := r) (b := t))
  rw [hi, mul_comm]

theorem timeKernelLp_primitive (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ≥0) :
    timeKernelLp (psi γ 1) (continuous_psi γ 1) t =
      ∫ s in 0..(t : ℝ), timeKernelLp (psi γ 0) (continuous_psi γ 0) s.toNNReal := by
  apply ext_inner_left ℝ
  intro f
  let μ : Measure ℝ := volume.restrict (Ioc 0 (t : ℝ))
  let w : ℝ × ℝ → ℝ := fun p => if p.2 ≤ p.1 then Real.exp (-γ * (p.1-p.2)) else 0
  have hf : Integrable (fun r => f r) μ := ((Lp.memLp f).restrict _).integrable (by norm_num)
  have hw : AEStronglyMeasurable w (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    · fun_prop
    · fun_prop
  have hwb : ∀ᵐ p ∂μ.prod μ, ‖w p‖ ≤ (1 : ℝ) := by
    apply ae_of_all
    intro p
    by_cases hp : p.2 ≤ p.1
    · simp only [w, ite_eq_left hp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) (sub_nonneg.mpr hp)
    · simp [w, hp]
  have hF : Integrable (fun p : ℝ × ℝ => w p * f p.2) (μ.prod μ) :=
    (hf.comp_snd μ).bdd_mul hw hwb
  have hswap := integral_integral_swap (f := fun s r => w (s,r) * f r) hF
  have hleft : (∫ s, ∫ r, w (s,r) * f r ∂μ ∂μ) =
      ∫ s, inner ℝ f (timeKernelLp (psi γ 0) (continuous_psi γ 0) s.toNNReal) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [show (∫ r, w (s,r) * f r ∂μ) = ∫ r in Ioc 0 s, f r * Real.exp (-γ*(s-r)) from
      primitive_integrand_left γ t s hs f]
    rw [inner_timeKernelLp]
    simp only [Real.coe_toNNReal s hs.1.le, psi_zero]
  have hright : (∫ r, ∫ s, w (s,r) * f r ∂μ ∂μ) =
      inner ℝ f (timeKernelLp (psi γ 1) (continuous_psi γ 1) t) := by
    rw [inner_timeKernelLp]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact primitive_integrand_right γ t r hr f
  have he : inner ℝ f (timeKernelLp (psi γ 1) (continuous_psi γ 1) t) =
      ∫ s in 0..(t : ℝ), inner ℝ f
        (timeKernelLp (psi γ 0) (continuous_psi γ 0) s.toNNReal) := by
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    exact hright.symm.trans (hswap.symm.trans hleft)
  rw [he]
  exact (innerSL ℝ f).intervalIntegral_comp_comm
    (((continuous_timeKernelLp (psi γ 0) (continuous_psi γ 0)).comp
      continuous_real_toNNReal).intervalIntegrable _ _)

/-- The Wiener convolution, on the existing explicitly constructed Brownian source. -/
def convolutionLp (k : ℝ → ℝ) (hk : Continuous k) (t : ℝ≥0) : Lp ℝ 2 probability :=
  ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis (timeKernelLp k hk t)

/-- Time continuity follows from dominated convergence of the actual L² kernels. -/
theorem continuous_convolutionLp (k : ℝ → ℝ) (hk : Continuous k) :
    Continuous (convolutionLp k hk) :=
  (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).continuous.comp
    (continuous_timeKernelLp k hk)

theorem convolutionLp_mean (k : ℝ → ℝ) (hk : Continuous k) (t : ℝ≥0) :
    (∫ ω, convolutionLp k hk t ω ∂probability) = 0 :=
  ULA.GaussianHilbert.isonormal_mean _ _

theorem convolutionLp_hasGaussianLaw (k : ℝ → ℝ) (hk : Continuous k) (t : ℝ≥0) :
    HasGaussianLaw (convolutionLp k hk t) probability :=
  ULA.GaussianHilbert.isonormal_hasGaussianLaw _ _

theorem convolutionLp_covariance (k l : ℝ → ℝ) (hk : Continuous k) (hl : Continuous l)
    (t : ℝ≥0) :
    cov[convolutionLp k hk t, convolutionLp l hl t; probability] =
      ∫ s in 0..(t : ℝ), k s * l s := by
  rw [convolutionLp, convolutionLp, ULA.GaussianHilbert.isonormal_covariance,
    timeKernelLp_inner]

/-- Every finite collection of convolutions is jointly Gaussian. -/
theorem convolutionLp_jointlyGaussian {ι : Type*} [Fintype ι]
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i)) (t : ℝ≥0) :
    HasGaussianLaw (fun ω i => convolutionLp (kernels i) (hc i) t ω) probability :=
  ULA.hasGaussianLaw_pi_of_linearMap_Lp probability
    (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).toLinearMap
    (ULA.GaussianHilbert.isonormal_hasGaussianLaw ULA.CanonicalBrownian.basis)
    (fun i => timeKernelLp (kernels i) (hc i) t)

/-- The joint law of the actual Brownian integrals equals the Gaussian
innovation law constructed from the Gram covariance. -/
theorem convolutionLp_jointLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i)) (t : ℝ≥0) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i => convolutionLp (kernels i) (hc i) t ω))
      (kernelGaussian kernels t) probability := by
  let F : Sample → EuclideanSpace ℝ ι :=
    fun ω => WithLp.toLp 2 (fun i => convolutionLp (kernels i) (hc i) t ω)
  have hFmem : MemLp F 2 probability :=
    MemLp.of_eval_piLp (fun i => Lp.memLp (convolutionLp (kernels i) (hc i) t))
  have hg : HasGaussianLaw F probability :=
    HasGaussianLaw.map_of_measurable
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm.toContinuousLinearMap
      (convolutionLp_jointlyGaussian kernels hc t) (by fun_prop)
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
    exact convolutionLp_mean _ _ _
  · apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    change covarianceBilin (probability.map F) x y =
      covarianceBilin (kernelGaussian kernels t) x y
    rw [covarianceBilin_apply_pi
      (fun i => Lp.memLp (convolutionLp (kernels i) (hc i) t))]
    rw [show covarianceBilin (kernelGaussian kernels t) x y =
      dotProduct (x : ι → ℝ) ((gramCovariance kernels t).mulVec y) from
      covarianceBilin_multivariateGaussian (gramCovariance_posSemidef kernels hc t.coe_nonneg) x y]
    simp_rw [convolutionLp_covariance]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, gramCovariance]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The velocity innovation `∫₀ᵗ exp(-γ(t-s)) dBₛ`. -/
def velocityLp (γ : ℝ) (t : ℝ≥0) : Lp ℝ 2 probability :=
  convolutionLp (psi γ 0) (continuous_psi γ 0) t

/-- The position innovation `∫₀ᵗ ψ₁(t-s) dBₛ`. -/
def positionLp (γ : ℝ) (t : ℝ≥0) : Lp ℝ 2 probability :=
  convolutionLp (psi γ 1) (continuous_psi γ 1) t

theorem timeKernelLp_one (t : ℝ≥0) : timeKernelLp (fun _ => 1) continuous_const t =
    ULA.CanonicalBrownian.timeIndicator t := by
  apply Lp.ext
  have hb : ULA.CanonicalBrownian.timeIndicator t =ᵐ[volume]
      (Ioc 0 (t : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) := indicatorConstLp_coeFn
  filter_upwards [timeKernelLp_coe (fun _ => 1) continuous_const t, hb] with r hr hb
  rw [hr, hb]
  rfl
theorem velocityLp_zero_friction (t : ℝ≥0) : velocityLp 0 t = ULA.CanonicalBrownian.valueLp t := by
  unfold velocityLp convolutionLp ULA.CanonicalBrownian.valueLp
  congr 1
  apply Lp.ext
  have hb : ULA.CanonicalBrownian.timeIndicator t =ᵐ[volume]
      (Ioc 0 (t : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) := indicatorConstLp_coeFn
  filter_upwards [timeKernelLp_coe (psi 0 0) (continuous_psi 0 0) t, hb] with r hr hb
  rw [hr, hb]
  simp [timeKernel, psi]

theorem velocityLp_add_friction_positionLp (γ : ℝ) (t : ℝ≥0) :
    velocityLp γ t + γ • positionLp γ t = ULA.CanonicalBrownian.valueLp t := by
  unfold velocityLp positionLp convolutionLp ULA.CanonicalBrownian.valueLp
  rw [← map_smul, ← map_add]
  congr 1
  apply Lp.ext
  have hb : ULA.CanonicalBrownian.timeIndicator t =ᵐ[volume]
      (Ioc 0 (t : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) := indicatorConstLp_coeFn
  filter_upwards [Lp.coeFn_add (timeKernelLp (psi γ 0) (continuous_psi γ 0) t)
      (γ • timeKernelLp (psi γ 1) (continuous_psi γ 1) t),
    Lp.coeFn_smul γ (timeKernelLp (psi γ 1) (continuous_psi γ 1) t),
    timeKernelLp_coe (psi γ 0) (continuous_psi γ 0) t,
    timeKernelLp_coe (psi γ 1) (continuous_psi γ 1) t, hb] with r ha hs h0 h1 hb
  rw [ha, Pi.add_apply, hs, Pi.smul_apply, h0, h1, hb]
  by_cases hr : r ∈ Ioc 0 (t : ℝ)
  · simp only [timeKernel, indicator_of_mem hr, smul_eq_mul]
    linarith [friction_mul_psi_one γ ((t : ℝ)-r)]
  · simp [timeKernel, hr]
/-- Stochastic Fubini is proved in the deterministic time Hilbert space,
then transported through the continuous isonormal isometry. -/
theorem positionLp_eq_integral_velocityLp (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ≥0) :
    positionLp γ t = ∫ s in 0..(t : ℝ), velocityLp γ s.toNNReal := by
  unfold positionLp convolutionLp
  rw [timeKernelLp_primitive γ hγ t]
  exact (ContinuousLinearMap.intervalIntegral_comp_comm
    (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).toContinuousLinearMap
      (((continuous_timeKernelLp (psi γ 0) (continuous_psi γ 0)).comp
        continuous_real_toNNReal).intervalIntegrable _ _)).symm

/-- The actual velocity Wiener integral solves the damped additive Brownian
integral equation on the same source as the numerical innovations. -/
theorem velocityLp_integral_equation (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ≥0) :
    velocityLp γ t = ULA.CanonicalBrownian.valueLp t -
      γ • ∫ s in 0..(t : ℝ), velocityLp γ s.toNNReal := by
  rw [← positionLp_eq_integral_velocityLp γ hγ]
  have hbalance := velocityLp_add_friction_positionLp γ t
  exact eq_sub_iff_add_eq.mpr hbalance

theorem continuous_velocityLp (γ : ℝ) : Continuous (velocityLp γ) :=
  continuous_convolutionLp _ _

theorem continuous_positionLp (γ : ℝ) : Continuous (positionLp γ) :=
  continuous_convolutionLp _ _

theorem velocity_position_covariance (γ : ℝ) (t : ℝ≥0) :
    cov[velocityLp γ t, positionLp γ t; probability] = klmcCovariance γ t 0 1 :=
  convolutionLp_covariance _ _ _ _ _

/-- Actual first-order Brownian integrals have exactly the KLMC noise law. -/
theorem klmc_jointLaw (γ : ℝ) (t : ℝ≥0) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i : Fin 2 =>
      convolutionLp (klmcKernels γ i) (continuous_klmcKernels γ i) t ω))
      (klmcGaussian γ t) probability :=
  convolutionLp_jointLaw _ _ _

/-- The second-order scheme's four innovations are constructed jointly from
the same Brownian motion, retaining every cross correlation. -/
theorem klmc2_jointLaw (γ : ℝ) (t : ℝ≥0) :
    HasLaw (fun ω => WithLp.toLp 2 (fun i : Fin 4 =>
      convolutionLp (klmc2Kernels γ i) (continuous_klmc2Kernels γ i) t ω))
      (klmc2Gaussian γ t) probability :=
  convolutionLp_jointLaw _ _ _

theorem hasDerivAt_positionLp_real (γ : ℝ) (hγ : 0 ≤ γ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun s : ℝ => positionLp γ s.toNNReal) (velocityLp γ x.toNNReal) x := by
  have hc := (continuous_velocityLp γ).comp continuous_real_toNNReal
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with s hs
  rw [positionLp_eq_integral_velocityLp γ hγ, Real.coe_toNNReal s hs.le]
  rfl

theorem positionLp_eq_brownian_convolution (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ≥0) :
    positionLp γ t = ∫ s in 0..(t : ℝ), Real.exp (-γ * ((t : ℝ)-s)) •
      ULA.CanonicalBrownian.valueLp s.toNNReal := by
  have hp : Continuous (fun s : ℝ => positionLp γ s.toNNReal) :=
    (continuous_positionLp γ).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => velocityLp γ s.toNNReal) :=
    (continuous_velocityLp γ).comp continuous_real_toNNReal
  have hb : Continuous (fun s : ℝ => ULA.CanonicalBrownian.valueLp s.toNNReal) := by
    have he : (fun s : ℝ => ULA.CanonicalBrownian.valueLp s.toNNReal) =
        (fun s : ℝ => velocityLp γ s.toNNReal + γ • positionLp γ s.toNNReal) :=
      funext fun s => (velocityLp_add_friction_positionLp γ s.toNNReal).symm
    rw [he]
    have hγp : Continuous (fun s : ℝ => γ • positionLp γ s.toNNReal) := hp.const_smul γ
    exact hv.add hγp
  have hzero : positionLp γ 0 = 0 := by
    rw [positionLp_eq_integral_velocityLp γ hγ]
    simp
  have hd : ∀ s ∈ Ioo 0 (t : ℝ),
      HasDerivAt (fun u : ℝ => Real.exp (γ*u) • positionLp γ u.toNNReal)
        (Real.exp (γ*s) • ULA.CanonicalBrownian.valueLp s.toNNReal) s := by
    intro s hs
    have hh := (((hasDerivAt_id s).const_mul γ).exp).smul
      (hasDerivAt_positionLp_real γ hγ hs.1)
    convert hh using 1
    · rfl
    · rw [← velocityLp_add_friction_positionLp γ s.toNNReal]
      simp only [id_eq, mul_one]
      module
  have hcont : Continuous (fun s : ℝ => Real.exp (γ*s) • positionLp γ s.toNNReal) := by fun_prop
  have hint : Continuous (fun s : ℝ => Real.exp (γ*s) • ULA.CanonicalBrownian.valueLp s.toNNReal) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s : ℝ => Real.exp (γ*s) • positionLp γ s.toNNReal)
    (f' := fun s : ℝ => Real.exp (γ*s) • ULA.CanonicalBrownian.valueLp s.toNNReal)
    t.coe_nonneg hcont.continuousOn hd (hint.intervalIntegrable 0 t)
  simp only [Real.toNNReal_coe, mul_zero, Real.exp_zero, one_smul,
    Real.toNNReal_zero, hzero, sub_zero] at hi
  have hx := congrArg (fun z : Lp ℝ 2 probability => Real.exp (-γ*(t : ℝ)) • z) hi
  have he : Real.exp (-γ*(t : ℝ)) * Real.exp (γ*(t : ℝ)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  rw [smul_smul, he, one_smul] at hx
  rw [← hx, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [smul_smul, ← Real.exp_add]
  congr 2
  ring
/-- Integration by parts representation of the velocity Wiener convolution. -/
theorem velocityLp_eq_brownian_sub_convolution (γ : ℝ) (hγ : 0 ≤ γ) (t : ℝ≥0) :
    velocityLp γ t = ULA.CanonicalBrownian.valueLp t -
      γ • ∫ s in 0..(t : ℝ), Real.exp (-γ * ((t : ℝ) - s)) •
        ULA.CanonicalBrownian.valueLp s.toNNReal := by
  rw [← positionLp_eq_brownian_convolution γ hγ t]
  exact eq_sub_iff_add_eq.mpr (velocityLp_add_friction_positionLp γ t)

end KineticLangevin.BrownianConvolution
