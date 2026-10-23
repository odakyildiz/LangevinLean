import KineticLangevin.BrownianSegments
import KineticLangevin.VectorSegmentEquations

/-! # Exact time convolution of the actual Wiener response kernels -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin.BrownianConvolution

/-- Ordinary causal exponential convolution of a deterministic scalar kernel. -/
def causalExponential (β : ℝ) (k : ℝ→ℝ) (t : ℝ) : ℝ :=
  ∫ s in 0..t,Real.exp (-β*(t-s))*k s

theorem causalExponential_factor (β : ℝ) (k : ℝ→ℝ) (t : ℝ) :
    causalExponential β k t=Real.exp (-β*t)*∫ s in 0..t,Real.exp (β*s)*k s := by
  rw [causalExponential,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [← mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem continuous_causalExponential (β : ℝ) (k : ℝ→ℝ) (hk : Continuous k) :
    Continuous (causalExponential β k) := by
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-β*t)*∫ s in 0..t,Real.exp (β*s)*k s) :=
    (by fun_prop : Continuous (fun t : ℝ ↦ Real.exp (-β*t))).mul
      (intervalIntegral.continuous_primitive (μ:=volume)
        ((by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (β*s))).mul hk).intervalIntegrable 0)
  exact hc.congr (fun t ↦ (causalExponential_factor β k t).symm)

lemma cutoff_integrand_left (k : ℝ→ℝ) (t s : ℝ) (hs : s∈Ioc 0 t) (f : ℝ→ℝ) :
    (∫ r in Ioc 0 t,(if r≤s then k (s-r) else 0)*f r)=∫ r in Ioc 0 s,f r*k (s-r) := by
  have he : (fun r ↦ (if r≤s then k (s-r) else 0)*f r)=
      (Iic s).indicator (fun r ↦ f r*k (s-r)) := by
    funext r
    by_cases hr : r≤s <;> simp [hr,mul_comm]
  rw [he,integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic s∩Ioc 0 t=Ioc 0 s := by
    ext r
    simp only [mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · rintro ⟨hrs,hr0,_⟩;exact ⟨hr0,hrs⟩
    · rintro ⟨hr0,hrs⟩;exact ⟨hrs,hr0,hrs.trans hs.2⟩
  rw [hset]

lemma damped_integrand_right (β γ : ℝ) (k : ℕ) (t r : ℝ) (hr : r∈Ioc 0 t) (f : ℝ→ℝ) :
    (∫ s in Ioc 0 t,(if r≤s then Real.exp (-β*(t-s))*psi γ k (s-r) else 0)*f r)=
      f r*causalExponential β (psi γ k) (t-r) := by
  have he : (fun s ↦ (if r≤s then Real.exp (-β*(t-s))*psi γ k (s-r) else 0)*f r)=
      (Ici r).indicator (fun s ↦ (Real.exp (-β*(t-s))*psi γ k (s-r))*f r) := by
    funext s
    by_cases hs : r≤s <;> simp [hs]
  rw [he,integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici r∩Ioc 0 t=Icc r t := by
    ext s
    simp only [mem_inter_iff,mem_Ici,mem_Ioc,mem_Icc]
    constructor
    · rintro ⟨hrs,_,hst⟩;exact ⟨hrs,hst⟩
    · rintro ⟨hrs,hst⟩;exact ⟨hrs,hr.1.trans_le hrs,hst⟩
  rw [hset,integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hr.2,
    intervalIntegral.integral_mul_const]
  have hi : (∫ s in r..t,Real.exp (-β*(t-s))*psi γ k (s-r))=causalExponential β (psi γ k) (t-r) := by
    have hfun : (fun s ↦ Real.exp (-β*(t-s))*psi γ k (s-r))=
        (fun u ↦ Real.exp (-β*((t-r)-u))*psi γ k u) ∘ (fun s ↦ s-r) := by
      funext s
      dsimp only [Function.comp_def]
      congr 3
      ring
    rw [hfun]
    simpa only [Function.comp_def,sub_self,causalExponential] using
      (intervalIntegral.integral_comp_sub_right
        (fun u ↦ Real.exp (-β*((t-r)-u))*psi γ k u) r (a:=r) (b:=t))
  rw [hi,mul_comm]

/-- The actual deterministic Hilbert kernel for φ is the damped time convolution
of the actual ψ kernel. This proves the stochastic Fubini identity after the
isonormal map, rather than assuming a stochastic interchange rule. -/
theorem timeKernelLp_causalExponential (β γ : ℝ) (hβ : 0≤β) (k : ℕ) (t : ℝ≥0) :
    timeKernelLp (causalExponential β (psi γ k)) (continuous_causalExponential β (psi γ k) (continuous_psi γ k)) t =
      ∫ s in 0..(t:ℝ),Real.exp (-β*((t:ℝ)-s)) • timeKernelLp (psi γ k) (continuous_psi γ k) s.toNNReal := by
  apply ext_inner_left ℝ
  intro f
  let μ : Measure ℝ := volume.restrict (Ioc 0 (t:ℝ))
  let w : ℝ×ℝ→ℝ := fun p ↦
    if 0<p.2 ∧ p.2≤p.1 ∧ p.1≤(t:ℝ) then
      Real.exp (-β*((t:ℝ)-p.1))*psi γ k (p.1-p.2) else 0
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) (t:ℝ))).exists_bound_of_continuousOn
    (continuous_psi γ k).continuousOn
  have hC0 : 0≤C := (norm_nonneg (psi γ k 0)).trans (hC 0 ⟨le_rfl,t.coe_nonneg⟩)
  have hf : Integrable (fun r ↦ f r) μ := ((Lp.memLp f).restrict _).integrable (by norm_num)
  have hw : AEStronglyMeasurable w (μ.prod μ) := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_fst).inter (measurableSet_le measurable_fst measurable_const)))
    · have hp := continuous_psi γ k
      fun_prop
    · fun_prop
  have hwb : ∀ᵐ p ∂μ.prod μ,‖w p‖≤C := by
    apply ae_of_all
    intro p
    by_cases hp : 0<p.2 ∧ p.2≤p.1 ∧ p.1≤(t:ℝ)
    · simp only [w,ite_eq_left hp,norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-β*((t:ℝ)-p.1))≤1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) (sub_nonneg.mpr hp.2.2)
      have hk := hC (p.1-p.2) ⟨sub_nonneg.mpr hp.2.1,by linarith [hp.1,hp.2.2]⟩
      change |psi γ k (p.1-p.2)|≤C at hk
      exact (mul_le_mul_of_nonneg_left hk (Real.exp_pos _).le).trans
        (by nlinarith [mul_nonneg (sub_nonneg.mpr hexp) hC0])
    · simp [w,hp,hC0]
  have hF : Integrable (fun p : ℝ×ℝ ↦ w p*f p.2) (μ.prod μ) :=
    (hf.comp_snd μ).bdd_mul hw hwb
  have hswap := integral_integral_swap (f:=fun s r ↦ w (s,r)*f r) hF
  have hleft : (∫ s,∫ r,w (s,r)*f r ∂μ ∂μ)=
      ∫ s,Real.exp (-β*((t:ℝ)-s))*inner ℝ f
        (timeKernelLp (psi γ k) (continuous_psi γ k) s.toNNReal) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have he : (∫ r,w (s,r)*f r ∂μ)=Real.exp (-β*((t:ℝ)-s))*
        ∫ r in Ioc 0 (t:ℝ),(if r≤s then psi γ k (s-r) else 0)*f r := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      dsimp only [w]
      by_cases hrs : r≤s <;> simp [hr.1,hs.2,hrs] <;> ring
    rw [he,cutoff_integrand_left _ _ s hs f,inner_timeKernelLp]
    simp only [Real.coe_toNNReal s hs.1.le]
  have hright : (∫ r,∫ s,w (s,r)*f r ∂μ ∂μ)=
      inner ℝ f (timeKernelLp (causalExponential β (psi γ k)) (continuous_causalExponential β (psi γ k) (continuous_psi γ k)) t) := by
    rw [inner_timeKernelLp]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have he : (∫ s,w (s,r)*f r ∂μ)=
        ∫ s in Ioc 0 (t:ℝ),(if r≤s then Real.exp (-β*((t:ℝ)-s))*psi γ k (s-r) else 0)*f r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      dsimp only [w]
      by_cases hrs : r≤s <;> simp [hr.1,hs.2,hrs]
    rw [he]
    exact damped_integrand_right β γ k t r hr f
  have he : inner ℝ f (timeKernelLp (causalExponential β (psi γ k)) (continuous_causalExponential β (psi γ k) (continuous_psi γ k)) t)=
      ∫ s in 0..(t:ℝ),Real.exp (-β*((t:ℝ)-s))*inner ℝ f
        (timeKernelLp (psi γ k) (continuous_psi γ k) s.toNNReal) := by
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    exact hright.symm.trans (hswap.symm.trans hleft)
  have hc : Continuous (fun s : ℝ ↦ Real.exp (-β*((t:ℝ)-s)) •
      timeKernelLp (psi γ k) (continuous_psi γ k) s.toNNReal) :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-β*((t:ℝ)-s)))).smul
      ((continuous_timeKernelLp (psi γ k) (continuous_psi γ k)).comp continuous_real_toNNReal)
  rw [he]
  simpa only [map_smul,smul_eq_mul,innerSL_apply_apply] using
    (innerSL ℝ f).intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)

/-- The φ response uses the same friction in its deterministic exponential convolution. -/
theorem timeKernelLp_phi (γ : ℝ) (hγ : 0≤γ) (k : ℕ) (t : ℝ≥0) :
    timeKernelLp (phi γ (k+1)) (continuous_phi γ (k+1)) t =
      ∫ s in 0..(t:ℝ),Real.exp (-γ*((t:ℝ)-s)) • timeKernelLp (psi γ k) (continuous_psi γ k) s.toNNReal :=
  timeKernelLp_causalExponential γ γ hγ k t

/-- Every integrated ψ response is the time primitive of the preceding actual Hilbert kernel. -/
theorem timeKernelLp_primitive_all (γ : ℝ) (k : ℕ) (t : ℝ≥0) :
    timeKernelLp (psi γ (k+1)) (continuous_psi γ (k+1)) t=
      ∫ s in 0..(t:ℝ),timeKernelLp (psi γ k) (continuous_psi γ k) s.toNNReal := by
  have he : causalExponential 0 (psi γ k)=psi γ (k+1) := by
    funext r
    simp [causalExponential,psi_succ]
  have hi := timeKernelLp_causalExponential 0 γ le_rfl k t
  simpa only [he,zero_mul,neg_zero,Real.exp_zero,one_smul] using hi

/-- The φ stochastic response on any Brownian interval is the ordinary damped convolution of ψ responses. -/
theorem segmentConvolutionLp_phi (γ : ℝ) (hγ : 0≤γ) (k : ℕ) (a t : ℝ≥0) :
    segmentConvolutionLp (phi γ (k+1)) (continuous_phi γ (k+1)) a t=
      ∫ s in 0..(t:ℝ),Real.exp (-γ*((t:ℝ)-s)) •
        segmentConvolutionLp (psi γ k) (continuous_psi γ k) a s.toNNReal := by
  let L := (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).toContinuousLinearMap.comp
    (timeShift a).toContinuousLinearMap
  change L (timeKernelLp (phi γ (k+1)) (continuous_phi γ (k+1)) t)=_
  have hc : Continuous (fun s : ℝ ↦ Real.exp (-γ*((t:ℝ)-s)) •
      timeKernelLp (psi γ k) (continuous_psi γ k) s.toNNReal) :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*((t:ℝ)-s)))).smul
      ((continuous_timeKernelLp (psi γ k) (continuous_psi γ k)).comp continuous_real_toNNReal)
  rw [timeKernelLp_phi γ hγ,← L.intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact map_smul L _ _

/-- Every actual scalar ψ response has the following response as its exact time primitive. -/
theorem segmentConvolutionLp_primitive_all (γ : ℝ) (k : ℕ) (a t : ℝ≥0) :
    segmentConvolutionLp (psi γ (k+1)) (continuous_psi γ (k+1)) a t=
      ∫ s in 0..(t:ℝ),segmentConvolutionLp (psi γ k) (continuous_psi γ k) a s.toNNReal := by
  let L := (ULA.GaussianHilbert.isonormal ULA.CanonicalBrownian.basis).toContinuousLinearMap.comp
    (timeShift a).toContinuousLinearMap
  change L (timeKernelLp (psi γ (k+1)) (continuous_psi γ (k+1)) t)=_
  rw [timeKernelLp_primitive_all γ k]
  exact (L.intervalIntegral_comp_comm
    (((continuous_timeKernelLp (psi γ k) (continuous_psi γ k)).comp
      continuous_real_toNNReal).intervalIntegrable 0 t)).symm

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The actual vector φ response is the same damped time convolution on the same Brownian source. -/
theorem vectorSegmentLp_phi (γ : ℝ) (hγ : 0≤γ) (k : ℕ) (a t : ℝ≥0) :
    vectorSegmentLp ι (phi γ (k+1)) (continuous_phi γ (k+1)) a t=
      ∫ s in 0..(t:ℝ),Real.exp (-γ*((t:ℝ)-s)) •
        vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a s.toNNReal := by
  have hc : Continuous (fun s : ℝ ↦ Real.exp (-γ*((t:ℝ)-s)) •
      segmentConvolutionLp (psi γ k) (continuous_psi γ k) a s.toNNReal) :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*((t:ℝ)-s)))).smul
      ((continuous_segmentConvolutionLp (psi γ k) (continuous_psi γ k) a).comp continuous_real_toNNReal)
  unfold vectorSegmentLp
  rw [segmentConvolutionLp_phi γ hγ,← (spatialLift ι).intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  exact map_smul (spatialLift ι) _ _

/-- The actual vector ψ responses satisfy every ordinary time-primitive identity. -/
theorem vectorSegmentLp_primitive_all (γ : ℝ) (k : ℕ) (a t : ℝ≥0) :
    vectorSegmentLp ι (psi γ (k+1)) (continuous_psi γ (k+1)) a t=
      ∫ s in 0..(t:ℝ),vectorSegmentLp ι (psi γ k) (continuous_psi γ k) a s.toNNReal := by
  unfold vectorSegmentLp
  rw [segmentConvolutionLp_primitive_all γ k]
  exact ((spatialLift ι).intervalIntegral_comp_comm
    (((continuous_segmentConvolutionLp (psi γ k) (continuous_psi γ k) a).comp
      continuous_real_toNNReal).intervalIntegrable 0 t)).symm

end KineticLangevin.BrownianConvolution
