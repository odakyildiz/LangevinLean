import UnadjustedLangevin.LSI.KLOfDensity
import UnadjustedLangevin.LSI.ScoreCalculus
import UnadjustedLangevin.GibbsScore
import Mathlib.Probability.Moments.Tilted
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option linter.style.header false

/-! # Compatibility of log-Sobolev and smoothness constants

The bounded-test part of the argument uses the original strictly positive C¹
relative-density definition of LSI. No moment or spectral-gap property is added
to that definition.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] in
private theorem integrable_exp_mul_bounded (ν : Measure E) [IsFiniteMeasure ν]
    (f : E → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ x, |f x| ≤ B) (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t * f x)) ν := by
  refine (integrable_const (Real.exp (|t| * B))).mono' (by fun_prop) ?_
  exact ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg t)))

/-- LSI tested on the normalized exponential of a bounded C¹ function. The
right side uses a bound on its gradient, so it is independent of the tilt.
This is the differential inequality behind the bounded-test spectral gap. -/
theorem IsLogSobolev.exponential_test
    {ν : Measure E} {α : ℝ} (hLSI : IsLogSobolev ν α) (hα : 0 ≤ α)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (B D : ℝ)
    (hb : ∀ x, |f x| ≤ B) (hD : 0 ≤ D)
    (hg : ∀ x, ‖gradient f x‖ ≤ D) (t : ℝ) :
    2 * α * (t * deriv (cgf f ν) t - cgf f ν t) ≤ t ^ 2 * D ^ 2 := by
  let : IsProbabilityMeasure ν := hLSI.1
  have hmeas : Measurable f := hf.continuous.measurable
  have hi (s : ℝ) := integrable_exp_mul_bounded ν f hmeas B hb s
  have hset : integrableExpSet f ν = univ := by
    ext s
    exact ⟨fun _ ↦ mem_univ s, fun _ ↦ hi s⟩
  have ht : t ∈ interior (integrableExpSet f ν) := by simp [hset]
  have hm : 0 < mgf f ν t := mgf_pos (hi t)
  let r : E → ℝ := fun x ↦ Real.exp (t * f x) / mgf f ν t
  have hr : ∀ x, 0 < r x := fun x ↦ div_pos (Real.exp_pos _) hm
  have hrd : ContDiff ℝ 1 r := ((contDiff_const.mul hf).exp).div_const _
  have htilt : tiltedMeasure ν r = ν.tilted (fun x ↦ t * f x) := rfl
  have hp : IsProbabilityMeasure (tiltedMeasure ν r) := by
    rw [htilt]
    exact isProbabilityMeasure_tilted (hi t)
  let : IsProbabilityMeasure (tiltedMeasure ν r) := hp
  have hl (x : E) : Real.log (r x) = t * f x - cgf f ν t := by
    dsimp [r, cgf]
    rw [Real.log_div (Real.exp_pos _).ne' hm.ne', Real.log_exp]
  have hfi : Integrable f (tiltedMeasure ν r) := by
    refine (integrable_const B).mono' ?_ (ae_of_all _ fun x ↦ ?_)
    · exact hmeas.aestronglyMeasurable
    · simpa only [Real.norm_eq_abs] using hb x
  have hlog : Integrable (fun x ↦ Real.log (r x)) (tiltedMeasure ν r) := by
    have heq : (fun x ↦ Real.log (r x)) =
        (fun x ↦ t * f x) - (fun _ ↦ cgf f ν t) := funext hl
    rw [heq]
    exact (hfi.const_mul t).sub (integrable_const (cgf f ν t))
  have hkl : InformationTheory.klDiv (tiltedMeasure ν r) ν ≠ ⊤ := by
    apply InformationTheory.klDiv_ne_top (withDensity_absolutelyContinuous _ _)
    exact hlog.congr (llr_tiltedMeasure_ae_eq_log ν r hrd.continuous.measurable
      (fun x ↦ (hr x).le)).symm
  let : IsProbabilityMeasure (ν.withDensity (fun x ↦ ENNReal.ofReal (r x))) := hp
  have hent : (InformationTheory.klDiv (tiltedMeasure ν r) ν).toReal =
      t * deriv (cgf f ν) t - cgf f ν t := by
    have hllr := llr_tiltedMeasure_ae_eq_log ν r hrd.continuous.measurable
      (fun x ↦ (hr x).le)
    have hac : tiltedMeasure ν r ≪ ν := withDensity_absolutelyContinuous _ _
    rw [InformationTheory.toReal_klDiv hac (hlog.congr hllr.symm)]
    simp only [probReal_univ, add_sub_cancel_right]
    rw [integral_congr_ae hllr]
    simp_rw [hl]
    rw [integral_sub (hfi.const_mul t) (integrable_const _), integral_const_mul,
      integral_const]
    simp only [probReal_univ, one_smul]
    congr 1
    rw [htilt]
    exact congrArg (fun z ↦ t * z) (integral_tilted_mul_self ht)
  have hgrad (x : E) : gradient (fun y ↦ Real.log (r y)) x = t • gradient f x := by
    have hfun : (fun y ↦ Real.log (r y)) = fun y ↦ t * f y - cgf f ν t := funext hl
    rw [hfun]
    simp only [gradient, fderiv_sub_const, fderiv_const_mul
      (hf.differentiable (by decide) x), map_smul]
  have hbound (x : E) : ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2 ≤
      t ^ 2 * D ^ 2 := by
    rw [hgrad, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) hD |>.mpr (hg x))
      (sq_nonneg t)
  have hscore : Integrable
      (fun x ↦ ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2) (tiltedMeasure ν r) := by
    refine (integrable_const (t ^ 2 * D ^ 2)).mono' ?_ (ae_of_all _ fun x ↦ ?_)
    · have hcont : Continuous (gradient (fun y ↦ Real.log (r y))) := by
        exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
          ((hrd.log (fun x ↦ (hr x).ne')).continuous_fderiv (by decide))
      exact (hcont.norm.pow 2).aestronglyMeasurable
    · simpa only [Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (‖gradient (fun y ↦ Real.log (r y)) x‖))] using hbound x
  have hlsi := hLSI.entropy_le_fisher hα r hr hrd hp hkl (relativeFisher_ne_top ν r hscore)
  rw [hent] at hlsi
  apply hlsi.trans
  change (∫⁻ x, ENNReal.ofReal (‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2)
    ∂tiltedMeasure ν r).toReal ≤ _
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
    hscore.aestronglyMeasurable]
  exact (integral_mono hscore (integrable_const _) hbound).trans_eq (by simp)


private theorem tendsto_entropy_quotient (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 3 ψ)
    (hzero : ψ 0 = 0) :
    Tendsto (fun t ↦ (t * deriv ψ t - ψ t) / t ^ 2) (𝓝[>] 0)
      (𝓝 (iteratedDeriv 2 ψ 0 / 2)) := by
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by decide)
  have hdψ' : Differentiable ℝ (deriv ψ) := by
    simpa only [iteratedDeriv_one] using hψ.differentiable_iteratedDeriv 1 (by norm_num)
  have hcψ' : Continuous (deriv ψ) := hdψ'.continuous
  have hcψ'' : Continuous (iteratedDeriv 2 ψ) :=
    hψ.continuous_iteratedDeriv 2 (by norm_num)
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := fun t ↦ t * iteratedDeriv 2 ψ t) (g' := fun t ↦ 2 * t)
  · exact Eventually.of_forall fun t ↦ by
      have h := ((hasDerivAt_id t).mul (hdψ' t).hasDerivAt).sub (hdψ t).hasDerivAt
      convert h using 1
      · ext x; rfl
      · simp only [iteratedDeriv_succ, iteratedDeriv_zero, id_eq, one_mul]
        ring
  · exact Eventually.of_forall fun t ↦ by
      convert (hasDerivAt_id t).pow 2 using 1
      · ext x; rfl
      · simp
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero (by norm_num) (ne_of_gt ht)
  · have hcont : Continuous (fun t ↦ t * deriv ψ t - ψ t) :=
      (continuous_id.mul hcψ').sub hψ.continuous
    simpa only [zero_mul, hzero, sub_self] using
      hcont.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · have hcont : Continuous (fun t : ℝ ↦ t ^ 2) := by fun_prop
    simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  · apply (hcψ''.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).div_const 2 |>.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    field_simp [(ne_of_gt ht : t ≠ 0)]

/-- The bounded-test spectral-gap consequence of the original LSI definition.
Only a C¹ bounded test function with a bounded gradient is used. Its variance
is displayed as the second moment minus the square of the mean. -/
theorem IsLogSobolev.variance_le_of_bounded
    {ν : Measure E} {α : ℝ} (hLSI : IsLogSobolev ν α) (hα : 0 ≤ α)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) (B D : ℝ)
    (hb : ∀ x, |f x| ≤ B) (hD : 0 ≤ D)
    (hg : ∀ x, ‖gradient f x‖ ≤ D) :
    α * ((∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2) ≤ D ^ 2 := by
  let : IsProbabilityMeasure ν := hLSI.1
  have hset : integrableExpSet f ν = univ := by
    ext s
    exact ⟨fun _ ↦ mem_univ s, fun _ ↦
      integrable_exp_mul_bounded ν f hf.continuous.measurable B hb s⟩
  have hanalytic (t : ℝ) : AnalyticAt ℝ (cgf f ν) t := analyticAt_cgf (by simp [hset])
  have hcgf : ContDiff ℝ 3 (cgf f ν) :=
    contDiff_iff_contDiffAt.mpr (fun t ↦ (hanalytic t).contDiffAt)
  have hlim := (tendsto_entropy_quotient (cgf f ν) hcgf (cgf_zero)).const_mul (2 * α)
  have hder : iteratedDeriv 2 (cgf f ν) 0 =
      (∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 := by
    rw [iteratedDeriv_two_cgf (by simp [hset]), deriv_cgf_zero (by simp [hset])]
    simp
  rw [hder] at hlim
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0,
      2 * α * ((t * deriv (cgf f ν) t - cgf f ν t) / t ^ 2) ≤ D ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    simpa only [mul_comm (D ^ 2)] using hLSI.exponential_test hα f hf B D hb hD hg t
  have h := le_of_tendsto hlim hbound
  nlinarith


omit [CompleteSpace E] in
private theorem integral_gibbs_weighted [FiniteDimensional ℝ E]
    (U : E → ℝ) (hdiff : Differentiable ℝ U) (g : E → ℝ) :
    (∫ x, g x ∂gibbsMeasure U) = (gibbsPartition U)⁻¹.toReal *
      ∫ x, Real.exp (-U x) * g x ∂volume := by
  rw [gibbsMeasure, integral_smul_measure]
  congr 1
  unfold gibbsWeight
  have hw : Measurable (fun x ↦ ENNReal.ofReal (Real.exp (-U x))) := by
    have hUc := hdiff.continuous
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul
    hw (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

omit [CompleteSpace E] in
private theorem integrable_gibbs_weighted [FiniteDimensional ℝ E]
    (U : E → ℝ) (hdiff : Differentiable ℝ U) (hZ : gibbsPartition U ≠ ⊤)
    (g : E → ℝ) :
    Integrable g (gibbsMeasure U) ↔
      Integrable (fun x ↦ Real.exp (-U x) * g x) volume := by
  rw [gibbsMeasure, integrable_inv_smul_measure (ne_of_gt (gibbsPartition_pos U hdiff)) hZ]
  unfold gibbsWeight
  have hw : Measurable (fun x ↦ ENNReal.ofReal (Real.exp (-U x))) := by
    have hUc := hdiff.continuous
    fun_prop
  rw [integrable_withDensity_iff_integrable_smul' hw
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- Gibbs integration by parts for a bounded C¹ test with bounded gradient.
Finiteness of the Gibbs score is supplied by the first-order smoothness
assumptions; no position moment or boundary condition is assumed. -/
theorem gibbs_stein_bounded [FiniteDimensional ℝ E]
    (U : E → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (hZ : gibbsPartition U ≠ ⊤)
    (ψ : E → ℝ) (hψ : ContDiff ℝ 1 ψ) (B D : ℝ)
    (hb : ∀ x, |ψ x| ≤ B) (_hD : 0 ≤ D)
    (hg : ∀ x, ‖gradient ψ x‖ ≤ D) (v : E) :
    (∫ x, ψ x * inner ℝ (gradient U x) v ∂gibbsMeasure U) =
      ∫ x, inner ℝ (gradient ψ x) v ∂gibbsMeasure U := by
  let : IsProbabilityMeasure (gibbsMeasure U) := by
    constructor
    rw [gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (gibbsPartition_pos U hdiff)) hZ
  have hs := (gibbs_score_subgaussian U L hdiff hLip hZ v).integrable
  have hiψ : Integrable ψ (gibbsMeasure U) :=
    (integrable_const B).mono' hψ.continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)
  have hprod : Integrable (fun x ↦ ψ x * inner ℝ (gradient U x) v) (gibbsMeasure U) :=
    hs.bdd_mul hψ.continuous.aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)
  have hcgrad : Continuous (gradient ψ) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hψ.continuous_fderiv (by decide))
  have hdir : Integrable (fun x ↦ inner ℝ (gradient ψ x) v) (gibbsMeasure U) := by
    apply (integrable_const (D * ‖v‖)).mono'
      (hcgrad.inner continuous_const).aestronglyMeasurable
    exact ae_of_all _ fun x ↦ (by
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hg x) (norm_nonneg v)))
  have hw (x : E) : fderiv ℝ (fun y ↦ Real.exp (-U y)) x v =
      -(Real.exp (-U x) * inner ℝ (gradient U x) v) := by
    have hd : HasFDerivAt (fun z ↦ Real.exp (-U z))
        (Real.exp (-U x) • (-fderiv ℝ U x)) x :=
      (hdiff x).hasFDerivAt.neg.exp
    rw [hd.fderiv]
    simp [inner_gradient_left]
  have h₁ : Integrable
      (fun x ↦ fderiv ℝ ψ x v * Real.exp (-U x)) volume := by
    simpa only [← inner_gradient_left, mul_comm] using
      (integrable_gibbs_weighted U hdiff hZ _).mp hdir
  have h₂ : Integrable
      (fun x ↦ ψ x * fderiv ℝ (fun y ↦ Real.exp (-U y)) x v) volume := by
    have hi := ((integrable_gibbs_weighted U hdiff hZ _).mp hprod).neg
    convert hi using 1
    ext x
    simp only [hw, Pi.neg_apply]
    ring
  have h₃ : Integrable (fun x ↦ ψ x * Real.exp (-U x)) volume := by
    simpa only [mul_comm] using (integrable_gibbs_weighted U hdiff hZ _).mp hiψ
  have hip := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h₁ h₂ h₃
    (fun x _ ↦ hψ.differentiable (by decide) x) (fun x _ ↦ hdiff.neg.exp x)
  simp only [hw, mul_neg] at hip
  rw [integral_neg] at hip
  have hi : (∫ x, Real.exp (-U x) * (ψ x * inner ℝ (gradient U x) v) ∂volume) =
      ∫ x, Real.exp (-U x) * inner ℝ (gradient ψ x) v ∂volume := by
    simpa only [← inner_gradient_left, neg_inj, mul_assoc, mul_comm, mul_left_comm] using hip
  rw [integral_gibbs_weighted U hdiff, integral_gibbs_weighted U hdiff, hi]


private theorem integral_mul_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤
      (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hfs := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hgs := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg
  have hfg : Integrable (fun x ↦ f x * g x) μ := by
    simpa only [Pi.mul_def] using hf.integrable_mul hg
  have hdisc : discrim (∫ x, f x ^ 2 ∂μ) (2 * ∫ x, f x * g x ∂μ)
      (∫ x, g x ^ 2 ∂μ) ≤ 0 := by
    apply discrim_le_zero
    intro c
    have hnonneg : (0 : ℝ) ≤ ∫ x, (c * f x + g x) ^ 2 ∂μ :=
      integral_nonneg (fun x ↦ sq_nonneg (c * f x + g x))
    have hpoint : (fun x ↦ (c * f x + g x) ^ 2) =
        (fun x ↦ c ^ 2 * f x ^ 2) + (fun x ↦ 2 * c * (f x * g x)) + (fun x ↦ g x ^ 2) := by
      ext x; dsimp; ring
    rw [hpoint] at hnonneg
    simp only [Pi.add_def] at hnonneg
    have hsum : Integrable (fun x ↦ c ^ 2 * f x ^ 2 + 2 * c * (f x * g x)) μ := by
      simpa only [Pi.add_def] using (hfs.const_mul (c ^ 2)).add (hfg.const_mul (2 * c))
    rw [integral_add hsum hgs, integral_add (hfs.const_mul _) (hfg.const_mul _),
      integral_const_mul, integral_const_mul] at hnonneg
    nlinarith
  simp only [discrim] at hdisc
  nlinarith

/-- In positive dimension, the log-Sobolev constant of a normalized smooth
Gibbs law cannot exceed its global gradient Lipschitz constant. The proof
uses bounded sinusoidal tests, so it needs no assumed second position moment,
transport inequality, Hessian, or strong convexity. -/
theorem logSobolev_constant_le_smoothness [FiniteDimensional ℝ E] [Nontrivial E]
    (U : E → ℝ) (L : ℝ≥0) (α : ℝ) (hα : 0 ≤ α)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hZ : gibbsPartition U ≠ ⊤) (hLSI : IsLogSobolev (gibbsMeasure U) α) :
    α ≤ (L : ℝ) := by
  let : IsProbabilityMeasure (gibbsMeasure U) := hLSI.1
  obtain ⟨v, hv⟩ := exists_norm_eq E (by norm_num : (0 : ℝ) ≤ 1)
  let ν := gibbsMeasure U
  let s : E → ℝ := fun x ↦ inner ℝ (gradient U x) v
  have hs := gibbs_score_subgaussian U L hdiff hLip hZ v
  have hs₂ : MemLp s 2 ν := hs.memLp 2
  have hsint : Integrable s ν := hs.integrable
  have hsmean : (∫ x, s x ∂ν) = 0 := by
    have h := gibbs_stein_bounded U L hdiff hLip hZ (fun _ ↦ 1)
      contDiff_const 1 0 (fun _ ↦ by norm_num) le_rfl (by intro x; simp [gradient]) v
    simpa only [one_mul, gradient_fun_const, inner_zero_left, integral_zero] using h
  have hscore : (∫ x, s x ^ 2 ∂ν) ≤ (L : ℝ) := by
    have h := integral_sq_le_of_subgaussian ν s (L * ‖v‖₊ ^ 2) hs
    simpa only [NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, hv, one_pow, mul_one] using h
  have hbound (t : ℝ) (ht : 0 < t) :
      α * (∫ x, Real.cos (t * inner ℝ v x) ∂ν) ^ 2 ≤ (L : ℝ) := by
    let f : E → ℝ := fun x ↦ Real.sin (t * inner ℝ v x)
    have hf : ContDiff ℝ 1 f :=
      (contDiff_const.mul (contDiff_const.inner ℝ contDiff_id)).sin
    have hfb (x : E) : |f x| ≤ 1 := Real.abs_sin_le_one _
    have hgrad (x : E) : gradient f x =
        (Real.cos (t * inner ℝ v x) * t) • v := by
      have hlin : HasFDerivAt (fun y ↦ inner ℝ v y) (InnerProductSpace.toDual ℝ E v) x :=
        (InnerProductSpace.toDual ℝ E v).hasFDerivAt
      have hd := (hlin.const_mul t).sin
      rw [gradient, hd.fderiv]
      simp only [map_smul, LinearIsometryEquiv.symm_apply_apply, smul_smul]
    have hfg (x : E) : ‖gradient f x‖ ≤ |t| := by
      rw [hgrad, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (Real.abs_cos_le_one (t * inner ℝ v x)) (abs_nonneg t)
    have hf₂ : MemLp f 2 ν := MemLp.of_bound hf.continuous.aestronglyMeasurable 1
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hfb x)
    have hfint : Integrable f ν := hf₂.integrable (by norm_num)
    have hvar := hLSI.variance_le_of_bounded hα f hf 1 |t| hfb (abs_nonneg t) hfg
    have hvareq : (∫ x, (f x - ∫ y, f y ∂ν) ^ 2 ∂ν) =
        (∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 := by
      rw [← variance_eq_integral hf₂.aemeasurable, variance_eq_sub hf₂]
      rfl
    have hstein := gibbs_stein_bounded U L hdiff hLip hZ f hf 1 |t| hfb (abs_nonneg t) hfg v
    have hcrosse : (∫ x, s x * (f x - ∫ y, f y ∂ν) ∂ν) =
        t * ∫ x, Real.cos (t * inner ℝ v x) ∂ν := by
      simp_rw [mul_sub]
      have hprod : Integrable (fun x ↦ s x * f x) ν := by
        simpa only [Pi.mul_def] using hs₂.integrable_mul hf₂
      rw [integral_sub hprod (hsint.mul_const _), integral_mul_const, hsmean, zero_mul, sub_zero]
      have hh : (∫ x, s x * f x ∂ν) =
          ∫ x, inner ℝ (gradient f x) v ∂ν := by
        simpa only [s, ν, mul_comm] using hstein
      rw [hh]
      simp_rw [hgrad, real_inner_smul_left, real_inner_self_eq_norm_sq, hv,
        one_pow, mul_one, mul_comm (Real.cos _), ← integral_const_mul]
    have hcs := integral_mul_sq_le ν s (fun x ↦ f x - ∫ y, f y ∂ν)
      hs₂ (hf₂.sub (memLp_const _))
    rw [hcrosse, hvareq] at hcs
    have hvarnonneg : 0 ≤ (∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2 := by
      rw [← hvareq]
      exact integral_nonneg fun _ ↦ sq_nonneg _
    have hcs' := hcs.trans (mul_le_mul_of_nonneg_right hscore hvarnonneg)
    have hfinal : α * (t * ∫ x, Real.cos (t * inner ℝ v x) ∂ν) ^ 2 ≤
        (L : ℝ) * t ^ 2 := by
      calc
        _ ≤ α * ((L : ℝ) * ((∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs' hα
        _ = (L : ℝ) * (α * ((∫ x, f x ^ 2 ∂ν) - (∫ x, f x ∂ν) ^ 2)) := by ring
        _ ≤ (L : ℝ) * t ^ 2 := by
          exact mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using hvar) L.coe_nonneg
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos ht)).mp
    nlinarith [hfinal]
  have hlim : Tendsto (fun t : ℝ ↦ ∫ x, Real.cos (t * inner ℝ v x) ∂ν)
      (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ ↦ ∫ x, Real.cos (t * inner ℝ v x) ∂ν) 0 := by
      apply continuousAt_of_dominated (bound := fun _ ↦ (1 : ℝ))
      · exact Eventually.of_forall fun t ↦ by fun_prop
      · exact Eventually.of_forall fun t ↦ ae_of_all _ fun x ↦ by
          simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * inner ℝ v x)
      · exact integrable_const 1
      · exact ae_of_all _ fun x ↦ by fun_prop
    simpa only [zero_mul, Real.cos_zero, integral_const, probReal_univ, one_smul] using
      hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0,
      α * (∫ x, Real.cos (t * inner ℝ v x) ∂ν) ^ 2 ≤ (L : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hbound t ht
  have hh := le_of_tendsto ((hlim.pow 2).const_mul α) hevent
  simpa using hh


/-- The same compatibility bound using only LSI and first-order smoothness.
LSI includes probability normalization; this rules out an infinite Gibbs
partition internally. -/
theorem IsLogSobolev.constant_le_smoothness [FiniteDimensional ℝ E] [Nontrivial E]
    {U : E → ℝ} {L : ℝ≥0} {α : ℝ}
    (hLSI : IsLogSobolev (gibbsMeasure U) α)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) :
    α ≤ (L : ℝ) := by
  by_cases hα : 0 ≤ α
  · have hZ : gibbsPartition U ≠ ⊤ := by
      intro htop
      have hzero : gibbsMeasure U = 0 := by simp [gibbsMeasure, htop]
      let : IsProbabilityMeasure (gibbsMeasure U) := hLSI.1
      have hh := measure_univ (μ := gibbsMeasure U)
      simp only [hzero, Measure.coe_zero, Pi.zero_apply] at hh
      exact zero_ne_one hh
    exact logSobolev_constant_le_smoothness U L α hα hdiff hLip hZ hLSI
  · exact (lt_of_not_ge hα).le.trans L.coe_nonneg

end ULA.LSI
