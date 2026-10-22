import UnadjustedLangevin.Generator
import UnadjustedLangevin.LSI.EntropyChainRule
import UnadjustedLangevin.LSI.GaussianEntropy
import UnadjustedLangevin.LSI.BoundedLog
import UnadjustedLangevin.LSI.GaussianTimeDerivative
import UnadjustedLangevin.LSI.GaussianMeasurability
import UnadjustedLangevin.LSI.GaussianWeakEquation
import UnadjustedLangevin.LSI.GaussianEnergyIntegrability

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-! # Entropy identities for the actual Gaussian interpolation

Bounded entropy primitives are integrable under the Gibbs law and converge
to the actual KL entropy. These are the endpoint identifications used when
passing from bounded weak tests to the entropy identity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ULA.LSI

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The bounded-log derivative weights can be removed from any integrable
energy or flux by dominated convergence; each weight lies between zero and one. -/
theorem boundedLogWeight_integral_tendsto
    (ν : Measure Ω) (z f : Ω → ℝ) (hz : Measurable z) (hf : Integrable f ν) :
    Tendsto (fun m : ℕ ↦ ∫ x, boundedLogWeight m (z x) * f x ∂ν)
      atTop (𝓝 (∫ x, f x ∂ν)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
  · intro m
    have hm : Measurable (fun x ↦ boundedLogWeight m (z x)) := by
      unfold boundedLogWeight
      fun_prop
    exact hm.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact hf.norm
  · intro m
    exact ae_of_all _ fun x ↦ by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (boundedLogWeight_nonneg m (z x))]
      exact mul_le_of_le_one_left (norm_nonneg _) (boundedLogWeight_le_one m (z x))
  · exact ae_of_all _ fun x ↦ by
      simpa only [one_mul] using (boundedLogWeight_tendsto (z x)).mul_const (f x)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The flux pairing of two square-integrable fields is integrable. -/
theorem integrable_inner_of_memLp_two (ν : Measure Ω) (f g : Ω → E)
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x ↦ inner ℝ (f x) (g x)) ν := by
  have hp : Integrable (fun x ↦ ‖f x‖ * ‖g x‖) ν :=
    memLp_one_iff_integrable.mp (show MemLp (fun x ↦ ‖f x‖ * ‖g x‖) 1 ν from
      hf.norm.mul hg.norm)
  apply hp.mono' (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact ae_of_all _ fun x ↦ norm_inner_le_norm (𝕜 := ℝ) (f x) (g x)

/-- The real normalized Gibbs density used to perform the time chain rule in
Lebesgue measure. Its positivity makes all reciprocal cancellations exact. -/
def gibbsLebesgueDensity (U : E → ℝ) (y : E) : ℝ :=
  (ULA.gibbsPartition U).toReal⁻¹ * Real.exp (-U y)

theorem gibbsLebesgueDensity_pos (U : E → ℝ) (hU : Differentiable ℝ U)
    [IsProbabilityMeasure (ULA.gibbsMeasure U)] (y : E) :
    0 < gibbsLebesgueDensity U y := by
  exact mul_pos (inv_pos.mpr (ENNReal.toReal_pos (ULA.gibbsPartition_pos U hU).ne'
    (gibbsPartition_ne_top_of_probability U))) (Real.exp_pos _)

/-- The normalized Gibbs law equals the measure with its displayed real
Lebesgue density, with finite normalization proved from probability mass. -/
theorem gibbsMeasure_eq_withDensity_real (U : E → ℝ) (hU : Differentiable ℝ U)
    [IsProbabilityMeasure (ULA.gibbsMeasure U)] :
    ULA.gibbsMeasure U = volume.withDensity (fun y ↦
      ENNReal.ofReal (gibbsLebesgueDensity U y)) := by
  have hw : Measurable (ULA.gibbsWeight U) :=
    (Real.measurable_exp.comp hU.continuous.measurable.neg).ennreal_ofReal
  rw [ULA.gibbsMeasure, ← withDensity_smul _ hw]
  congr 1
  funext y
  dsimp [gibbsLebesgueDensity, ULA.gibbsWeight]
  rw [ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← ENNReal.toReal_inv, ENNReal.ofReal_toReal
    (ENNReal.inv_ne_top.mpr (ULA.gibbsPartition_pos U hU).ne')]

/-- The exact time derivative of the weighted bounded entropy integrand. Gibbs
normalization cancels the reciprocal density, leaving the bounded log slope
times the actual mixture's Lebesgue time derivative. -/
theorem hasDerivAt_weighted_boundedEntropy
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ)
    (t : ℝ) (ht : 0 < t) (m : ℕ) (y : E) :
    HasDerivAt (fun s ↦ gibbsLebesgueDensity U y *
      boundedEntropy m (interpolationRelativeDensity U μ s y))
      (boundedLogSlope m (Real.log (interpolationRelativeDensity U μ t y)) *
        interpolationLebesgueDensityTimeDerivative U μ t y) t := by
  have htime := (hasDerivAt_interpolationLebesgueDensity_time U μ L hLip hG t ht y).2
  have hrel : HasDerivAt (fun s ↦ interpolationRelativeDensity U μ s y)
      (((ULA.gibbsPartition U).toReal * Real.exp (U y)) *
        interpolationLebesgueDensityTimeDerivative U μ t y) t := by
    exact htime.const_mul _
  have hcomp := (boundedEntropy_hasDerivAt m
    (interpolationRelativeDensity_pos U μ L hU hLip t ht y)).comp t hrel
  have hweighted := hcomp.const_mul (gibbsLebesgueDensity U y)
  have hZ : (ULA.gibbsPartition U).toReal ≠ 0 :=
    (ENNReal.toReal_pos (ULA.gibbsPartition_pos U hU).ne'
      (gibbsPartition_ne_top_of_probability U)).ne'
  have hcancel : gibbsLebesgueDensity U y *
      ((ULA.gibbsPartition U).toReal * Real.exp (U y)) = 1 := by
    dsimp [gibbsLebesgueDensity]
    calc
      _ = ((ULA.gibbsPartition U).toReal⁻¹ * (ULA.gibbsPartition U).toReal) *
          (Real.exp (-U y) * Real.exp (U y)) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ hZ, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  convert hweighted using 1
  · rfl
  · calc
      _ = (gibbsLebesgueDensity U y *
        ((ULA.gibbsPartition U).toReal * Real.exp (U y))) *
        (boundedLogSlope m (Real.log (interpolationRelativeDensity U μ t y)) *
          interpolationLebesgueDensityTimeDerivative U μ t y) := by rw [hcancel, one_mul]
      _ = _ := by ring

/-- A finite KL divergence identifies the density's entropy integrand with
Mathlib's RN-derivative formula and proves its integrability. -/
theorem integrable_klFun_density_of_finite_kl
    (ν : Measure E) [IsProbabilityMeasure ν] (r : E → ℝ)
    (hr : Measurable r) (hpos : ∀ y, 0 ≤ r y)
    [IsProbabilityMeasure (tiltedMeasure ν r)]
    (hKL : InformationTheory.klDiv (tiltedMeasure ν r) ν ≠ ⊤) :
    Integrable (fun y ↦ InformationTheory.klFun (r y)) ν ∧
      (∫ y, InformationTheory.klFun (r y) ∂ν) =
        (InformationTheory.klDiv (tiltedMeasure ν r) ν).toReal := by
  have hac : tiltedMeasure ν r ≪ ν := withDensity_absolutelyContinuous _ _
  have hrn := Measure.rnDeriv_withDensity ν hr.ennreal_ofReal
  have heq : (fun y ↦ InformationTheory.klFun ((tiltedMeasure ν r).rnDeriv ν y).toReal)
      =ᵐ[ν] fun y ↦ InformationTheory.klFun (r y) := by
    filter_upwards [hrn] with y hy
    simp only [tiltedMeasure, hy, ENNReal.toReal_ofReal (hpos y)]
  have hi := (InformationTheory.integrable_klFun_rnDeriv_iff hac).mpr
    (InformationTheory.klDiv_ne_top_iff.mp hKL).2
  refine ⟨hi.congr heq, ?_⟩
  rw [InformationTheory.toReal_klDiv_eq_integral_klFun hac]
  exact (integral_congr_ae heq).symm

/-- Bounded entropy integrands of the actual interpolation are integrable.
The domination is precisely the finite relative-entropy integrand. -/
theorem interpolation_boundedEntropy_integrable
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) (m : ℕ) :
    Integrable (fun y ↦ boundedEntropy m (interpolationRelativeDensity U μ t y))
      (ULA.gibbsMeasure U) := by
  let : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  let : IsProbabilityMeasure (tiltedMeasure (ULA.gibbsMeasure U)
      (interpolationRelativeDensity U μ t)) :=
    interpolationRelativeDensity_isProbability U μ L hU hLip t ht
  have hpos := interpolationRelativeDensity_pos U μ L hU hLip t ht
  have hKL : InformationTheory.klDiv
      (tiltedMeasure (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t))
        (ULA.gibbsMeasure U) ≠ ⊤ := by
    rw [tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht]
    exact interpolationLaw_klDiv_ne_top U μ α hα L hU hLip hLSI hgrad t ht
  have hi := (integrable_klFun_density_of_finite_kl (ULA.gibbsMeasure U)
    (interpolationRelativeDensity U μ t)
    (interpolationRelativeDensity_measurable U μ L hU hLip t)
    (fun y ↦ (hpos y).le) hKL).1
  have hcont : Continuous (fun y ↦ boundedEntropy m (interpolationRelativeDensity U μ t y)) :=
    continuous_iff_continuousAt.mpr fun y ↦
      (boundedEntropy_hasDerivAt m (hpos y)).continuousAt.comp
        (interpolationRelativeDensity_continuous U μ L hU hLip t ht).continuousAt
  apply hi.mono' hcont.aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (boundedEntropy_nonneg m (hpos y))]
  exact boundedEntropy_le_klFun m (hpos y)

/-- The bounded entropy integrals converge to the actual positive-time KL.
The reference density is identified with its RN derivative before taking the
limit, and the dominating KL integrand is proved integrable. -/
theorem interpolation_boundedEntropy_tendsto
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun m : ℕ ↦ ∫ y,
      boundedEntropy m (interpolationRelativeDensity U μ t y) ∂ULA.gibbsMeasure U)
      atTop (𝓝 ((InformationTheory.klDiv (interpolationLaw U μ t)
        (ULA.gibbsMeasure U)).toReal)) := by
  let : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  let : IsProbabilityMeasure (tiltedMeasure (ULA.gibbsMeasure U)
      (interpolationRelativeDensity U μ t)) :=
    interpolationRelativeDensity_isProbability U μ L hU hLip t ht
  have hpos := interpolationRelativeDensity_pos U μ L hU hLip t ht
  have hKL : InformationTheory.klDiv
      (tiltedMeasure (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t))
        (ULA.gibbsMeasure U) ≠ ⊤ := by
    rw [tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht]
    exact interpolationLaw_klDiv_ne_top U μ α hα L hU hLip hLSI hgrad t ht
  obtain ⟨hi, heq⟩ := integrable_klFun_density_of_finite_kl (ULA.gibbsMeasure U)
    (interpolationRelativeDensity U μ t)
    (interpolationRelativeDensity_measurable U μ L hU hLip t)
    (fun y ↦ (hpos y).le) hKL
  rw [tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht] at heq
  rw [← heq]
  apply tendsto_integral_of_dominated_convergence
    (fun y ↦ InformationTheory.klFun (interpolationRelativeDensity U μ t y))
  · intro m
    exact (interpolation_boundedEntropy_integrable U μ α hα L hU hLip hLSI hgrad t ht m).aestronglyMeasurable
  · exact hi
  · intro m
    exact ae_of_all _ fun y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (boundedEntropy_nonneg m (hpos y))]
      exact boundedEntropy_le_klFun m (hpos y)
  · exact ae_of_all _ fun y ↦ boundedEntropy_tendsto (hpos y)

/-- The actual entropy truncated by the bounded primitive `Φ_m`. -/
def interpolationBoundedEntropy (U : E → ℝ) (μ : Measure E) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ y, boundedEntropy m (interpolationRelativeDensity U μ t y) ∂ULA.gibbsMeasure U

/-- The classical time-chain-rule flux before spatial integration by parts. -/
def interpolationBoundedEntropyFlux (U : E → ℝ) (μ : Measure E) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ y, boundedLogSlope m (Real.log (interpolationRelativeDensity U μ t y)) *
    interpolationLebesgueDensityTimeDerivative U μ t y

/-- The actual bounded log test satisfies all regularity, boundedness and
finite-energy premises of the global Gaussian weak equation. -/
theorem interpolationBoundedLogTest_admissible
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) (m : ℕ) :
    ContDiff ℝ 1 (fun y ↦ boundedLogSlope m (Real.log (interpolationRelativeDensity U μ t y))) ∧
      (∀ y, ‖boundedLogSlope m (Real.log (interpolationRelativeDensity U μ t y))‖ ≤
        (m + 1 : ℝ) * (Real.pi / 2)) ∧
      MemLp (gradient (fun y ↦ boundedLogSlope m
        (Real.log (interpolationRelativeDensity U μ t y)))) 2 (interpolationLaw U μ t) := by
  have hpos := interpolationRelativeDensity_pos U μ L hU hLip t ht
  have hlog := (interpolationRelativeDensity_contDiff U μ L hU hLip t ht).log
    (fun y ↦ (hpos y).ne')
  have hψ : ContDiff ℝ 1 (fun y ↦ boundedLogSlope m
      (Real.log (interpolationRelativeDensity U μ t y))) :=
    ((boundedLogSlope_contDiff m).of_le (by simp)).comp hlog
  refine ⟨hψ, fun y ↦ norm_boundedLogSlope_le_const m _, ?_⟩
  have hm : AEStronglyMeasurable (gradient (fun y ↦ boundedLogSlope m
      (Real.log (interpolationRelativeDensity U μ t y)))) (interpolationLaw U μ t) := by
    exact ((InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hψ.continuous_fderiv (by norm_num))).aestronglyMeasurable
  apply (interpolationRelativeScore_memLp U μ L hU hLip hgrad t ht).of_le hm
  exact ae_of_all _ fun y ↦ norm_gradient_boundedLogSlope_comp_le m _ y
    (hlog.differentiable (by norm_num) y)

/-- The bounded entropy flux is the exact spatial Gaussian flux paired with
the weighted relative score. The global weak equation applies to the actual
bounded log test, with all its admissibility conditions already proved. -/
theorem interpolationBoundedEntropyFlux_eq_joint
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) (m : ℕ) :
    interpolationBoundedEntropyFlux U μ m t =
      -(∫ z : E × E,
        realGaussianKernel (1 / (4 * t)) (z.1 - t • gradient U z.1) z.2 *
          boundedLogWeight m (Real.log (interpolationRelativeDensity U μ t z.2)) *
          inner ℝ (gradient U z.1 - (1 / (2 * t)) •
            (z.2 - (z.1 - t • gradient U z.1)))
            (interpolationRelativeScoreField U μ t z.2) ∂μ.prod volume) := by
  obtain ⟨hψ, hM, hψgrad⟩ := interpolationBoundedLogTest_admissible U μ L hU hLip hgrad t ht m
  have hw := interpolationLebesgueDensity_weak_identity U μ L hLip hgrad t ht
    (fun y ↦ boundedLogSlope m (Real.log (interpolationRelativeDensity U μ t y)))
    hψ ((m + 1 : ℝ) * (Real.pi / 2)) hM hψgrad
  calc
    _ = ∫ y, interpolationLebesgueDensityTimeDerivative U μ t y *
        boundedLogSlope m (Real.log (interpolationRelativeDensity U μ t y)) := by
      unfold interpolationBoundedEntropyFlux
      apply integral_congr_ae
      exact ae_of_all _ fun _ ↦ mul_comm _ _
    _ = _ := hw
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      have hpos := interpolationRelativeDensity_pos U μ L hU hLip t ht
      have hlog := (interpolationRelativeDensity_contDiff U μ L hU hLip t ht).log
        (fun y ↦ (hpos y).ne')
      rw [gradient_boundedLogSlope_comp m _ z.2 (hlog.differentiable (by norm_num) z.2),
        ← interpolationRelativeScoreField_eq U μ L hU hLip t ht z.2,
        frozenGaussianFlux, real_inner_smul_left, real_inner_smul_right]
      ring

/-- The bounded entropy of the actual Gaussian interpolation obeys the full
time chain rule on every positive-time interval. All spacetime integrability
is proved from the initial score moment and the Gaussian kernel. -/
theorem interpolationBoundedEntropy_time_chain_rule
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hgrad : MemLp (gradient U) 2 μ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (m : ℕ) :
    (interpolationBoundedEntropy U μ m b - interpolationBoundedEntropy U μ m a =
      ∫ t in a..b, interpolationBoundedEntropyFlux U μ m t) ∧
      AbsolutelyContinuousOnInterval (interpolationBoundedEntropy U μ m) a b ∧
      ∀ᵐ t ∂volume, t ∈ Ioo a b →
        HasDerivAt (interpolationBoundedEntropy U μ m)
          (interpolationBoundedEntropyFlux U μ m t) t := by
  let : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  have hG := hgrad.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  let f : ℝ → E → ℝ := fun t y ↦ gibbsLebesgueDensity U y *
    boundedEntropy m (interpolationRelativeDensity U μ t y)
  let fdot : ℝ → E → ℝ := fun t y ↦
    boundedLogSlope m (Real.log (interpolationRelativeDensity U μ t y)) *
      interpolationLebesgueDensityTimeDerivative U μ t y
  have hJ : Measurable (gibbsLebesgueDensity U) := by
    have hUc := hU.continuous
    unfold gibbsLebesgueDensity
    fun_prop
  have hfa : Integrable (f a) volume := by
    have hi := interpolation_boundedEntropy_integrable U μ α hα L hU hLip hLSI hgrad a ha m
    rw [gibbsMeasure_eq_withDensity_real U hU] at hi
    have hh := (integrable_withDensity_iff_integrable_smul' hJ.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hi
    simpa only [ENNReal.toReal_ofReal (gibbsLebesgueDensity_pos U hU _).le, smul_eq_mul]
      using hh
  have hpDot := integrable_interpolationLebesgueDensityTimeDerivative_spacetime U μ L hLip hG a b ha
  have hpDot' : Integrable (fun p : ℝ × E ↦
      interpolationLebesgueDensityTimeDerivative U μ p.1 p.2)
      ((volume.restrict (Ioc a b)).prod volume) := by
    exact hpDot.mono_measure (Measure.prod_mono
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) le_rfl)
  have hχ : Measurable (fun p : ℝ × E ↦
      boundedLogSlope m (Real.log (interpolationRelativeDensity U μ p.1 p.2))) :=
    (boundedLogSlope_contDiff m).continuous.measurable.comp
      (interpolationRelativeDensity_joint_measurable U μ L hU hLip).log
  have hdot : Integrable (fun p : ℝ × E ↦ fdot p.1 p.2)
      ((volume.restrict (Ioc a b)).prod volume) :=
    hpDot'.bdd_mul hχ.aestronglyMeasurable
      (ae_of_all _ fun p ↦ norm_boundedLogSlope_le_const m _)
  have hderiv : ∀ᵐ y ∂(volume : Measure E), ∀ t ∈ Icc a b,
      HasDerivAt (fun u ↦ f u y) (fdot t y) t := by
    exact ae_of_all _ fun y t ht ↦
      hasDerivAt_weighted_boundedEntropy U μ L hU hLip hG t (ha.trans_le ht.1) m y
  have hweight (t : ℝ) : (∫ y, f t y) = interpolationBoundedEntropy U μ m t := by
    rw [interpolationBoundedEntropy, ULA.integral_gibbs_eq_weighted U hU]
    dsimp [f, gibbsLebesgueDensity]
    simp only [ENNReal.toReal_inv]
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  have hfun : (fun t ↦ ∫ y, f t y) = interpolationBoundedEntropy U μ m := funext hweight
  have hFTC := (integral_eq_initial_add_integral_of_spacetime_integrable volume f fdot
    a b hab hfa hdot hderiv).2
  rw [hweight b, hweight a] at hFTC
  have hAC := (absolutelyContinuous_integral_of_spacetime_integrable volume f fdot
    a b hab hfa hdot hderiv).2
  rw [hfun] at hAC
  have hAE := integral_hasDerivAt_ae_of_spacetime_integrable volume f fdot
    a b hab hfa hdot hderiv
  rw [hfun] at hAE
  exact ⟨by dsimp [interpolationBoundedEntropyFlux, fdot]; linarith, hAC, hAE⟩

/-- The frozen Gaussian velocity, expressed on the original independent
initial-state/noise probability space. -/
def frozenGaussianVelocityField (U : E → ℝ) (t : ℝ) (p : E × E) : E :=
  gradient U p.1 - ((1 / (2 * t)) * Real.sqrt (2 * t)) • p.2

/-- The actual relative score evaluated at the independent Gaussian update. -/
def interpolationScoreAlongUpdate (U : E → ℝ) (μ : Measure E) (t : ℝ) (p : E × E) : E :=
  interpolationRelativeScoreField U μ t (ULA.malaProposal U t p.1 p.2)

/-- The untruncated entropy flux on a single fixed probability space. -/
def interpolationRawEntropyFlux (U : E → ℝ) (μ : Measure E) (t : ℝ) : ℝ :=
  -(∫ p : E × E, inner ℝ (frozenGaussianVelocityField U t p)
    (interpolationScoreAlongUpdate U μ t p) ∂μ.prod (stdGaussian E))

theorem frozenGaussianVelocityField_memLp
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) :
    MemLp (frozenGaussianVelocityField U t) 2 (μ.prod (stdGaussian E)) := by
  have hz : MemLp (fun z : E ↦ z) 2 (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)
  convert (hgrad.comp_fst (stdGaussian E)).sub
    ((hz.comp_snd μ).const_smul ((1 / (2 * t)) * Real.sqrt (2 * t))) using 1
  funext p
  rfl

theorem interpolationScoreAlongUpdate_memLp
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    MemLp (interpolationScoreAlongUpdate U μ t) 2 (μ.prod (stdGaussian E)) := by
  have hs : MemLp (interpolationRelativeScoreField U μ t) 2 (interpolationLaw U μ t) := by
    convert interpolationRelativeScore_memLp U μ L hU hLip hgrad t ht using 1
    funext y
    exact interpolationRelativeScoreField_eq U μ L hU hLip t ht y
  exact (memLp_map_measure_iff hs.aestronglyMeasurable
    (ULA.malaProposal_measurable U t L hLip).aemeasurable).mp hs

theorem frozenGaussianVelocityField_energy
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    (∫ p : E × E, ‖frozenGaussianVelocityField U t p‖ ^ 2 ∂μ.prod (stdGaussian E)) =
      (∫ x, ‖gradient U x‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * t) := by
  have heq (p : E × E) : frozenGaussianVelocityField U t p =
      (1 : ℝ) • gradient U p.1 +
        (-((1 / (2 * t)) * Real.sqrt (2 * t))) • p.2 := by
    simp [frozenGaussianVelocityField, sub_eq_add_neg]
  simp_rw [heq]
  rw [integral_norm_sq_affine_stdGaussian μ (gradient U) hgrad]
  simp only [one_pow, one_mul, neg_sq]
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * t)]
  field_simp

/-- The bounded spatial flux is an expectation on the original independent
Gaussian space. This identifies its limit without any logarithmic bound on
the mixture's time derivative. -/
theorem interpolationBoundedEntropyFlux_eq_raw_weighted
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) (m : ℕ) :
    interpolationBoundedEntropyFlux U μ m t =
      -(∫ p : E × E, boundedLogWeight m (Real.log (interpolationRelativeDensity U μ t
          (ULA.malaProposal U t p.1 p.2))) *
        inner ℝ (frozenGaussianVelocityField U t p)
          (interpolationScoreAlongUpdate U μ t p) ∂μ.prod (stdGaussian E)) := by
  let T : E × E → E × E := fun p ↦ (p.1, ULA.malaProposal U t p.1 p.2)
  let K : E × E → ℝ := fun z ↦ realGaussianKernel (1 / (4 * t))
    (z.1 - t • gradient U z.1) z.2
  let F : E × E → ℝ := fun z ↦
    boundedLogWeight m (Real.log (interpolationRelativeDensity U μ t z.2)) *
      inner ℝ (gradient U z.1 - (1 / (2 * t)) •
        (z.2 - (z.1 - t • gradient U z.1))) (interpolationRelativeScoreField U μ t z.2)
  have hT : Measurable T := measurable_fst.prodMk (ULA.malaProposal_measurable U t L hLip)
  have hS : Measurable (interpolationRelativeScoreField U μ t) :=
    ((interpolationRelativeScoreField_stronglyMeasurable U μ L hLip).comp_measurable
      (measurable_const.prodMk measurable_id)).measurable
  have hr := interpolationRelativeDensity_measurable U μ L hU hLip t
  have hg := hLip.continuous.measurable
  have hF : StronglyMeasurable F := by
    unfold F boundedLogWeight
    fun_prop
  have hK : Measurable K := by
    unfold K realGaussianKernel
    fun_prop
  have hKpos (z : E × E) : 0 ≤ K z := by
    have hN := ULA.radialGaussianNormalizer_pos (H := E) (1 / (4 * t)) (by positivity)
    dsimp [K, realGaussianKernel]
    positivity
  have hchange : (∫ z, K z * F z ∂μ.prod volume) =
      ∫ z, F z ∂(μ.prod (stdGaussian E)).map T := by
    rw [frozenGaussianJointLaw_eq_density U μ L hLip t ht,
      integral_withDensity_eq_integral_toReal_smul hK.ennreal_ofReal
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hKpos _), smul_eq_mul]
  rw [interpolationBoundedEntropyFlux_eq_joint U μ L hU hLip hgrad t ht m]
  congr 1
  calc
    _ = ∫ z, K z * F z ∂μ.prod volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun z ↦ by dsimp [K, F]; ring
    _ = _ := hchange
    _ = ∫ p, F (T p) ∂μ.prod (stdGaussian E) := integral_map_of_stronglyMeasurable hT hF
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      dsimp [F, T, frozenGaussianVelocityField, interpolationScoreAlongUpdate]
      simp only [ULA.malaProposal, add_sub_cancel_left, smul_smul]

/-- Bounded entropy flux converges pointwise at positive time to the actual
raw entropy flux, by square integrability of its two Gaussian factors. -/
theorem interpolationBoundedEntropyFlux_tendsto
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun m : ℕ ↦ interpolationBoundedEntropyFlux U μ m t) atTop
      (𝓝 (interpolationRawEntropyFlux U μ t)) := by
  have hi : Integrable (fun p : E × E ↦ inner ℝ (frozenGaussianVelocityField U t p)
      (interpolationScoreAlongUpdate U μ t p)) (μ.prod (stdGaussian E)) :=
    integrable_inner_of_memLp_two _ _ _ (frozenGaussianVelocityField_memLp U μ hgrad t)
      (interpolationScoreAlongUpdate_memLp U μ L hU hLip hgrad t ht)
  have hz : Measurable (fun p : E × E ↦ Real.log (interpolationRelativeDensity U μ t
      (ULA.malaProposal U t p.1 p.2))) :=
    (interpolationRelativeDensity_measurable U μ L hU hLip t).log.comp
      (ULA.malaProposal_measurable U t L hLip)
  have hd := (boundedLogWeight_integral_tendsto (μ.prod (stdGaussian E)) _ _ hz hi).neg
  simpa only [← interpolationBoundedEntropyFlux_eq_raw_weighted U μ L hU hLip hgrad t ht,
    interpolationRawEntropyFlux] using hd

/-- Fisher energy represented under the fixed Gibbs measure. -/
def interpolationRelativeFisherEnergy (U : E → ℝ) (μ : Measure E) (t : ℝ) : ℝ :=
  ∫ y, interpolationRelativeDensity U μ t y *
    ‖interpolationRelativeScoreField U μ t y‖ ^ 2 ∂ULA.gibbsMeasure U

theorem interpolationScoreAlongUpdate_energy
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    (∫ p : E × E, ‖interpolationScoreAlongUpdate U μ t p‖ ^ 2 ∂μ.prod (stdGaussian E)) =
      interpolationRelativeFisherEnergy U μ t := by
  have hm : StronglyMeasurable (fun y : E ↦ ‖interpolationRelativeScoreField U μ t y‖ ^ 2) :=
    ((interpolationRelativeScoreField_stronglyMeasurable U μ L hLip).comp_measurable
      (measurable_const.prodMk measurable_id)).norm.pow 2
  rw [interpolationRelativeFisherEnergy,
    (interpolationRelativeScoreField_weighted_energy U μ L hU hLip
      (hgrad.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)) t ht).2]
  exact (integral_map_of_stronglyMeasurable
    (ULA.malaProposal_measurable U t L hLip) hm).symm

/-- Uniform-in-truncation control of the entropy flux by Gaussian velocity
and relative Fisher energies. This provides the time-DCT majorant. -/
theorem norm_interpolationBoundedEntropyFlux_le
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) (m : ℕ) :
    ‖interpolationBoundedEntropyFlux U μ m t‖ ≤
      ((∫ x, ‖gradient U x‖ ^ 2 ∂μ) + (Module.finrank ℝ E : ℝ) / (2 * t) +
        interpolationRelativeFisherEnergy U μ t) / 2 := by
  let P := μ.prod (stdGaussian E)
  let V := frozenGaussianVelocityField U t
  let S := interpolationScoreAlongUpdate U μ t
  let w : E × E → ℝ := fun p ↦ boundedLogWeight m (Real.log (interpolationRelativeDensity U μ t
    (ULA.malaProposal U t p.1 p.2)))
  have hV := frozenGaussianVelocityField_memLp U μ hgrad t
  have hS := interpolationScoreAlongUpdate_memLp U μ L hU hLip hgrad t ht
  have hwm : Measurable w := by
    have hr := (interpolationRelativeDensity_measurable U μ L hU hLip t).log.comp
      (ULA.malaProposal_measurable U t L hLip)
    unfold w boundedLogWeight
    fun_prop
  have hwn (p : E × E) : ‖w p‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (boundedLogWeight_nonneg m _)]
    exact boundedLogWeight_le_one m _
  have hi := (integrable_inner_of_memLp_two P V S hV hS).bdd_mul
    hwm.aestronglyMeasurable (ae_of_all _ hwn)
  have hiV := hV.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiS := hS.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hmajor : Integrable (fun p : E × E ↦ (‖V p‖ ^ 2 + ‖S p‖ ^ 2) / 2) P :=
    (hiV.add hiS).div_const 2
  have hpoint (p : E × E) : ‖w p * inner ℝ (V p) (S p)‖ ≤
      (‖V p‖ ^ 2 + ‖S p‖ ^ 2) / 2 := by
    have hp := norm_inner_le_norm (𝕜 := ℝ) (V p) (S p)
    have hw := mul_le_of_le_one_left (norm_nonneg (inner ℝ (V p) (S p))) (hwn p)
    rw [norm_mul]
    nlinarith [sq_nonneg (‖V p‖ - ‖S p‖)]
  have hb := (norm_integral_le_integral_norm (f := fun p ↦ w p * inner ℝ (V p) (S p))).trans
    (integral_mono hi.norm hmajor hpoint)
  rw [integral_div, integral_add hiV hiS] at hb
  rw [interpolationBoundedEntropyFlux_eq_raw_weighted U μ L hU hLip hgrad t ht m, norm_neg]
  change ‖∫ p, w p * inner ℝ (V p) (S p) ∂P‖ ≤ _
  rw [← frozenGaussianVelocityField_energy U μ hgrad t ht,
    ← interpolationScoreAlongUpdate_energy U μ L hU hLip hgrad t ht]
  exact hb

theorem interpolationBoundedEntropyFlux_measurable
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) (m : ℕ) :
    Measurable (interpolationBoundedEntropyFlux U μ m) := by
  have hχ := (boundedLogSlope_contDiff m).continuous.measurable.comp
    (interpolationRelativeDensity_joint_measurable U μ L hU hLip).log
  have hh := hχ.mul (interpolationLebesgueDensityTimeDerivative_measurable U μ L hLip)
  exact hh.stronglyMeasurable.integral_prod_right.measurable

theorem interpolationRawEntropyFlux_measurable
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U)) :
    Measurable (interpolationRawEntropyFlux U μ) := by
  have hg := hLip.continuous.measurable
  have hY : Measurable (fun p : ℝ × (E × E) ↦
      (p.1, ULA.malaProposal U p.1 p.2.1 p.2.2)) := by
    unfold ULA.malaProposal
    fun_prop
  have hS := (interpolationRelativeScoreField_stronglyMeasurable U μ L hLip).comp_measurable hY
  have hV : StronglyMeasurable (fun p : ℝ × (E × E) ↦ frozenGaussianVelocityField U p.1 p.2) := by
    unfold frozenGaussianVelocityField
    fun_prop
  exact (hV.inner hS).integral_prod_right.neg.measurable

/-- On a compact positive-time interval, one integrable scalar function
dominates every bounded entropy flux and its untruncated limit. -/
theorem interpolation_entropy_flux_time_domination
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (hgrad : MemLp (gradient U) 2 μ) (a b : ℝ) (ha : 0 < a) :
    ∃ D : ℝ → ℝ, Integrable D (volume.restrict (Ioc a b)) ∧
      (∀ m, ∀ᵐ t ∂volume.restrict (Ioc a b),
        ‖interpolationBoundedEntropyFlux U μ m t‖ ≤ D t) ∧
      ∀ᵐ t ∂volume.restrict (Ioc a b), ‖interpolationRawEntropyFlux U μ t‖ ≤ D t := by
  let G := ∫ x, ‖gradient U x‖ ^ 2 ∂μ
  let D : ℝ → ℝ := fun t ↦ (G + (Module.finrank ℝ E : ℝ) / (2 * a) +
    interpolationRelativeFisherEnergy U μ t) / 2
  have hG := hgrad.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hI : Integrable (interpolationRelativeFisherEnergy U μ) (volume.restrict (Ioc a b)) :=
    (integrable_interpolationRelativeScoreField_energy_spacetime U μ L hU hLip hG a b ha)
      |>.integral_prod_left.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hD : Integrable D (volume.restrict (Ioc a b)) :=
    ((integrable_const (G + (Module.finrank ℝ E : ℝ) / (2 * a))).add hI).div_const 2
  have hpoint (m : ℕ) (t : ℝ) (ht : t ∈ Ioc a b) :
      ‖interpolationBoundedEntropyFlux U μ m t‖ ≤ D t := by
    have htpos := ha.trans ht.1
    apply (norm_interpolationBoundedEntropyFlux_le U μ L hU hLip hgrad t htpos m).trans
    dsimp [D, G]
    gcongr
    exact ht.1.le
  refine ⟨D, hD, fun m ↦ ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hpoint m t ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hlim := (interpolationBoundedEntropyFlux_tendsto U μ L hU hLip hgrad t (ha.trans ht.1)).norm
    exact le_of_tendsto hlim (Eventually.of_forall fun m ↦ hpoint m t ht)

/-- The actual KL entropy of the frozen Gaussian interpolation. -/
def actualInterpolationEntropy (U : E → ℝ) (μ : Measure E) (t : ℝ) : ℝ :=
  (InformationTheory.klDiv (interpolationLaw U μ t) (ULA.gibbsMeasure U)).toReal

/-- The complete finite-entropy identity on a positive-time interval follows
by the two dominated limits of the bounded entropy time chain rule. -/
theorem interpolationEntropy_integral_identity
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hgrad : MemLp (gradient U) 2 μ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    actualInterpolationEntropy U μ b - actualInterpolationEntropy U μ a =
      ∫ t in a..b, interpolationRawEntropyFlux U μ t := by
  let : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  obtain ⟨D, hD, hdom, _⟩ := interpolation_entropy_flux_time_domination U μ L hU hLip hgrad a b ha
  rw [intervalIntegral.integral_of_le hab]
  apply integral_identity_of_dominated_limits (volume.restrict (Ioc a b))
    (fun m ↦ interpolationBoundedEntropy U μ m a)
    (fun m ↦ interpolationBoundedEntropy U μ m b)
    (actualInterpolationEntropy U μ a) (actualInterpolationEntropy U μ b)
    (fun m t ↦ interpolationBoundedEntropyFlux U μ m t)
    (interpolationRawEntropyFlux U μ) D
  · intro m
    have h := (interpolationBoundedEntropy_time_chain_rule U μ α hα L hU hLip hLSI hgrad a b ha hab m).1
    rwa [intervalIntegral.integral_of_le hab] at h
  · exact interpolation_boundedEntropy_tendsto U μ α hα L hU hLip hLSI hgrad a ha
  · exact interpolation_boundedEntropy_tendsto U μ α hα L hU hLip hLSI hgrad b (ha.trans_le hab)
  · intro m
    exact (interpolationBoundedEntropyFlux_measurable U μ L hU hLip m).aestronglyMeasurable
  · exact hD
  · exact hdom
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact interpolationBoundedEntropyFlux_tendsto U μ L hU hLip hgrad t (ha.trans ht.1)

/-- The actual interpolation entropy is absolutely continuous on every
positive-time interval, and its derivative is the actual Gaussian flux a.e.
All density, admissibility and spacetime integrability inputs are derived. -/
theorem interpolationEntropy_local_chain_rule
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hgrad : MemLp (gradient U) 2 μ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (actualInterpolationEntropy U μ) a b ∧
      ∀ᵐ t ∂volume, t ∈ Ioo a b →
        HasDerivAt (actualInterpolationEntropy U μ) (interpolationRawEntropyFlux U μ t) t := by
  let : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  obtain ⟨D, hD, _, hraw⟩ := interpolation_entropy_flux_time_domination U μ L hU hLip hgrad a b ha
  have hq : IntervalIntegrable (interpolationRawEntropyFlux U μ) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hD.mono' (interpolationRawEntropyFlux_measurable U μ L hLip).aestronglyMeasurable hraw
  apply regularity_of_integral_identity _ _ a b hab hq
  intro t ht
  have h := interpolationEntropy_integral_identity U μ α hα L hU hLip hLSI hgrad a t ha ht.1
  linarith

end ULA.LSI
