import LatentDiffusion.Density
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false

/-!
# Differentiating the actual evidence and centering posterior scores

The normalizer is the actual integral of `exp (-U)`. Common-neighborhood
domination proves its derivative, and normalization identifies the derivative
of its logarithm with the actual posterior mean score. At an evidence
maximizer the average posterior parameter gradient therefore vanishes.
Neither a zero-score condition nor an evidence derivative is assumed.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace LatentDiffusion.RegularEvidence

variable {A Z : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [CompleteSpace A] [MeasurableSpace Z]

def normalizer (ν : Measure Z) (U : A → Z → ℝ) (a : A) : ℝ :=
  ∫ z, Real.exp (-U a z) ∂ν

def posterior (ν : Measure Z) (U : A → Z → ℝ) (a : A) : Measure Z :=
  Density.posteriorMeasure ν (fun z ↦ Real.exp (-U a z)) (normalizer ν U a)

def unnormalizedScore (ν : Measure Z) (U : A → Z → ℝ) (a : A) : A :=
  ∫ z, Real.exp (-U a z) • gradient (fun b ↦ U b z) a ∂ν

def posteriorScore (ν : Measure Z) (U : A → Z → ℝ) (a : A) : A :=
  ∫ z, gradient (fun b ↦ U b z) a ∂posterior ν U a

/-- Added normalizer regularity consists only of ordinary measurability,
integrability and differentiation domination on one common neighborhood. -/
structure LocalNormalizerRegularity (ν : Measure Z) (U : A → Z → ℝ) (a : A) where
  neighborhood : Set A
  neighborhood_mem : neighborhood ∈ 𝓝 a
  bound : Z → ℝ
  measurable : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (fun z ↦ Real.exp (-U b z)) ν
  density_integrable : Integrable (fun z ↦ Real.exp (-U a z)) ν
  gradient_measurable : AEStronglyMeasurable
    (fun z ↦ Real.exp (-U a z) • gradient (fun b ↦ U b z) a) ν
  derivative_bound : ∀ᵐ z ∂ν, ∀ b ∈ neighborhood,
    Real.exp (-U b z) * ‖gradient (fun c ↦ U c z) b‖ ≤ bound z
  bound_integrable : Integrable bound ν
  differentiable : ∀ᵐ z ∂ν, ∀ b ∈ neighborhood,
    DifferentiableAt ℝ (fun c ↦ U c z) b

theorem LocalNormalizerRegularity.weighted_gradient_integrable
    {ν : Measure Z} {U : A → Z → ℝ} {a : A}
    (data : LocalNormalizerRegularity ν U a) :
    Integrable (fun z ↦ Real.exp (-U a z) • gradient (fun b ↦ U b z) a) ν := by
  apply data.bound_integrable.mono' data.gradient_measurable
  filter_upwards [data.derivative_bound] with z hz
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    hz a (mem_of_mem_nhds data.neighborhood_mem)

/-- The actual normalizing integral has the derivative obtained by
differentiating its positive density under the integral sign. -/
theorem normalizer_hasFDerivAt
    (ν : Measure Z) (U : A → Z → ℝ) (a : A)
    (data : LocalNormalizerRegularity ν U a) :
    HasFDerivAt (normalizer ν U)
      (-(InnerProductSpace.toDual ℝ A) (unnormalizedScore ν U a)) a := by
  let D : A → Z → A →L[ℝ] ℝ := fun b z ↦
    -(InnerProductSpace.toDual ℝ A)
      (Real.exp (-U b z) • gradient (fun c ↦ U c z) b)
  have hmeas : AEStronglyMeasurable (D a) ν := by
    exact ((InnerProductSpace.toDual ℝ A).continuous.comp_aestronglyMeasurable
      data.gradient_measurable).neg
  have hd : HasFDerivAt (normalizer ν U) (∫ z, D a z ∂ν) a := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun b z ↦ Real.exp (-U b z)) (F' := D) data.neighborhood_mem
      data.measurable data.density_integrable hmeas
    · filter_upwards [data.derivative_bound] with z hz b hb
      simpa only [D, norm_neg, LinearIsometryEquiv.norm_map, norm_smul,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hz b hb
    · exact data.bound_integrable
    · filter_upwards [data.differentiable] with z hz b hb
      have h := (hz b hb).hasFDerivAt.neg.exp
      convert h using 1
      simp [D, gradient]
  have heq : (∫ z, D a z ∂ν) =
      -(InnerProductSpace.toDual ℝ A) (unnormalizedScore ν U a) := by
    rw [show (fun z ↦ D a z) = (fun z ↦
      -((InnerProductSpace.toDual ℝ A).toContinuousLinearEquiv.toContinuousLinearMap
        (Real.exp (-U a z) • gradient (fun b ↦ U b z) a))) from rfl]
    rw [integral_neg, ContinuousLinearMap.integral_comp_comm
      (InnerProductSpace.toDual ℝ A).toContinuousLinearEquiv.toContinuousLinearMap
        data.weighted_gradient_integrable]
    rfl
  rwa [heq] at hd

omit [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A] in
theorem posterior_isProbability
    (ν : Measure Z) (U : A → Z → ℝ) (a : A)
    (hint : Integrable (fun z ↦ Real.exp (-U a z)) ν)
    (hZ : 0 < normalizer ν U a) : IsProbabilityMeasure (posterior ν U a) :=
  Density.posteriorMeasure_isProbability ν _ _ (fun _ ↦ (Real.exp_pos _).le) hZ hint rfl

/-- The posterior mean gradient is an absolutely integrable actual score. -/
theorem posterior_gradient_integrable
    (ν : Measure Z) (U : A → Z → ℝ) (a : A)
    (data : LocalNormalizerRegularity ν U a)
    (hmeas : Measurable (fun z ↦ Real.exp (-U a z)))
    (hZ : 0 < normalizer ν U a) :
    Integrable (fun z ↦ gradient (fun b ↦ U b z) a) (posterior ν U a) := by
  unfold posterior Density.posteriorMeasure Density.densityMeasure
  rw [integrable_withDensity_iff_integrable_smul' (hmeas.div_const _).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_nonneg _) hZ.le),
    div_eq_inv_mul, mul_smul]
  exact data.weighted_gradient_integrable.smul ((normalizer ν U a)⁻¹)

/-- Normalizing the actual density normalizes its integral gradient. -/
theorem posteriorScore_eq
    (ν : Measure Z) (U : A → Z → ℝ) (a : A)
    (hmeas : Measurable (fun z ↦ Real.exp (-U a z)))
    (hZ : 0 < normalizer ν U a) :
    posteriorScore ν U a = (normalizer ν U a)⁻¹ • unnormalizedScore ν U a := by
  unfold posteriorScore posterior Density.posteriorMeasure Density.densityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (hmeas.div_const _).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (Real.exp_nonneg _) hZ.le),
    div_eq_inv_mul, mul_smul]
  rw [integral_smul]
  rfl

/-- The logarithm of the actual normalizer has derivative minus the actual
posterior mean parameter gradient. -/
theorem log_normalizer_hasFDerivAt
    (ν : Measure Z) (U : A → Z → ℝ) (a : A)
    (data : LocalNormalizerRegularity ν U a)
    (hmeas : Measurable (fun z ↦ Real.exp (-U a z)))
    (hZ : 0 < normalizer ν U a) :
    HasFDerivAt (fun b ↦ Real.log (normalizer ν U b))
      (-(InnerProductSpace.toDual ℝ A) (posteriorScore ν U a)) a := by
  have h := (normalizer_hasFDerivAt ν U a data).log hZ.ne'
  rw [posteriorScore_eq ν U a hmeas hZ]
  simpa only [map_smul, smul_neg] using h

def logEvidence {M : ℕ} (ν : Measure Z) (U : Fin M → A → Z → ℝ) (a : A) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i, Real.log (normalizer ν (U i) a)

def averagedPosteriorScore {M : ℕ} (ν : Measure Z) (U : Fin M → A → Z → ℝ)
    (a : A) : A := (M : ℝ)⁻¹ • ∑ i, posteriorScore ν (U i) a

/-- The full evidence derivative is computed from the actual integrals. -/
theorem logEvidence_hasFDerivAt {M : ℕ}
    (ν : Measure Z) (U : Fin M → A → Z → ℝ) (a : A)
    (data : ∀ i, LocalNormalizerRegularity ν (U i) a)
    (hmeas : ∀ i, Measurable (fun z ↦ Real.exp (-U i a z)))
    (hZ : ∀ i, 0 < normalizer ν (U i) a) :
    HasFDerivAt (logEvidence ν U)
      (-(InnerProductSpace.toDual ℝ A) (averagedPosteriorScore ν U a)) a := by
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦
    log_normalizer_hasFDerivAt ν (U i) a (data i) (hmeas i) (hZ i))).const_mul ((M : ℝ)⁻¹)
  convert h using 1
  · rfl
  · simp only [averagedPosteriorScore, map_smul, map_sum,
      Finset.sum_neg_distrib, smul_neg]

/-- At an actual evidence maximum the average posterior parameter gradient
vanishes. This discharges the optimizer-centering condition from evidence
optimality and ordinary dominated differentiation. -/
theorem averaged_posterior_parameter_gradient_eq_zero {M : ℕ}
    (ν : Measure Z) (U : Fin M → A → Z → ℝ) (a : A)
    (data : ∀ i, LocalNormalizerRegularity ν (U i) a)
    (hmeas : ∀ i, Measurable (fun z ↦ Real.exp (-U i a z)))
    (hZ : ∀ i, 0 < normalizer ν (U i) a)
    (hmax : IsLocalMax (logEvidence ν U) a) :
    averagedPosteriorScore ν U a = 0 := by
  have hz := hmax.hasFDerivAt_eq_zero (logEvidence_hasFDerivAt ν U a data hmeas hZ)
  apply (InnerProductSpace.toDual ℝ A).injective
  simpa only [map_zero, neg_eq_zero] using hz

theorem sum_posterior_parameter_gradient_eq_zero {M : ℕ} (hM : 0 < M)
    (ν : Measure Z) (U : Fin M → A → Z → ℝ) (a : A)
    (data : ∀ i, LocalNormalizerRegularity ν (U i) a)
    (hmeas : ∀ i, Measurable (fun z ↦ Real.exp (-U i a z)))
    (hZ : ∀ i, 0 < normalizer ν (U i) a)
    (hmax : IsLocalMax (logEvidence ν U) a) :
    ∑ i, (∫ z, gradient (fun b ↦ U i b z) a ∂posterior ν (U i) a) = 0 := by
  have h := averaged_posterior_parameter_gradient_eq_zero ν U a data hmeas hZ hmax
  exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero (Nat.cast_ne_zero.mpr hM.ne'))

end LatentDiffusion.RegularEvidence
