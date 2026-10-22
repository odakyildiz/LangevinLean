import UnadjustedLangevin.LSI.EntropyMoment
import UnadjustedLangevin.LSI.ULALaw
import UnadjustedLangevin.LSI.GaussianDrift
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing

set_option linter.style.header false

/-! # Entropy comparison at the initial endpoint

Data processing controls entropy against the simultaneously evolved target.
A pointwise upper bound on that target's relative density changes the reference
back to the Gibbs law. The change-of-reference result proves finiteness of the
new entropy internally, using only a one-sided density estimate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA.LSI

variable {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- Adjoining the same independent probability innovation preserves KL exactly. -/
theorem klDiv_prod_same_right (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (η : Measure Ξ) [IsProbabilityMeasure η] :
    InformationTheory.klDiv (μ.prod η) (ν.prod η) = InformationTheory.klDiv μ ν := by
  simpa only [Measure.compProd_const] using
    InformationTheory.klDiv_compProd_left μ ν (Kernel.const Ω η)

/-- The logarithm of the Radon–Nikodym chain rule, on the law being integrated. -/
theorem llr_eq_add_of_absolutelyContinuous
    (μ ρ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ν] (hμρ : μ ≪ ρ) (hρν : ρ ≪ ν) :
    llr μ ν =ᵐ[μ] fun x ↦ llr μ ρ x + llr ρ ν x := by
  have hμν := hμρ.trans hρν
  filter_upwards [hμν.ae_le (Measure.rnDeriv_mul_rnDeriv hμρ),
    Measure.rnDeriv_pos hμρ, hμρ.ae_le (Measure.rnDeriv_pos hρν),
    hμρ.ae_le (Measure.rnDeriv_lt_top μ ρ),
    hμν.ae_le (Measure.rnDeriv_lt_top ρ ν)] with x hx hp hq ht hu
  simp only [Pi.mul_apply] at hx
  dsimp [llr]
  rw [← hx, ENNReal.toReal_mul, Real.log_mul]
  · exact ENNReal.toReal_ne_zero.mpr ⟨hp.ne', ht.ne⟩
  · exact ENNReal.toReal_ne_zero.mpr ⟨hq.ne', hu.ne⟩

/-- The negative exponential of an absolutely-continuous log likelihood is
integrable even when its KL divergence has not yet been shown finite. -/
theorem integrable_exp_neg_llr
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) : Integrable (fun x ↦ Real.exp (-llr μ ν x)) μ := by
  exact Measure.integrable_toReal_rnDeriv.congr (exp_neg_llr hμν).symm

/-- A measurable log likelihood with an integrable upper bound is integrable.
The negative tail is controlled by the always-integrable reciprocal likelihood. -/
theorem integrable_llr_of_integrable_upper_bound
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (b : Ω → ℝ) (hb : Integrable b μ)
    (hbound : ∀ᵐ x ∂μ, llr μ ν x ≤ b x) : Integrable (llr μ ν) μ := by
  apply (hb.norm.add (integrable_exp_neg_llr μ ν hμν)).mono' (by fun_prop)
  filter_upwards [hbound] with x hx
  rw [Real.norm_eq_abs]
  by_cases hp : 0 ≤ llr μ ν x
  · rw [abs_of_nonneg hp]
    exact hx.trans ((le_abs_self _).trans (le_add_of_nonneg_right (Real.exp_nonneg _)))
  · rw [abs_of_neg (lt_of_not_ge hp)]
    change -llr μ ν x ≤ |b x| + Real.exp (-llr μ ν x)
    have he := Real.add_one_le_exp (-llr μ ν x)
    have hn := abs_nonneg (b x)
    linarith

/-- Changing the reference measure by an upper bound on its relative density
preserves finite KL and adds at most the expected logarithmic density bound.
This result derives finiteness; it does not assume finite KL for `μ` versus `ν`. -/
theorem klDiv_finite_and_le_of_reference_density_bound
    (μ ρ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure ν]
    (hKL : InformationTheory.klDiv μ ρ ≠ ⊤) (hρν : ρ ≪ ν)
    (b : Ω → ℝ) (hb : Integrable b μ)
    (hbound : ∀ᵐ x ∂ν, (ρ.rnDeriv ν x).toReal ≤ Real.exp (b x)) :
    InformationTheory.klDiv μ ν ≠ ⊤ ∧
      (InformationTheory.klDiv μ ν).toReal ≤
        (InformationTheory.klDiv μ ρ).toReal + ∫ x, b x ∂μ := by
  obtain ⟨hμρ, hllr⟩ := InformationTheory.klDiv_ne_top_iff.mp hKL
  have hμν := hμρ.trans hρν
  have hchain := llr_eq_add_of_absolutelyContinuous μ ρ ν hμρ hρν
  have hupper : ∀ᵐ x ∂μ, llr ρ ν x ≤ b x := by
    filter_upwards [hμν.ae_le hbound, hμρ.ae_le (Measure.rnDeriv_pos hρν),
      hμν.ae_le (Measure.rnDeriv_lt_top ρ ν)] with x hx hp ht
    apply (Real.log_le_iff_le_exp (ENNReal.toReal_pos hp.ne' ht.ne)).mpr hx
  have hsum : ∀ᵐ x ∂μ, llr μ ν x ≤ llr μ ρ x + b x := by
    filter_upwards [hchain, hupper] with x hx hb
    rw [hx]
    linarith
  have hnew := integrable_llr_of_integrable_upper_bound μ ν hμν
    (fun x ↦ llr μ ρ x + b x) (hllr.add hb) hsum
  refine ⟨InformationTheory.klDiv_ne_top hμν hnew, ?_⟩
  rw [InformationTheory.toReal_klDiv_of_measure_eq hμν (by simp),
    InformationTheory.toReal_klDiv_of_measure_eq hμρ (by simp)]
  have hi := integral_mono_ae hnew (hllr.add hb) hsum
  simp only [Pi.add_apply] at hi
  rw [integral_add hllr hb] at hi
  exact hi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The same frozen-drift Gaussian transition contracts relative entropy between
any two input laws. No invariance of either law is asserted or needed. -/
theorem interpolationLaw_klDiv_le
    (U : E → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : ℝ) :
    InformationTheory.klDiv (interpolationLaw U μ t) (interpolationLaw U ν t) ≤
      InformationTheory.klDiv μ ν := by
  unfold interpolationLaw ULA.ulaLawStep
  have h := InformationTheory.klDiv_map_le (μ.prod (stdGaussian E))
    (ν.prod (stdGaussian E)) (ULA.malaProposal_measurable U t L hLip)
  rw [klDiv_prod_same_right] at h
  exact h

/-- The actual interpolation has a finite score moment whenever its input does.
The quantitative bound is locally uniform in time and needs no state moment. -/
theorem interpolationLaw_gradient_moment
    (U : E → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x ↦ ‖gradient U x‖ ^ 2) (interpolationLaw U μ t) ∧
      (∫ x, ‖gradient U x‖ ^ 2 ∂interpolationLaw U μ t) ≤
        2 * (1 + (L : ℝ) ^ 2 * t ^ 2) * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
          4 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  obtain ⟨herr, hbound⟩ := frozen_gradient_error_energy μ U L hLip hi t ht
  have hgrad : MemLp (gradient U) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hLip.continuous.aestronglyMeasurable).mpr hi
  have hg0 : Integrable (fun p : E × E ↦ ‖gradient U p.1‖ ^ 2)
      (μ.prod (stdGaussian E)) := hi.comp_fst _
  have hproposal := ULA.malaProposal_measurable U t L hLip
  have hmeas : AEStronglyMeasurable
      (fun p : E × E ↦ gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1)
      (μ.prod (stdGaussian E)) :=
    ((hLip.continuous.measurable.comp hproposal).sub
      (hLip.continuous.measurable.comp measurable_fst)).aestronglyMeasurable
  have he := (memLp_two_iff_integrable_sq_norm hmeas).mpr herr
  have htotal : MemLp
      (fun p : E × E ↦ gradient U (ULA.malaProposal U t p.1 p.2)) 2
      (μ.prod (stdGaussian E)) := by
    convert he.add (hgrad.comp_fst (stdGaussian E)) using 1
    ext p
    simp only [Pi.add_apply, sub_add_cancel]
  have htotint := htotal.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hsq : StronglyMeasurable (fun x ↦ ‖gradient U x‖ ^ 2) :=
    (hLip.continuous.norm.pow 2).stronglyMeasurable
  have hout : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) (interpolationLaw U μ t) := by
    unfold interpolationLaw ULA.ulaLawStep
    exact (integrable_map_measure hsq.aestronglyMeasurable hproposal.aemeasurable).mpr
      htotint
  have hp (p : E × E) : ‖gradient U (ULA.malaProposal U t p.1 p.2)‖ ^ 2 ≤
      2 * ‖gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1‖ ^ 2 +
        2 * ‖gradient U p.1‖ ^ 2 := by
    have hn := norm_add_le
      (gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1) (gradient U p.1)
    rw [sub_add_cancel] at hn
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
    nlinarith [sq_nonneg
      (‖gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1‖ - ‖gradient U p.1‖)]
  have hh := integral_mono htotint ((herr.const_mul 2).add (hg0.const_mul 2)) hp
  simp only [Pi.add_apply] at hh
  rw [integral_add (herr.const_mul 2) (hg0.const_mul 2), integral_const_mul,
    integral_const_mul] at hh
  have hg0eq : (∫ p : E × E, ‖gradient U p.1‖ ^ 2 ∂μ.prod (stdGaussian E)) =
      ∫ x, ‖gradient U x‖ ^ 2 ∂μ := by
    simpa only [probReal_univ, one_smul] using
      integral_fun_fst (μ := μ) (ν := stdGaussian E) (fun x ↦ ‖gradient U x‖ ^ 2)
  rw [hg0eq] at hh
  have houteq : (∫ x, ‖gradient U x‖ ^ 2 ∂interpolationLaw U μ t) =
      ∫ p : E × E, ‖gradient U (ULA.malaProposal U t p.1 p.2)‖ ^ 2
        ∂μ.prod (stdGaussian E) := by
    unfold interpolationLaw ULA.ulaLawStep
    exact integral_map_of_stronglyMeasurable hproposal hsq
  refine ⟨hout, ?_⟩
  rw [houteq]
  nlinarith

/-- Data processing plus a reference interpolation density bound controls the
actual Gibbs-relative entropy. Both its finiteness and the score moment needed
in the correction are derived from finite initial KL and smoothness. -/
theorem interpolationLaw_entropy_bound_of_density_bound
    (U : E → ℝ) (L : ℝ≥0) (hL : 0 < L) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤)
    (t : ℝ) (ht : 0 ≤ t) (b c : ℝ)
    (href : interpolationLaw U (ULA.gibbsMeasure U) t ≪ ULA.gibbsMeasure U)
    (hbound : ∀ᵐ x ∂ULA.gibbsMeasure U,
      ((interpolationLaw U (ULA.gibbsMeasure U) t).rnDeriv (ULA.gibbsMeasure U) x).toReal ≤
        Real.exp (b + c * ‖gradient U x‖ ^ 2)) :
    InformationTheory.klDiv (interpolationLaw U μ t) (ULA.gibbsMeasure U) ≠ ⊤ ∧
      (InformationTheory.klDiv (interpolationLaw U μ t) (ULA.gibbsMeasure U)).toReal ≤
        (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal + b +
          c * (∫ x, ‖gradient U x‖ ^ 2 ∂interpolationLaw U μ t) := by
  have : IsProbabilityMeasure (interpolationLaw U μ t) :=
    interpolationLaw_isProbability U μ L hLip t
  have : IsProbabilityMeasure (interpolationLaw U (ULA.gibbsMeasure U) t) :=
    interpolationLaw_isProbability U (ULA.gibbsMeasure U) L hLip t
  obtain ⟨hgrad, _⟩ := gibbs_gradient_moment_bound_of_finite_kl U L hL hU hLip μ hKL
  obtain ⟨hgradt, _⟩ := interpolationLaw_gradient_moment U L hLip μ hgrad t ht
  have hdpi := interpolationLaw_klDiv_le U L hLip μ (ULA.gibbsMeasure U) t
  have hbetween :
      InformationTheory.klDiv (interpolationLaw U μ t)
        (interpolationLaw U (ULA.gibbsMeasure U) t) ≠ ⊤ :=
    (lt_of_le_of_lt hdpi (lt_top_iff_ne_top.mpr hKL)).ne
  obtain ⟨hfinite, hb⟩ := klDiv_finite_and_le_of_reference_density_bound
    (interpolationLaw U μ t) (interpolationLaw U (ULA.gibbsMeasure U) t)
    (ULA.gibbsMeasure U) hbetween href
    (fun x ↦ b + c * ‖gradient U x‖ ^ 2)
    ((integrable_const b).add (hgradt.const_mul c)) hbound
  rw [integral_add (integrable_const b) (hgradt.const_mul c), integral_const,
    integral_const_mul] at hb
  simp only [probReal_univ, one_smul] at hb
  have hreal := ENNReal.toReal_mono hKL hdpi
  exact ⟨hfinite, by linarith⟩

end ULA.LSI
