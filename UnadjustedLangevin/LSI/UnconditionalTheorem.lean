import UnadjustedLangevin.LSI.Compatibility
import UnadjustedLangevin.LSI.EntropyMoment
import UnadjustedLangevin.LSI.GaussianEntropy
import UnadjustedLangevin.LSI.GaussianMeasurability
import UnadjustedLangevin.LSI.InitialEntropy
import UnadjustedLangevin.LSI.IntegratedEntropy
import UnadjustedLangevin.LSI.DiscreteEntropy
import UnadjustedLangevin.LSI.GaussianEntropyProduction

set_option linter.style.header false

/-! # Actual ULA entropy from the potential and functional inequality

All analytic quantities in this file are those of the actual independent
Gaussian transition. In particular, finiteness of the iterated KL divergence
is proved before its ordinary real value is used.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- On a singleton state space, all probability laws agree. This treats the
zero-dimensional endpoint separately from the positive-dimensional argument
that compares the LSI and gradient Lipschitz constants. -/
theorem probabilityMeasure_eq_of_subsingleton [Subsingleton E]
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s _
  by_cases hzero : (0 : E) ∈ s
  · have hs : s = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      simpa only [Subsingleton.elim x 0] using hzero
    simp [hs]
  · have hs : s = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hzero (by simpa only [Subsingleton.elim x 0] using hx)
    simp [hs]

/-- A positive admissible step already forces a positive smoothness parameter,
including Lean's convention that division by zero is zero. -/
theorem positive_smoothness_of_step (α h : ℝ) (L : ℝ≥0) (hh : 0 < h)
    (hsmall : h ≤ α / (4 * (L : ℝ) ^ 2)) : 0 < L := by
  by_contra hn
  have hz : L = 0 := le_antisymm (le_of_not_gt hn) zero_le
  simp only [hz, NNReal.coe_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, div_zero] at hsmall
  linarith

/-- Finite initial KL implies finite KL at every actual Gaussian ULA iterate.
No density path, regularity data, moment assumption, or recurrence is supplied.
The step can be any positive real number in this finiteness statement. -/
theorem ula_kl_finite
    (U : E → ℝ) (α h : ℝ) (L : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hα : 0 < α) (hh : 0 < h) (hL : 0 < L)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤) (k : ℕ) :
    InformationTheory.klDiv (ulaLaws U h μ k) (ULA.gibbsMeasure U) ≠ ⊤ := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  induction k with
  | zero => exact hKL
  | succ k hk =>
    have : IsProbabilityMeasure (ulaLaws U h μ k) := ulaLaws_isProbability U h μ L hLip k
    have hgradient := (gibbs_gradient_moment_bound_of_finite_kl U L hL hU hLip
      (ulaLaws U h μ k) hk).1
    have hmem : MemLp (gradient U) 2 (ulaLaws U h μ k) :=
      (memLp_two_iff_integrable_sq_norm hLip.continuous.aestronglyMeasurable).mpr hgradient
    have hfinite := interpolationLaw_klDiv_ne_top U (ulaLaws U h μ k) α hα L hU hLip
      hLSI hmem h hh
    rwa [interpolationLaw_endpoint] at hfinite

/-- The numerical restrictions needed by the entropy comparison follow from
the original LSI and the paper's step condition in positive dimension. -/
theorem lsi_step_bounds [Nontrivial E]
    (U : E → ℝ) (α h : ℝ) (L : ℝ≥0)
    (hα : 0 < α) (hh : 0 < h)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hsmall : h ≤ α / (4 * (L : ℝ) ^ 2)) :
    α ≤ (L : ℝ) ∧ 0 < L ∧ h * (L : ℝ) ≤ 1 / 4 ∧ α * h ≤ 1 / 4 := by
  have hαL := hLSI.constant_le_smoothness hU hLip
  have hL : 0 < (L : ℝ) := hα.trans_le hαL
  have hs := (le_div_iff₀ (by positivity : 0 < 4 * (L : ℝ) ^ 2)).mp hsmall
  have hmul : (4 * h * (L : ℝ)) * (L : ℝ) ≤ 1 * (L : ℝ) := by nlinarith
  have hhL : h * (L : ℝ) ≤ 1 / 4 := by
    have := (mul_le_mul_iff_of_pos_right hL).mp hmul
    linarith
  exact ⟨hαL, hL, hhL, by nlinarith⟩

/-- LSI in real-valued integral form for the actual positive-time law.
Finiteness of both KL and Fisher, and the initial score moment, are derived
from finite initial KL rather than supplied as interpolation hypotheses. -/
theorem interpolationLaw_entropy_le_fisher
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (L : ℝ≥0) (hL : 0 < L)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤)
    (t : ℝ) (ht : 0 < t) :
    2 * α * (InformationTheory.klDiv (interpolationLaw U μ t)
      (ULA.gibbsMeasure U)).toReal ≤
        ∫ y, ‖interpolationRelativeScoreField U μ t y‖ ^ 2 ∂interpolationLaw U μ t := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  have hG := (gibbs_gradient_moment_bound_of_finite_kl U L hL hU hLip μ hKL).1
  have hgrad : MemLp (gradient U) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hLip.continuous.aestronglyMeasurable).mpr hG
  have hKLt := interpolationLaw_klDiv_ne_top U μ α hα L hU hLip hLSI hgrad t ht
  have hFI := interpolationRelativeFisher_ne_top U μ L hU hLip hgrad t ht
  have hscore := interpolationRelativeScore_memLp U μ L hU hLip hgrad t ht
  have hint := hscore.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have h := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKLt) hFI).mpr
      (interpolationLaw_logSobolev U μ α L hU hLip hLSI t ht)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * α)] at h
  unfold relativeFisher at h
  rw [tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ sq_nonneg _)] at h
  simpa only [interpolationRelativeScoreField_eq U μ L hU hLip t ht] using h

/-- The same actual-law LSI estimate in the Fisher notation used by the
entropy-production identity. Both extended quantities have already been
proved finite before taking real values. -/
theorem interpolationLaw_entropy_le_relativeFisher
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (L : ℝ≥0) (hL : 0 < L)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤)
    (t : ℝ) (ht : 0 < t) :
    2 * α * (InformationTheory.klDiv (interpolationLaw U μ t)
      (ULA.gibbsMeasure U)).toReal ≤
        (relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)).toReal := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  have hG := (gibbs_gradient_moment_bound_of_finite_kl U L hL hU hLip μ hKL).1
  have hgrad : MemLp (gradient U) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hLip.continuous.aestronglyMeasurable).mpr hG
  have hKLt := interpolationLaw_klDiv_ne_top U μ α hα L hU hLip hLSI hgrad t ht
  have hFI := interpolationRelativeFisher_ne_top U μ L hU hLip hgrad t ht
  have h := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKLt) hFI).mpr
      (interpolationLaw_logSobolev U μ α L hU hLip hLSI t ht)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * α)] using h

/-- The coefficient-six entropy estimate for one actual Gaussian transition.
All interpolation calculus, initial-endpoint control, score moments, and the
comparison of constants are proved from the potential and LSI hypotheses. -/
theorem interpolation_kl_one_step
    (U : E → ℝ) (α h : ℝ) (L : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hα : 0 < α) (hh : 0 < h)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hsmall : h ≤ α / (4 * (L : ℝ) ^ 2))
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤) :
    (InformationTheory.klDiv (interpolationLaw U μ h) (ULA.gibbsMeasure U)).toReal ≤
      Real.exp (-α * h) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal +
        6 * h ^ 2 * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  rcases subsingleton_or_nontrivial E with hs | hn
  · letI := hs
    have : IsProbabilityMeasure (interpolationLaw U μ h) :=
      interpolationLaw_isProbability U μ L hLip h
    rw [probabilityMeasure_eq_of_subsingleton (interpolationLaw U μ h) (ULA.gibbsMeasure U),
      InformationTheory.klDiv_self, ENNReal.toReal_zero]
    positivity
  · letI := hn
    obtain ⟨hαL, hL, _, _⟩ := lsi_step_bounds U α h L hα hh hU hLip hLSI hsmall
    obtain ⟨hG, hmoment⟩ := gibbs_gradient_moment_bound_of_finite_kl_of_alpha_le
      U L hU hLip μ hKL α hα hαL
    have hgrad : MemLp (gradient U) 2 μ :=
      (memLp_two_iff_integrable_sq_norm hLip.continuous.aestronglyMeasurable).mpr hG
    have hAC (s : ℝ) (hs : s ∈ Ioo 0 h) :
        AbsolutelyContinuousOnInterval (actualInterpolationEntropy U μ) s h :=
      (interpolationEntropy_local_chain_rule U μ α hα L hU hLip hLSI hgrad
        s h hs.1 hs.2.le).1
    have hlsi : ∀ᵐ t ∂volume, t ∈ Ioo 0 h →
        2 * α * actualInterpolationEntropy U μ t ≤
          (relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)).toReal :=
      ae_of_all _ fun t ht ↦ interpolationLaw_entropy_le_relativeFisher
        U μ α hα L hL hU hLip hLSI hKL t ht.1
    have hprod := interpolationEntropy_derivative_bound_ae
      U μ α hα L hU hLip hLSI hgrad h hh
    have hbound := one_step_entropy_of_ae_interpolation
      (actualInterpolationEntropy U μ) (interpolationEntropyMajorant U L μ)
      (fun t ↦ (relativeFisher (ULA.gibbsMeasure U)
        (interpolationRelativeDensity U μ t)).toReal)
      (∫ x, ‖gradient U x‖ ^ 2 ∂μ) α L h (Module.finrank ℝ E : ℝ)
      hα hL hh hαL (by positivity) hsmall
      (by rw [interpolationEntropyMajorant_zero]; exact ENNReal.toReal_nonneg)
      hAC (interpolationEntropyMajorant_continuousAt_zero U L μ)
      (interpolationLaw_entropy_eventually_le_majorant U L hL hU hLip μ hKL)
      hlsi hprod (by simpa only [interpolationEntropyMajorant_zero] using hmoment)
    simpa only [actualInterpolationEntropy, interpolationEntropyMajorant_zero] using hbound

/-- One-step entropy decay at every actual ULA iterate, with the current
finite KL established by induction from the finite initial KL. -/
theorem ula_kl_one_step
    (U : E → ℝ) (α h : ℝ) (L : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hα : 0 < α) (hh : 0 < h)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hsmall : h ≤ α / (4 * (L : ℝ) ^ 2))
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤) (k : ℕ) :
    ulaEntropy U h μ (ULA.gibbsMeasure U) (k + 1) ≤
      Real.exp (-α * h) * ulaEntropy U h μ (ULA.gibbsMeasure U) k +
        6 * h ^ 2 * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  have : IsProbabilityMeasure (ulaLaws U h μ k) := ulaLaws_isProbability U h μ L hLip k
  have hfinite := ula_kl_finite U α h L μ hα hh
    (positive_smoothness_of_step α h L hh hsmall) hU hLip hLSI hKL k
  have hbound := interpolation_kl_one_step U α h L (ulaLaws U h μ k)
    hα hh hU hLip hLSI hsmall hfinite
  rwa [interpolationLaw_endpoint] at hbound

/-- The full ULA KL theorem from differentiability, Lipschitz gradient, LSI,
the paper's step condition, and finite initial KL. Finiteness of every output
KL is part of the conclusion, so `toReal` cannot erase an infinite entropy.
No convexity, interpolation data, moment, compatibility, derivative,
weak-equation, or discrete-recurrence hypothesis is supplied. -/
theorem ula_kl_bound
    (U : E → ℝ) (α h : ℝ) (L : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hα : 0 < α) (hh : 0 < h)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hsmall : h ≤ α / (4 * (L : ℝ) ^ 2))
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤) (k : ℕ) :
    InformationTheory.klDiv (ulaLaws U h μ k) (ULA.gibbsMeasure U) ≠ ⊤ ∧
      ulaEntropy U h μ (ULA.gibbsMeasure U) k ≤
        Real.exp (-α * h * k) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal +
          8 * h * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 / α := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  have hL := positive_smoothness_of_step α h L hh hsmall
  refine ⟨ula_kl_finite U α h L μ hα hh hL hU hLip hLSI hKL k, ?_⟩
  rcases subsingleton_or_nontrivial E with hs | hn
  · letI := hs
    have : IsProbabilityMeasure (ulaLaws U h μ k) := ulaLaws_isProbability U h μ L hLip k
    unfold ulaEntropy
    rw [probabilityMeasure_eq_of_subsingleton (ulaLaws U h μ k) (ULA.gibbsMeasure U),
      InformationTheory.klDiv_self, ENNReal.toReal_zero]
    positivity
  · letI := hn
    have hαh := (lsi_step_bounds U α h L hα hh hU hLip hLSI hsmall).2.2.2
    have hstep := ula_kl_one_step U α h L μ hα hh hU hLip hLSI hsmall hKL
    simpa only [ulaEntropy_zero] using discrete_entropy_recurrence_bound
      (ulaEntropy U h μ (ULA.gibbsMeasure U)) α h (Module.finrank ℝ E : ℝ) L
      hα hh (by positivity) hαh hstep k

end ULA.LSI
