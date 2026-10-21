import UnadjustedLangevin.LSI.ULALaw
import UnadjustedLangevin.LSI.EntropyFlow
import UnadjustedLangevin.LSI.OneStep
import UnadjustedLangevin.LSI.DiscreteEntropy

set_option linter.style.header false

/-! # A conditional KL bound for the actual ULA laws

These theorems connect actual independent-Gaussian ULA laws to the scalar
interpolation estimate and its iteration. The density path must be identified
with the actual frozen-drift law at every interpolation time. Its regularity,
finite entropy and Fisher information, entropy-production estimate, and initial
gradient-moment estimate remain explicit analytic hypotheses.

No discrete recurrence is assumed: the one-step estimate with constant `6`
is derived from those interpolation hypotheses and LSI, then iterated to the
bound with constant `8` in Vempala--Wibisono (2019), Theorem 2. This conditional
result does not establish all of that paper's analytic hypotheses from LSI and
Lipschitzness alone. The comparison `α ≤ L` is also a displayed hypothesis.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual squared-gradient moment of the current ULA law. Applications
retain an explicit integrability proof before using this real integral. -/
def ulaGradientMoment (U : E → ℝ) (h : ℝ) (μ : Measure E) (k : ℕ) : ℝ :=
  ∫ x, ‖gradient U x‖ ^ 2 ∂ulaLaws U h μ k

omit [BorelSpace E] in
/-- Finiteness of the identified interpolation entropy at time zero gives
finiteness of the corresponding actual ULA entropy. -/
theorem ula_kl_finite_of_interpolation (U : E → ℝ) (h : ℝ) (μ ν : Measure E)
    (hh : 0 ≤ h) (r : ℕ → ℝ → E → ℝ)
    (hlaw : ∀ k t, t ∈ Icc 0 h →
      tiltedMeasure ν (r k t) = interpolationLaw U (ulaLaws U h μ k) t)
    (hKL : ∀ k t, t ∈ Icc 0 h →
      InformationTheory.klDiv (tiltedMeasure ν (r k t)) ν ≠ ⊤) (k : ℕ) :
    InformationTheory.klDiv (ulaLaws U h μ k) ν ≠ ⊤ := by
  have hfinite := hKL k 0 ⟨le_rfl, hh⟩
  rw [hlaw k 0 ⟨le_rfl, hh⟩, interpolationLaw_zero] at hfinite
  exact hfinite

section Interpolation

variable (U : E → ℝ) (α h : ℝ) (L : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hα : 0 < α) (hh : 0 < h) (hL : 0 < (L : ℝ)) (hαL : α ≤ (L : ℝ))
    (hsmall : h ≤ α / (4 * (L : ℝ) ^ 2))
    (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (r : ℕ → ℝ → E → ℝ) (H' : ℕ → ℝ → ℝ)
    (hlaw : ∀ k t, t ∈ Icc 0 h →
      tiltedMeasure (ULA.gibbsMeasure U) (r k t) =
        interpolationLaw U (ulaLaws U h μ k) t)
    (hr : ∀ k t, t ∈ Icc 0 h → ∀ x, 0 < r k t x)
    (hdiff : ∀ k t, t ∈ Icc 0 h → ContDiff ℝ 1 (r k t))
    (hKL : ∀ k t, t ∈ Icc 0 h →
      InformationTheory.klDiv (tiltedMeasure (ULA.gibbsMeasure U) (r k t))
        (ULA.gibbsMeasure U) ≠ ⊤)
    (hFI : ∀ k t, t ∈ Icc 0 h →
      relativeFisher (ULA.gibbsMeasure U) (r k t) ≠ ⊤)
    (hcont : ∀ k, ContinuousOn (fun t ↦ densityEntropy (ULA.gibbsMeasure U) (r k t))
      (Icc 0 h))
    (hderiv : ∀ k t, t ∈ Ico 0 h →
      HasDerivWithinAt (fun s ↦ densityEntropy (ULA.gibbsMeasure U) (r k s))
        (H' k t) (Ici t) t)
    (hproduction : ∀ k t, t ∈ Ico 0 h →
      H' k t ≤ -(3 / 4 : ℝ) * (relativeFisher (ULA.gibbsMeasure U) (r k t)).toReal +
        t ^ 2 * (L : ℝ) ^ 2 * ulaGradientMoment U h μ k +
        2 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2)
    (hgradient : ∀ k,
      ulaGradientMoment U h μ k ≤
        (4 * (L : ℝ) ^ 2 / α) * densityEntropy (ULA.gibbsMeasure U) (r k 0) +
          2 * (Module.finrank ℝ E : ℝ) * (L : ℝ))

include hα hh hL hαL hsmall hLip hLSI r H' hlaw hr hdiff hKL hFI hcont hderiv
  hproduction hgradient

/-- The actual ULA law satisfies the paper's one-step entropy estimate,
conditional on the displayed analytic interpolation hypotheses. -/
theorem ula_kl_one_step_of_interpolation
    (_hUdiff : Differentiable ℝ U)
    (_hgradientIntegrable : ∀ k,
      Integrable (fun x ↦ ‖gradient U x‖ ^ 2) (ulaLaws U h μ k)) (k : ℕ) :
    ulaEntropy U h μ (ULA.gibbsMeasure U) (k + 1) ≤
      Real.exp (-α * h) * ulaEntropy U h μ (ULA.gibbsMeasure U) k +
        6 * h ^ 2 * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  have hzero : densityEntropy (ULA.gibbsMeasure U) (r k 0) =
      ulaEntropy U h μ (ULA.gibbsMeasure U) k := by
    unfold densityEntropy ulaEntropy
    rw [hlaw k 0 ⟨le_rfl, hh.le⟩, interpolationLaw_zero]
  have hend : densityEntropy (ULA.gibbsMeasure U) (r k h) =
      ulaEntropy U h μ (ULA.gibbsMeasure U) (k + 1) := by
    unfold densityEntropy ulaEntropy
    rw [hlaw k h ⟨hh.le, le_rfl⟩, interpolationLaw_endpoint]
  have hprob (t : ℝ) (ht : t ∈ Icc 0 h) :
      IsProbabilityMeasure (tiltedMeasure (ULA.gibbsMeasure U) (r k t)) := by
    have := ulaLaws_isProbability U h μ L hLip k
    rw [hlaw k t ht]
    exact interpolationLaw_isProbability U (ulaLaws U h μ k) L hLip t
  have hlsi (t : ℝ) (ht : t ∈ Ico 0 h) :
      2 * α * densityEntropy (ULA.gibbsMeasure U) (r k t) ≤
        (relativeFisher (ULA.gibbsMeasure U) (r k t)).toReal := by
    have ht' : t ∈ Icc (0 : ℝ) h := ⟨ht.1, ht.2.le⟩
    exact hLSI.entropy_le_fisher hα.le (r k t) (hr k t ht') (hdiff k t ht')
      (hprob t ht') (hKL k t ht') (hFI k t ht')
  have hone := one_step_entropy_of_interpolation
    (fun t ↦ densityEntropy (ULA.gibbsMeasure U) (r k t)) (H' k)
    (fun t ↦ (relativeFisher (ULA.gibbsMeasure U) (r k t)).toReal)
    (ulaGradientMoment U h μ k) α L h (Module.finrank ℝ E : ℝ)
    hα hL hh hαL (by positivity) hsmall ENNReal.toReal_nonneg
    (hcont k) (hderiv k) hlsi (hproduction k) (hgradient k)
  rwa [hzero, hend] at hone

/-- The KL bound for the actual iterated ULA laws obtained from explicit
interpolation hypotheses. Finite KL is supplied on the identified paths;
no extended value is silently replaced by its `toReal` conversion. -/
theorem ula_kl_bound_of_interpolation
    (_hUdiff : Differentiable ℝ U)
    (_hgradientIntegrable : ∀ k,
      Integrable (fun x ↦ ‖gradient U x‖ ^ 2) (ulaLaws U h μ k)) (k : ℕ) :
    ulaEntropy U h μ (ULA.gibbsMeasure U) k ≤
      Real.exp (-α * h * k) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal +
        8 * h * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 / α := by
  have hstep (j : ℕ) := ula_kl_one_step_of_interpolation
    (U := U) (α := α) (h := h) (L := L) (μ := μ)
    (hα := hα) (hh := hh) (hL := hL) (hαL := hαL) (hsmall := hsmall)
    (hLip := hLip) (hLSI := hLSI) (r := r) (H' := H')
    (hlaw := hlaw) (hr := hr) (hdiff := hdiff) (hKL := hKL) (hFI := hFI)
    (hcont := hcont) (hderiv := hderiv) (_hUdiff := _hUdiff)
    (_hgradientIntegrable := _hgradientIntegrable)
    (hproduction := hproduction) (hgradient := hgradient) j
  have hαh : α * h ≤ 1 / 4 := by
    have hbound := (le_div_iff₀ (by positivity : 0 < 4 * (L : ℝ) ^ 2)).mp hsmall
    have hLh : h * (L : ℝ) ≤ 1 / 4 := by
      have hmul : (4 * h * (L : ℝ)) * (L : ℝ) ≤ 1 * (L : ℝ) := by nlinarith
      have := (mul_le_mul_iff_of_pos_right hL).mp hmul
      linarith
    nlinarith
  simpa only [ulaEntropy_zero] using discrete_entropy_recurrence_bound
    (ulaEntropy U h μ (ULA.gibbsMeasure U)) α h (Module.finrank ℝ E : ℝ) L
    hα hh (by positivity) hαh hstep k

end Interpolation

end ULA.LSI
