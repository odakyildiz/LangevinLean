import UnadjustedLangevin.LSI.Theorem
import UnadjustedLangevin.LSI.Regularity

set_option linter.style.header false

/-! # The ULA KL bound from regular interpolation densities and a weak equation

This wrapper derives finite KL and Fisher information, entropy continuity,
the actual entropy derivative, and its production estimate from explicit
density regularity, squared-score integrability, and a forced weak equation.
It then applies the conditional bound for the actual Gaussian ULA laws.

The hypotheses do not include an entropy derivative, a production inequality,
or a discrete recurrence. Remaining obligations include constructing the
regular densities for the frozen-drift laws, proving the weak equation for
admissible noncompact tests, bounding its drift-error energy, and proving the
initial gradient-moment estimate. The comparison `α ≤ L` remains explicit.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual ULA KL bound from local dominated density regularity and an
admissible forced weak equation. The entropy derivative and production bound
are derived; the law identification, drift-energy estimate, and initial
gradient-moment estimate are retained as explicit analytic inputs. -/
theorem ula_kl_bound_of_regular_interpolation
    (U : E → ℝ) (α h : ℝ) (L : ℝ≥0) (μ : Measure E) [IsProbabilityMeasure μ]
    (hα : 0 < α) (hh : 0 < h) (hL : 0 < (L : ℝ)) (hαL : α ≤ (L : ℝ))
    (hsmall : h ≤ α / (4 * (L : ℝ) ^ 2))
    (hUdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (r rdot : ℕ → ℝ → E → ℝ) (err : ℕ → ℝ → E → E)
    (hlaw : ∀ k t, t ∈ Icc 0 h →
      tiltedMeasure (ULA.gibbsMeasure U) (r k t) =
        interpolationLaw U (ulaLaws U h μ k) t)
    (hr : ∀ k t, t ∈ Icc 0 h → ∀ x, 0 < r k t x)
    (hdiff : ∀ k t, t ∈ Icc 0 h → ContDiff ℝ 1 (r k t))
    (data : ∀ k t, t ∈ Icc 0 h →
      LocalEntropyRegularity (ULA.gibbsMeasure U) (r k) (rdot k) t)
    (hfisher_int : ∀ k t, t ∈ Icc 0 h →
      Integrable (fun x ↦ ‖gradient (fun y ↦ Real.log (r k t y)) x‖ ^ 2)
        (tiltedMeasure (ULA.gibbsMeasure U) (r k t)))
    (henergy_int : ∀ k t, t ∈ Ico 0 h →
      Integrable (fun x ↦ r k t x * ‖err k t x‖ ^ 2) (ULA.gibbsMeasure U))
    (herror_meas : ∀ k t, t ∈ Ico 0 h →
      AEStronglyMeasurable
        (fun x ↦ r k t x * inner ℝ (err k t x)
          (gradient (fun y ↦ Real.log (r k t y)) x)) (ULA.gibbsMeasure U))
    (hweak : ∀ k t, t ∈ Ico 0 h → ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ →
      Integrable (fun x ↦ rdot k t x * ψ x) (ULA.gibbsMeasure U) →
      Integrable (fun x ↦ inner ℝ (gradient (r k t) x) (gradient ψ x))
        (ULA.gibbsMeasure U) →
      Integrable (fun x ↦ r k t x * inner ℝ (err k t x) (gradient ψ x))
        (ULA.gibbsMeasure U) →
      (∫ x, rdot k t x * ψ x ∂ULA.gibbsMeasure U) =
        -(∫ x, inner ℝ (gradient (r k t) x) (gradient ψ x) ∂ULA.gibbsMeasure U) +
          ∫ x, r k t x * inner ℝ (err k t x) (gradient ψ x) ∂ULA.gibbsMeasure U)
    (henergy : ∀ k t, t ∈ Ico 0 h →
      (∫ x, r k t x * ‖err k t x‖ ^ 2 ∂ULA.gibbsMeasure U) ≤
        t ^ 2 * (L : ℝ) ^ 2 * ulaGradientMoment U h μ k +
          2 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2)
    (hgradientIntegrable : ∀ k,
      Integrable (fun x ↦ ‖gradient U x‖ ^ 2) (ulaLaws U h μ k))
    (hgradient : ∀ k,
      ulaGradientMoment U h μ k ≤
        (4 * (L : ℝ) ^ 2 / α) * densityEntropy (ULA.gibbsMeasure U) (r k 0) +
          2 * (Module.finrank ℝ E : ℝ) * (L : ℝ)) (k : ℕ) :
    ulaEntropy U h μ (ULA.gibbsMeasure U) k ≤
      Real.exp (-α * h * k) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal +
        8 * h * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 / α := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  have hprob (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 h) :
      IsProbabilityMeasure (tiltedMeasure (ULA.gibbsMeasure U) (r j t)) := by
    have := ulaLaws_isProbability U h μ L hLip j
    rw [hlaw j t ht]
    exact interpolationLaw_isProbability U (ulaLaws U h μ j) L hLip t
  have hKL (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 h) :
      InformationTheory.klDiv (tiltedMeasure (ULA.gibbsMeasure U) (r j t))
        (ULA.gibbsMeasure U) ≠ ⊤ :=
    klDiv_finite_of_localRegularity (ULA.gibbsMeasure U) (r j) (rdot j) t
      (data j t ht) (hr j t ht) (hdiff j t ht)
  have hFI (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 h) :
      relativeFisher (ULA.gibbsMeasure U) (r j t) ≠ ⊤ :=
    relativeFisher_ne_top (ULA.gibbsMeasure U) (r j t) (hfisher_int j t ht)
  have hcont (j : ℕ) :
      ContinuousOn (fun t ↦ densityEntropy (ULA.gibbsMeasure U) (r j t)) (Icc 0 h) :=
    densityEntropy_continuousOn_of_regular (ULA.gibbsMeasure U) (r j) (rdot j) h
      (data j) (hr j) (hdiff j) (hprob j)
  let H' : ℕ → ℝ → ℝ := fun j t ↦
    ∫ x, rdot j t x * (Real.log (r j t x) + 1) ∂ULA.gibbsMeasure U
  have hcalculus (j : ℕ) (t : ℝ) (ht : t ∈ Ico 0 h) :=
    densityEntropy_derivative_bound_of_regular_weak_equation
      (ULA.gibbsMeasure U) (r j) (rdot j) h t ht (err j t)
      (data j) (hr j) (hdiff j) (hprob j)
      (hfisher_int j t ⟨ht.1, ht.2.le⟩)
      (henergy_int j t ht) (herror_meas j t ht) (hweak j t ht)
  have hderiv (j : ℕ) (t : ℝ) (ht : t ∈ Ico 0 h) :
      HasDerivWithinAt (fun s ↦ densityEntropy (ULA.gibbsMeasure U) (r j s))
        (H' j t) (Ici t) t := (hcalculus j t ht).1
  have hproduction (j : ℕ) (t : ℝ) (ht : t ∈ Ico 0 h) :
      H' j t ≤ -(3 / 4 : ℝ) * (relativeFisher (ULA.gibbsMeasure U) (r j t)).toReal +
        t ^ 2 * (L : ℝ) ^ 2 * ulaGradientMoment U h μ j +
          2 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
    have hprod := (hcalculus j t ht).2
    have herror := henergy j t ht
    dsimp only [H']
    linarith
  exact ula_kl_bound_of_interpolation
    (U := U) (α := α) (h := h) (L := L) (μ := μ)
    (hα := hα) (hh := hh) (hL := hL) (hαL := hαL) (hsmall := hsmall)
    (hLip := hLip) (hLSI := hLSI) (r := r) (H' := H')
    (hlaw := hlaw) (hr := hr) (hdiff := hdiff) (hKL := hKL) (hFI := hFI)
    (hcont := hcont) (hderiv := hderiv) (_hUdiff := hUdiff)
    (_hgradientIntegrable := hgradientIntegrable)
    (hproduction := hproduction) (hgradient := hgradient) k

end ULA.LSI
