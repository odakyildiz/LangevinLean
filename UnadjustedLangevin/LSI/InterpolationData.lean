import UnadjustedLangevin.LSI.RegularizedTheorem

set_option linter.style.header false

/-! # Explicit regular interpolation data for the conditional LSI theorem

This structure packages density regularity, an admissible weak equation,
and moment estimates. It contains no entropy derivative, entropy recurrence,
or convergence bound. Its fields remain mathematical assumptions: this file
does not construct them from smoothness and LSI alone.

Packaging the same analytic interface allows particle algorithms to reuse the
proved entropy argument without copying or hiding its remaining obligations.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Sufficient analytic data for the actual frozen-drift Gaussian laws.
Every density, weak-equation and energy hypothesis is explicit below.
In particular, no ULA entropy estimate is a field of this structure. -/
structure RegularInterpolationData (U : E → ℝ) (α h : ℝ) (L : ℝ≥0)
    (μ : Measure E) where
  r : ℕ → ℝ → E → ℝ
  rdot : ℕ → ℝ → E → ℝ
  err : ℕ → ℝ → E → E
  law : ∀ k t, t ∈ Icc 0 h →
    tiltedMeasure (ULA.gibbsMeasure U) (r k t) =
      interpolationLaw U (ulaLaws U h μ k) t
  positive : ∀ k t, t ∈ Icc 0 h → ∀ x, 0 < r k t x
  smooth : ∀ k t, t ∈ Icc 0 h → ContDiff ℝ 1 (r k t)
  regularity : ∀ k t, t ∈ Icc 0 h →
    LocalEntropyRegularity (ULA.gibbsMeasure U) (r k) (rdot k) t
  score_integrable : ∀ k t, t ∈ Icc 0 h →
    Integrable (fun x ↦ ‖gradient (fun y ↦ Real.log (r k t y)) x‖ ^ 2)
      (tiltedMeasure (ULA.gibbsMeasure U) (r k t))
  error_integrable : ∀ k t, t ∈ Ico 0 h →
    Integrable (fun x ↦ r k t x * ‖err k t x‖ ^ 2) (ULA.gibbsMeasure U)
  error_measurable : ∀ k t, t ∈ Ico 0 h →
    AEStronglyMeasurable (fun x ↦ r k t x * inner ℝ (err k t x)
      (gradient (fun y ↦ Real.log (r k t y)) x)) (ULA.gibbsMeasure U)
  weak_equation : ∀ k t, t ∈ Ico 0 h → ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ →
    Integrable (fun x ↦ rdot k t x * ψ x) (ULA.gibbsMeasure U) →
    Integrable (fun x ↦ inner ℝ (gradient (r k t) x) (gradient ψ x))
      (ULA.gibbsMeasure U) →
    Integrable (fun x ↦ r k t x * inner ℝ (err k t x) (gradient ψ x))
      (ULA.gibbsMeasure U) →
    (∫ x, rdot k t x * ψ x ∂ULA.gibbsMeasure U) =
      -(∫ x, inner ℝ (gradient (r k t) x) (gradient ψ x) ∂ULA.gibbsMeasure U) +
        ∫ x, r k t x * inner ℝ (err k t x) (gradient ψ x) ∂ULA.gibbsMeasure U
  error_bound : ∀ k t, t ∈ Ico 0 h →
    (∫ x, r k t x * ‖err k t x‖ ^ 2 ∂ULA.gibbsMeasure U) ≤
      t ^ 2 * (L : ℝ) ^ 2 * ulaGradientMoment U h μ k +
        2 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2
  gradient_integrable : ∀ k,
    Integrable (fun x ↦ ‖gradient U x‖ ^ 2) (ulaLaws U h μ k)
  gradient_bound : ∀ k,
    ulaGradientMoment U h μ k ≤
      (4 * (L : ℝ) ^ 2 / α) * densityEntropy (ULA.gibbsMeasure U) (r k 0) +
        2 * (Module.finrank ℝ E : ℝ) * (L : ℝ)

variable {U : E → ℝ} {α h : ℝ} {L : ℝ≥0} {μ : Measure E}

/-- The regularity fields give finite actual KL for each algorithm law.
Target normalization is a separate requirement, supplied by LSI in applications. -/
theorem RegularInterpolationData.kl_finite
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (data : RegularInterpolationData U α h L μ) (hh : 0 ≤ h) (k : ℕ) :
    InformationTheory.klDiv (ulaLaws U h μ k) (ULA.gibbsMeasure U) ≠ ⊤ := by
  apply ula_kl_finite_of_interpolation U h μ (ULA.gibbsMeasure U) hh data.r data.law
  intro j t ht
  exact klDiv_finite_of_localRegularity (ULA.gibbsMeasure U) (data.r j)
    (data.rdot j) t (data.regularity j t ht) (data.positive j t ht) (data.smooth j t ht)

/-- All hypotheses of the regularized theorem are exposed in `data`.
LSI, potential smoothness and the numerical step regime are separate inputs. -/
theorem RegularInterpolationData.kl_bound [IsProbabilityMeasure μ]
    (data : RegularInterpolationData U α h L μ)
    (hα : 0 < α) (hh : 0 < h) (hL : 0 < (L : ℝ)) (hαL : α ≤ (L : ℝ))
    (hsmall : h ≤ α / (4 * (L : ℝ) ^ 2))
    (hUdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α) (k : ℕ) :
    ulaEntropy U h μ (ULA.gibbsMeasure U) k ≤
      Real.exp (-α * h * k) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal +
        8 * h * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 / α :=
  ula_kl_bound_of_regular_interpolation U α h L μ hα hh hL hαL hsmall hUdiff hLip
    hLSI data.r data.rdot data.err data.law data.positive data.smooth data.regularity
    data.score_integrable data.error_integrable data.error_measurable data.weak_equation
    data.error_bound data.gradient_integrable data.gradient_bound k

/-- The same regular density data identify probability measures on the path. -/
theorem RegularInterpolationData.path_probability [IsProbabilityMeasure μ]
    (data : RegularInterpolationData U α h L μ)
    (hLip : LipschitzWith L (gradient U)) (k : ℕ) (t : ℝ) (ht : t ∈ Icc 0 h) :
    IsProbabilityMeasure (tiltedMeasure (ULA.gibbsMeasure U) (data.r k t)) := by
  have := ulaLaws_isProbability U h μ L hLip k
  rw [data.law k t ht]
  exact interpolationLaw_isProbability U (ulaLaws U h μ k) L hLip t

/-- The one-step bound is derived from regularity and the weak equation,
not assumed as a field of the interpolation data. -/
theorem RegularInterpolationData.one_step [IsProbabilityMeasure μ]
    (data : RegularInterpolationData U α h L μ)
    (hα : 0 < α) (hh : 0 < h) (hL : 0 < (L : ℝ)) (hαL : α ≤ (L : ℝ))
    (hsmall : h ≤ α / (4 * (L : ℝ) ^ 2))
    (hUdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α) (k : ℕ) :
    ulaEntropy U h μ (ULA.gibbsMeasure U) (k + 1) ≤
      Real.exp (-α * h) * ulaEntropy U h μ (ULA.gibbsMeasure U) k +
        6 * h ^ 2 * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  have : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  let H' : ℕ → ℝ → ℝ := fun j t ↦
    ∫ x, data.rdot j t x * (Real.log (data.r j t x) + 1) ∂ULA.gibbsMeasure U
  have hcalculus (j : ℕ) (t : ℝ) (ht : t ∈ Ico 0 h) :=
    densityEntropy_derivative_bound_of_regular_weak_equation
      (ULA.gibbsMeasure U) (data.r j) (data.rdot j) h t ht (data.err j t)
      (data.regularity j) (data.positive j) (data.smooth j)
      (data.path_probability hLip j)
      (data.score_integrable j t ⟨ht.1, ht.2.le⟩)
      (data.error_integrable j t ht) (data.error_measurable j t ht)
      (data.weak_equation j t ht)
  apply ula_kl_one_step_of_interpolation
    (U := U) (α := α) (h := h) (L := L) (μ := μ)
    (hα := hα) (hh := hh) (hL := hL) (hαL := hαL) (hsmall := hsmall)
    (hLip := hLip) (hLSI := hLSI) (r := data.r) (H' := H')
    (hlaw := data.law) (hr := data.positive) (hdiff := data.smooth)
    (hKL := fun j t ht ↦ klDiv_finite_of_localRegularity (ULA.gibbsMeasure U)
      (data.r j) (data.rdot j) t (data.regularity j t ht)
      (data.positive j t ht) (data.smooth j t ht))
    (hFI := fun j t ht ↦ relativeFisher_ne_top (ULA.gibbsMeasure U) (data.r j t)
      (data.score_integrable j t ht))
    (hcont := fun j ↦ densityEntropy_continuousOn_of_regular (ULA.gibbsMeasure U)
      (data.r j) (data.rdot j) h (data.regularity j) (data.positive j) (data.smooth j)
      (data.path_probability hLip j))
    (hderiv := fun j t ht ↦ (hcalculus j t ht).1)
    (hgradient := data.gradient_bound) (_hUdiff := hUdiff)
    (_hgradientIntegrable := data.gradient_integrable) (k := k)
  intro j t ht
  have hp := (hcalculus j t ht).2
  have he := data.error_bound j t ht
  dsimp only [H']
  linarith

end ULA.LSI
