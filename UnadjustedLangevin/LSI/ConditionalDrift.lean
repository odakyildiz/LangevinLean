import UnadjustedLangevin.LSI.GaussianDrift
import UnadjustedLangevin.LSI.ULALaw
import UnadjustedLangevin.LSI.KLOfDensity
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.FactorsThrough

set_option linter.style.header false

/-! # Conditional drift for the actual Gaussian interpolation

The discrepancy on the independent joint law is turned into a measurable
field on the interpolated state using conditional expectation and the
Doob–Dynkin factorization theorem. Conditional Jensen then transfers the
joint squared-error estimate to the actual interpolated law. These facts
supply the drift-energy bridge; density construction and the admissible
weak entropy equation are separate obligations.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA.LSI

/-- A square-integrable random vector has a measurable conditional mean as a
function of any measurable observed state. Its energy on the observed law
is at most the energy of the original random vector. No conditional kernel
or preselected version of the conditional mean is assumed. -/
theorem exists_conditional_mean_with_energy
    {Ω S F : Type*} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → S) (hY : Measurable Y) (D : Ω → F) (hD : MemLp D 2 P) :
    ∃ e : S → F, StronglyMeasurable e ∧
      (fun ω ↦ e (Y ω)) =ᵐ[P] P[D | MeasurableSpace.comap Y mS] ∧
      Integrable (fun y ↦ ‖e y‖ ^ 2) (P.map Y) ∧
      (∫ y, ‖e y‖ ^ 2 ∂P.map Y) ≤ ∫ ω, ‖D ω‖ ^ 2 ∂P := by
  obtain ⟨e, he, hfactor⟩ :=
    (stronglyMeasurable_condExp (μ := P) (m := MeasurableSpace.comap Y mS)
      (f := D)).exists_eq_measurable_comp
  have hcomp : (fun ω ↦ e (Y ω)) = P[D | MeasurableSpace.comap Y mS] := by
    funext ω
    exact congrFun hfactor.symm ω
  have hCE : MemLp (P[D | MeasurableSpace.comap Y mS]) 2 P := hD.condExp (by norm_num)
  have hCEint : Integrable (fun ω ↦ ‖P[D | MeasurableSpace.comap Y mS] ω‖ ^ 2) P :=
    hCE.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hint : Integrable (fun y ↦ ‖e y‖ ^ 2) (P.map Y) := by
    apply (integrable_map_measure (he.norm.pow 2).aestronglyMeasurable hY.aemeasurable).mpr
    change Integrable (fun ω ↦ ‖((fun ω ↦ e (Y ω)) ω)‖ ^ 2) P
    rw [hcomp]
    exact hCEint
  refine ⟨e, he, Filter.EventuallyEq.of_eq hcomp, hint, ?_⟩
  have hmap := integral_map_of_stronglyMeasurable (μ := P) hY (he.norm.pow 2)
  change (∫ y, ‖e y‖ ^ 2 ∂P.map Y) = (∫ ω, ‖e (Y ω)‖ ^ 2 ∂P) at hmap
  rw [hmap]
  change (∫ ω, ‖((fun ω ↦ e (Y ω)) ω)‖ ^ 2 ∂P) ≤ _
  rw [hcomp]
  have h := integral_norm_condExp_rpow_le (m := MeasurableSpace.comap Y mS)
    (p := (2 : ℝ)) (by norm_num)
    (by simpa only [Real.rpow_two] using
      hD.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
  simpa only [Real.rpow_two] using h


/-- A state-space version of the conditional mean preserves every measurable
set test. This identifies its vector-valued flux on the observed law with
the joint discrepancy flux, rather than specifying only an energy bound. -/
theorem conditional_mean_setIntegral
    {Ω S F : Type*} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → S) (hY : Measurable Y) (D : Ω → F) (hD : Integrable D P)
    (e : S → F) (he : StronglyMeasurable e)
    (hcond : (fun ω ↦ e (Y ω)) =ᵐ[P] P[D | MeasurableSpace.comap Y mS])
    (A : Set S) (hA : MeasurableSet A) :
    (∫ y in A, e y ∂P.map Y) = ∫ ω in Y ⁻¹' A, D ω ∂P := by
  rw [setIntegral_map hA he.aestronglyMeasurable hY.aemeasurable]
  calc
    _ = ∫ ω in Y ⁻¹' A, P[D | MeasurableSpace.comap Y mS] ω ∂P :=
      integral_congr_ae (ae_restrict_of_ae hcond)
    _ = _ := setIntegral_condExp hY.comap_le hD ⟨A, hA, rfl⟩


/-- Conditional drift also preserves integrable inner-product tests that depend
on the observed state. This is the weak-equation flux identity, including
noncompact tests whenever the displayed joint product is integrable. -/
theorem conditional_mean_inner_integral
    {Ω S F : Type*} [mΩ : MeasurableSpace Ω] [mS : MeasurableSpace S]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace F] [BorelSpace F]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → S) (hY : Measurable Y) (D : Ω → F) (hD : Integrable D P)
    (e : S → F) (he : StronglyMeasurable e)
    (hcond : (fun ω ↦ e (Y ω)) =ᵐ[P] P[D | MeasurableSpace.comap Y mS])
    (φ : S → F) (hφ : StronglyMeasurable φ)
    (hprod : Integrable (fun ω ↦ inner ℝ (D ω) (φ (Y ω))) P) :
    (∫ y, inner ℝ (e y) (φ y) ∂P.map Y) =
      ∫ ω, inner ℝ (D ω) (φ (Y ω)) ∂P := by
  have hYpull : Measurable[MeasurableSpace.comap Y mS] Y :=
    Measurable.of_comap_le le_rfl
  have hpull := condExp_bilin_of_stronglyMeasurable_right (μ := P)
    (m := MeasurableSpace.comap Y mS) (innerSL ℝ)
    (hφ.comp_measurable hYpull) hprod hD
  rw [integral_map_of_stronglyMeasurable hY (he.inner hφ)]
  calc
    _ = ∫ ω, inner ℝ (P[D | MeasurableSpace.comap Y mS] ω) (φ (Y ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards [hcond] with ω hω
      rw [hω]
    _ = ∫ ω, P[fun ω ↦ inner ℝ (D ω) (φ (Y ω)) |
        MeasurableSpace.comap Y mS] ω ∂P := integral_congr_ae hpull.symm
    _ = _ := integral_condExp hY.comap_le

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The gradient discrepancy on the actual independent Gaussian joint law.
Its sign agrees with the extra drift in the relative-density equation. -/
def frozenGradientDiscrepancy (U : E → ℝ) (t : ℝ) (p : E × E) : E :=
  gradient U (ULA.malaProposal U t p.1 p.2) - gradient U p.1

/-- The information contained in the frozen-drift interpolated state. -/
abbrev frozenDriftSigmaAlgebra (U : E → ℝ) (t : ℝ) : MeasurableSpace (E × E) :=
  MeasurableSpace.comap (fun p : E × E ↦ ULA.malaProposal U t p.1 p.2) inferInstance

/-- Construct the actual interpolation's conditional drift-error field and
prove its squared-energy estimate. This conclusion follows from the Gaussian
update, square-integrable initial gradient, Lipschitzness and conditional
Jensen; no error field or error-energy estimate is supplied as an assumption. -/
theorem exists_frozen_drift_error
    (μ : Measure E) [IsProbabilityMeasure μ] (U : E → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (hgrad : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ err : E → E, StronglyMeasurable err ∧
      (fun p : E × E ↦ err (ULA.malaProposal U t p.1 p.2)) =ᵐ[μ.prod (stdGaussian E)]
        (μ.prod (stdGaussian E))[frozenGradientDiscrepancy U t |
          frozenDriftSigmaAlgebra U t] ∧
      Integrable (fun y ↦ ‖err y‖ ^ 2) (interpolationLaw U μ t) ∧
      (∫ y, ‖err y‖ ^ 2 ∂interpolationLaw U μ t) ≤
        t ^ 2 * (L : ℝ) ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
          2 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  let Y := fun p : E × E ↦ ULA.malaProposal U t p.1 p.2
  let D := frozenGradientDiscrepancy U t
  have hY : Measurable Y := ULA.malaProposal_measurable U t L hLip
  have henergy := frozen_gradient_error_energy μ U L hLip hgrad t ht
  have hDmeas : AEStronglyMeasurable D (μ.prod (stdGaussian E)) :=
    ((hLip.continuous.measurable.comp hY).sub
      (hLip.continuous.measurable.comp measurable_fst)).aestronglyMeasurable
  have hD : MemLp D 2 (μ.prod (stdGaussian E)) :=
    (memLp_two_iff_integrable_sq_norm hDmeas).mpr henergy.1
  obtain ⟨err, herr, hcond, hint, hbound⟩ :=
    exists_conditional_mean_with_energy (μ.prod (stdGaussian E)) Y hY D hD
  refine ⟨err, herr, hcond, hint, ?_⟩
  change (∫ y, ‖err y‖ ^ 2 ∂(μ.prod (stdGaussian E)).map Y) ≤ _
  calc
    _ ≤ ∫ p, ‖D p‖ ^ 2 ∂μ.prod (stdGaussian E) := hbound
    _ ≤ (L : ℝ) ^ 2 * (t ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
        2 * t * (Module.finrank ℝ E : ℝ)) := henergy.2
    _ = _ := by ring

/-- Whenever a relative density identifies the actual Gaussian interpolation,
its conditional drift has integrable density-weighted energy and the required
numerical estimate. Only the density identity is conditional here; the field
and its energy estimate are constructed by the preceding theorem. -/
theorem exists_frozen_drift_error_of_density
    (μ ν : Measure E) [IsProbabilityMeasure μ] (U : E → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (hgrad : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ)
    (t : ℝ) (ht : 0 ≤ t) (r : E → ℝ)
    (hrmeas : Measurable r) (hr : ∀ x, 0 ≤ r x)
    (hlaw : tiltedMeasure ν r = interpolationLaw U μ t) :
    ∃ err : E → E, StronglyMeasurable err ∧
      (fun p : E × E ↦ err (ULA.malaProposal U t p.1 p.2)) =ᵐ[μ.prod (stdGaussian E)]
        (μ.prod (stdGaussian E))[frozenGradientDiscrepancy U t |
          frozenDriftSigmaAlgebra U t] ∧
      Integrable (fun y ↦ r y * ‖err y‖ ^ 2) ν ∧
      (∫ y, r y * ‖err y‖ ^ 2 ∂ν) ≤
        t ^ 2 * (L : ℝ) ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
          2 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  obtain ⟨err, herr, hcond, hint, hbound⟩ :=
    exists_frozen_drift_error μ U L hLip hgrad t ht
  rw [← hlaw] at hint hbound
  have hweighted : Integrable (fun y ↦ r y * ‖err y‖ ^ 2) ν := by
    have hequiv := integrable_withDensity_iff_integrable_smul' (μ := ν)
      hrmeas.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)
      (g := fun y ↦ ‖err y‖ ^ 2)
    have h := hequiv.mp hint
    simpa only [ENNReal.toReal_ofReal (hr _), smul_eq_mul] using h
  rw [integral_tiltedMeasure ν r hrmeas hr] at hbound
  exact ⟨err, herr, hcond, hweighted, hbound⟩

end ULA.LSI
