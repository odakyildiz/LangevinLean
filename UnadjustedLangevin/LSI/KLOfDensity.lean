import UnadjustedLangevin.LSI.EntropyFlow
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option linter.style.header false

/-!
# Relative entropy and Fisher information of a specified density

The relative density is identified with the Radon-Nikodym derivative, so the
entropy formulas below concern Mathlib's actual Kullback-Leibler divergence.
Integrability of `r * log r` supplies a finite-KL proof before taking `toReal`.
The corresponding Fisher formula also retains its integrability hypothesis.
All measure-change facts need only a measurable nonnegative density; a smooth
positive density is a special case.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ULA.LSI

variable {E : Type*} [MeasurableSpace E]

/-- Integration against a specified relative density is weighted integration
against the reference measure. -/
theorem integral_tiltedMeasure (ν : Measure E) (r : E → ℝ)
    (hmeas : Measurable r) (hr : ∀ x, 0 ≤ r x) (g : E → ℝ) :
    (∫ x, g x ∂tiltedMeasure ν r) = ∫ x, r x * g x ∂ν := by
  unfold tiltedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hr _), smul_eq_mul]

/-- Integrability of the logarithm under the tilted measure is precisely
integrability of the entropy integrand under the reference measure. -/
theorem integrable_log_tiltedMeasure_iff (ν : Measure E) (r : E → ℝ)
    (hmeas : Measurable r) (hr : ∀ x, 0 ≤ r x) :
    Integrable (fun x ↦ Real.log (r x)) (tiltedMeasure ν r) ↔
      Integrable (fun x ↦ r x * Real.log (r x)) ν := by
  unfold tiltedMeasure
  have h := integrable_withDensity_iff_integrable_smul' (μ := ν)
    hmeas.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)
    (g := fun x ↦ Real.log (r x))
  simpa only [ENNReal.toReal_ofReal (hr _), smul_eq_mul] using h

/-- The actual log-likelihood ratio is the logarithm of the chosen density,
almost everywhere for the induced measure. -/
theorem llr_tiltedMeasure_ae_eq_log (ν : Measure E) [SigmaFinite ν]
    (r : E → ℝ) (hmeas : Measurable r) (hr : ∀ x, 0 ≤ r x) :
    llr (tiltedMeasure ν r) ν =ᵐ[tiltedMeasure ν r] fun x ↦ Real.log (r x) := by
  have hac : tiltedMeasure ν r ≪ ν := withDensity_absolutelyContinuous _ _
  have hRN := Measure.rnDeriv_withDensity ν hmeas.ennreal_ofReal
  filter_upwards [hac.ae_le hRN] with x hx
  simp only [llr, tiltedMeasure, hx, ENNReal.toReal_ofReal (hr x)]

/-- An integrable entropy integrand gives finite actual KL divergence.
The absolute-continuity and log-likelihood-integrability obligations are proved. -/
theorem klDiv_tiltedMeasure_ne_top (ν : Measure E) [SigmaFinite ν]
    (r : E → ℝ) (hmeas : Measurable r) (hr : ∀ x, 0 ≤ r x)
    (hint : Integrable (fun x ↦ r x * Real.log (r x)) ν) :
    InformationTheory.klDiv (tiltedMeasure ν r) ν ≠ ⊤ := by
  apply InformationTheory.klDiv_ne_top
    (withDensity_absolutelyContinuous _ _)
  exact ((integrable_log_tiltedMeasure_iff ν r hmeas hr).mpr hint).congr
    (llr_tiltedMeasure_ae_eq_log ν r hmeas hr).symm

/-- For a normalized relative density with integrable entropy integrand,
actual KL entropy equals the ordinary integral of `r * log r`. -/
theorem densityEntropy_eq_integral (ν : Measure E) [IsProbabilityMeasure ν]
    (r : E → ℝ) (hmeas : Measurable r) (hr : ∀ x, 0 ≤ r x)
    (hprob : IsProbabilityMeasure (tiltedMeasure ν r))
    (hint : Integrable (fun x ↦ r x * Real.log (r x)) ν) :
    densityEntropy ν r = ∫ x, r x * Real.log (r x) ∂ν := by
  let := hprob
  have hlog := (integrable_log_tiltedMeasure_iff ν r hmeas hr).mpr hint
  have hllr := llr_tiltedMeasure_ae_eq_log ν r hmeas hr
  have hllr_int := hlog.congr hllr.symm
  have hac : tiltedMeasure ν r ≪ ν := withDensity_absolutelyContinuous _ _
  unfold densityEntropy
  rw [InformationTheory.toReal_klDiv hac hllr_int]
  simp only [probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae hllr]
  exact integral_tiltedMeasure ν r hmeas hr _

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Integrability of the squared relative score gives finite Fisher information. -/
theorem relativeFisher_ne_top (ν : Measure E) (r : E → ℝ)
    (hint : Integrable
      (fun x ↦ ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2) (tiltedMeasure ν r)) :
    relativeFisher ν r ≠ ⊤ := by
  exact ne_of_lt ((hasFiniteIntegral_iff_ofReal
    (ae_of_all _ fun x ↦ sq_nonneg ‖gradient (fun y ↦ Real.log (r y)) x‖)).mp
      hint.hasFiniteIntegral)

/-- Finite relative Fisher information, written as a weighted integral against
the reference measure rather than an integral against the tilted measure. -/
theorem relativeFisher_toReal_eq_integral (ν : Measure E) (r : E → ℝ)
    (hmeas : Measurable r) (hr : ∀ x, 0 ≤ r x)
    (hint : Integrable
      (fun x ↦ ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2) (tiltedMeasure ν r)) :
    (relativeFisher ν r).toReal =
      ∫ x, r x * ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2 ∂ν := by
  calc
    (relativeFisher ν r).toReal =
        ∫ x, ‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2 ∂tiltedMeasure ν r :=
      (integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun x ↦ sq_nonneg ‖gradient (fun y ↦ Real.log (r y)) x‖)
        hint.aestronglyMeasurable).symm
    _ = _ := integral_tiltedMeasure ν r hmeas hr _

end ULA.LSI
