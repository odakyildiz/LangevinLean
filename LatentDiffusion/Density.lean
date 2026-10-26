import LatentDiffusion.Variational
import UnadjustedLangevin.LSI.KLOfDensity

/-!
# The actual log-density integral and the normalized KL free energy

This file proves the normalization bridge rather than assuming the variational
identity. A nonnegative relative density has finite actual KL whenever its
entropy integrand is integrable. An unnormalized positive base density `ρ` with
positive finite normalizer `Z` gives an actual probability posterior `ρ/Z`.
For a normalized relative density `r`, the trial law has actual base density
`rρ/Z`. Its integral of `log ((rρ/Z)/ρ)` is proved to equal `KL - log Z`.
Zero values of `r` are handled on the trial law's full-measure positive support.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace LatentDiffusion.Density

variable {E : Type*} [MeasurableSpace E]

/-- The actual measure whose density relative to `ν` is the supplied real `r`. -/
def densityMeasure (ν : Measure E) (r : E → ℝ) : Measure E :=
  ν.withDensity (fun x ↦ ENNReal.ofReal (r x))

/-- Normalization follows from the ordinary integral of the nonnegative density. -/
theorem densityMeasure_isProbability (ν : Measure E) (r : E → ℝ)
    (hr : ∀ x, 0 ≤ r x) (hint : Integrable r ν) (hmass : (∫ x, r x ∂ν) = 1) :
    IsProbabilityMeasure (densityMeasure ν r) := by
  constructor
  unfold densityMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hr), hmass]
  norm_num

/-- Points where the relative density vanishes have zero induced probability. -/
theorem density_positive_ae (ν : Measure E) (r : E → ℝ) (hmeas : Measurable r) :
    ∀ᵐ x ∂densityMeasure ν r, 0 < r x := by
  apply (ae_withDensity_iff hmeas.ennreal_ofReal).mpr
  exact ae_of_all _ fun x hx ↦ lt_of_not_ge
    (fun hnonpos ↦ hx (ENNReal.ofReal_eq_zero.mpr hnonpos))

/-- Finite actual KL and the shifted logarithm integral follow from a normalized
relative density and an integrable entropy integrand. No KL identity is a premise. -/
theorem relative_density_freeEnergy (π : Measure E) [IsProbabilityMeasure π]
    (r : E → ℝ) (hmeas : Measurable r) (hr : ∀ x, 0 ≤ r x)
    (hprob : IsProbabilityMeasure (densityMeasure π r))
    (hentropy : Integrable (fun x ↦ r x * Real.log (r x)) π) (logZ : ℝ) :
    InformationTheory.klDiv (densityMeasure π r) π ≠ ⊤ ∧
      Integrable (fun x ↦ Real.log (r x) - logZ) (densityMeasure π r) ∧
      (∫ x, (Real.log (r x) - logZ) ∂densityMeasure π r) =
        (InformationTheory.klDiv (densityMeasure π r) π).toReal - logZ := by
  let := hprob
  have hlog : Integrable (fun x ↦ Real.log (r x)) (densityMeasure π r) :=
    (ULA.LSI.integrable_log_tiltedMeasure_iff π r hmeas hr).mpr hentropy
  have hfinite : InformationTheory.klDiv (densityMeasure π r) π ≠ ⊤ :=
    ULA.LSI.klDiv_tiltedMeasure_ne_top π r hmeas hr hentropy
  have hkl : (InformationTheory.klDiv (densityMeasure π r) π).toReal =
      ∫ x, Real.log (r x) ∂densityMeasure π r := by
    have h := ULA.LSI.densityEntropy_eq_integral π r hmeas hr hprob hentropy
    change (InformationTheory.klDiv (densityMeasure π r) π).toReal =
      ∫ x, r x * Real.log (r x) ∂π at h
    rw [h]
    exact (ULA.LSI.integral_tiltedMeasure π r hmeas hr _).symm
  refine ⟨hfinite, hlog.sub (integrable_const _), ?_⟩
  rw [integral_sub hlog (integrable_const logZ), ← hkl]
  simp

/-- The posterior is the actual base measure tilted by `ρ/Z`. -/
def posteriorMeasure (ν : Measure E) (ρ : E → ℝ) (Z : ℝ) : Measure E :=
  densityMeasure ν (fun x ↦ ρ x / Z)

/-- An ordinary positive finite normalizer constructs a posterior probability. -/
theorem posteriorMeasure_isProbability (ν : Measure E) (ρ : E → ℝ) (Z : ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hZ : 0 < Z) (hint : Integrable ρ ν)
    (hnorm : (∫ x, ρ x ∂ν) = Z) :
    IsProbabilityMeasure (posteriorMeasure ν ρ Z) := by
  apply densityMeasure_isProbability ν (fun x ↦ ρ x / Z)
    (fun x ↦ div_nonneg (hρ x) hZ.le) (hint.div_const Z)
  rw [integral_div, hnorm, div_self (ne_of_gt hZ)]

/-- The trial density relative to the original base measure. -/
def trialDensity (ρ r : E → ℝ) (Z : ℝ) (x : E) : ℝ := r x * (ρ x / Z)

/-- Composition of actual density changes gives the claimed base density. -/
theorem trialMeasure_eq_relative (ν : Measure E) (ρ r : E → ℝ) (Z : ℝ)
    (hρmeas : Measurable ρ) (hrmeas : Measurable r)
    (hρ : ∀ x, 0 ≤ ρ x) (hZ : 0 < Z) :
    densityMeasure ν (trialDensity ρ r Z) =
      densityMeasure (posteriorMeasure ν ρ Z) r := by
  unfold posteriorMeasure densityMeasure trialDensity
  rw [← withDensity_mul ν (hρmeas.div_const Z).ennreal_ofReal hrmeas.ennreal_ofReal]
  apply withDensity_congr_ae
  apply ae_of_all
  intro x
  simp only [Pi.mul_apply]
  rw [mul_comm (r x), ENNReal.ofReal_mul (div_nonneg (hρ x) hZ.le)]

/-- The ordinary log ratio agrees on the trial law's actual support. -/
theorem log_trial_ratio_ae (ν : Measure E) (ρ r : E → ℝ) (Z : ℝ)
    (hrmeas : Measurable r) (hρ : ∀ x, 0 < ρ x) (hZ : 0 < Z) :
    (fun x ↦ Real.log (trialDensity ρ r Z x / ρ x)) =ᵐ[
      densityMeasure (posteriorMeasure ν ρ Z) r]
        fun x ↦ Real.log (r x) - Real.log Z := by
  filter_upwards [density_positive_ae (posteriorMeasure ν ρ Z) r hrmeas] with x hx
  have hid : trialDensity ρ r Z x / ρ x = r x / Z := by
    unfold trialDensity
    field_simp [ne_of_gt (hρ x), ne_of_gt hZ]
  rw [hid, Real.log_div (ne_of_gt hx) (ne_of_gt hZ)]

/-- A genuine density-normalization bridge for the source log-density free
energy. The posterior, trial law, finite KL, and integral identity are derived.
The assumptions are density measurability, positivity, normalization and entropy
integrability; the desired variational identity is not assumed. -/
theorem density_freeEnergy_eq_kl (ν : Measure E) (ρ r : E → ℝ) (Z : ℝ)
    (hρmeas : Measurable ρ) (hrmeas : Measurable r)
    (hρ : ∀ x, 0 < ρ x) (hr : ∀ x, 0 ≤ r x) (hZ : 0 < Z)
    (hρint : Integrable ρ ν) (hZeq : (∫ x, ρ x ∂ν) = Z)
    (hrint : Integrable r (posteriorMeasure ν ρ Z))
    (hrmass : (∫ x, r x ∂posteriorMeasure ν ρ Z) = 1)
    (hentropy : Integrable (fun x ↦ r x * Real.log (r x)) (posteriorMeasure ν ρ Z)) :
    let π := posteriorMeasure ν ρ Z
    let q := densityMeasure ν (trialDensity ρ r Z)
    IsProbabilityMeasure π ∧ IsProbabilityMeasure q ∧
      InformationTheory.klDiv q π ≠ ⊤ ∧
      Integrable (fun x ↦ Real.log (trialDensity ρ r Z x / ρ x)) q ∧
      (∫ x, Real.log (trialDensity ρ r Z x / ρ x) ∂q) =
        (InformationTheory.klDiv q π).toReal - Real.log Z := by
  dsimp only
  have hπ := posteriorMeasure_isProbability ν ρ Z (fun x ↦ (hρ x).le) hZ hρint hZeq
  let := hπ
  have hq := densityMeasure_isProbability (posteriorMeasure ν ρ Z) r hr hrint hrmass
  have heq := trialMeasure_eq_relative ν ρ r Z hρmeas hrmeas (fun x ↦ (hρ x).le) hZ
  rw [heq]
  have hfree := relative_density_freeEnergy (posteriorMeasure ν ρ Z) r hrmeas hr hq
    hentropy (Real.log Z)
  have hlog := log_trial_ratio_ae ν ρ r Z hrmeas hρ hZ
  exact ⟨hπ, hq, hfree.1, hfree.2.1.congr hlog.symm,
    (integral_congr_ae hlog).trans hfree.2.2⟩

/-- The same bridge in the manuscript's literal base-density integral form:
`∫ f log(f/ρ) dν`, with the actual trial density `f=rρ/Z`. Integrability of this
base-measure expression is also derived, rather than separately assumed. -/
theorem density_weighted_freeEnergy_eq_kl (ν : Measure E) (ρ r : E → ℝ) (Z : ℝ)
    (hρmeas : Measurable ρ) (hrmeas : Measurable r)
    (hρ : ∀ x, 0 < ρ x) (hr : ∀ x, 0 ≤ r x) (hZ : 0 < Z)
    (hρint : Integrable ρ ν) (hZeq : (∫ x, ρ x ∂ν) = Z)
    (hrint : Integrable r (posteriorMeasure ν ρ Z))
    (hrmass : (∫ x, r x ∂posteriorMeasure ν ρ Z) = 1)
    (hentropy : Integrable (fun x ↦ r x * Real.log (r x)) (posteriorMeasure ν ρ Z)) :
    let π := posteriorMeasure ν ρ Z
    let f := trialDensity ρ r Z
    let q := densityMeasure ν f
    InformationTheory.klDiv q π ≠ ⊤ ∧
      Integrable (fun x ↦ f x * Real.log (f x / ρ x)) ν ∧
      (∫ x, f x * Real.log (f x / ρ x) ∂ν) =
        (InformationTheory.klDiv q π).toReal - Real.log Z := by
  dsimp only
  obtain ⟨_, _, hfinite, hlog, hidentity⟩ :=
    density_freeEnergy_eq_kl ν ρ r Z hρmeas hrmeas hρ hr hZ hρint hZeq
      hrint hrmass hentropy
  have hfmeas : Measurable (trialDensity ρ r Z) := hrmeas.mul (hρmeas.div_const Z)
  have hf : ∀ x, 0 ≤ trialDensity ρ r Z x :=
    fun x ↦ mul_nonneg (hr x) (div_nonneg (hρ x).le hZ.le)
  have hiff := integrable_withDensity_iff_integrable_smul' (μ := ν)
    hfmeas.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)
    (g := fun x ↦ Real.log (trialDensity ρ r Z x / ρ x))
  have hweighted : Integrable
      (fun x ↦ trialDensity ρ r Z x * Real.log (trialDensity ρ r Z x / ρ x)) ν := by
    have hh := hiff.mp hlog
    simpa only [ENNReal.toReal_ofReal (hf _), smul_eq_mul] using hh
  refine ⟨hfinite, hweighted, ?_⟩
  exact (ULA.LSI.integral_tiltedMeasure ν (trialDensity ρ r Z) hfmeas hf
    (fun x ↦ Real.log (trialDensity ρ r Z x / ρ x))).symm.trans hidentity

end LatentDiffusion.Density
