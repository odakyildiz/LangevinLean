import UnadjustedLangevin.LSI.EntropyDerivative
import UnadjustedLangevin.LSI.KLOfDensity
import UnadjustedLangevin.LSI.DriftError

set_option linter.style.header false

/-! # Explicit analytic regularity for the entropy calculation

The local data below give sufficient hypotheses for differentiation under the
entropy integral. They contain no entropy derivative or convergence bound.
Together with an admissible weak Fokker-Planck identity they prove the entropy
production estimate used by the ULA interpolation argument.

Constructing these data for a Gaussian ULA interpolation, and proving its weak
equation for noncompact entropy tests, remain separate analytic obligations.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace ULA.LSI

/-- Sufficient local domination and differentiability data for the relative
entropy integrand. All bounds refer to a common neighborhood in time. -/
structure LocalEntropyRegularity {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (r rdot : ℝ → X → ℝ) (t : ℝ) where
  neighborhood : Set ℝ
  neighborhood_mem : neighborhood ∈ 𝓝 t
  bound : X → ℝ
  measurable : ∀ᶠ u in 𝓝 t,
    AEStronglyMeasurable (fun x ↦ r u x * Real.log (r u x)) ν
  integrable : Integrable (fun x ↦ r t x * Real.log (r t x)) ν
  derivative_measurable : AEStronglyMeasurable
    (fun x ↦ rdot t x * (Real.log (r t x) + 1)) ν
  derivative_bound : ∀ᵐ x ∂ν, ∀ u ∈ neighborhood,
    ‖rdot u x * (Real.log (r u x) + 1)‖ ≤ bound x
  bound_integrable : Integrable bound ν
  positive : ∀ᵐ x ∂ν, ∀ u ∈ neighborhood, 0 < r u x
  derivative : ∀ᵐ x ∂ν, ∀ u ∈ neighborhood,
    HasDerivAt (fun v ↦ r v x) (rdot u x) u

/-- The time derivative of the entropy integral follows from local analytic
data, rather than being a field of those data. -/
theorem LocalEntropyRegularity.hasDerivAt_entropy
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {r rdot : ℝ → X → ℝ} {t : ℝ}
    (data : LocalEntropyRegularity ν r rdot t) :
    Integrable (fun x ↦ rdot t x * (Real.log (r t x) + 1)) ν ∧
      HasDerivAt (fun u ↦ ∫ x, r u x * Real.log (r u x) ∂ν)
        (∫ x, rdot t x * (Real.log (r t x) + 1) ∂ν) t :=
  hasDerivAt_integral_mul_log_of_dominated ν data.neighborhood_mem
    data.measurable data.integrable data.derivative_measurable
    data.derivative_bound data.bound_integrable data.positive data.derivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E]

/-- Differentiating entropy and testing the forced weak equation proves its
production estimate. The remaining error-energy estimate is not assumed here. -/
theorem entropy_derivative_bound_of_regular_weak_equation
    (ν : Measure E) (r rdot : ℝ → E → ℝ) (t : ℝ) (err : E → E)
    (data : LocalEntropyRegularity ν r rdot t)
    (hpos : ∀ x, 0 < r t x) (hsmooth : ContDiff ℝ 1 (r t))
    (hfisher_int : Integrable
      (fun x ↦ r t x * ‖gradient (fun y ↦ Real.log (r t y)) x‖ ^ 2) ν)
    (henergy_int : Integrable (fun x ↦ r t x * ‖err x‖ ^ 2) ν)
    (herror_meas : AEStronglyMeasurable
      (fun x ↦ r t x * inner ℝ (err x)
        (gradient (fun y ↦ Real.log (r t y)) x)) ν)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ →
      Integrable (fun x ↦ rdot t x * ψ x) ν →
      Integrable (fun x ↦ inner ℝ (gradient (r t) x) (gradient ψ x)) ν →
      Integrable (fun x ↦ r t x * inner ℝ (err x) (gradient ψ x)) ν →
      (∫ x, rdot t x * ψ x ∂ν) =
        -(∫ x, inner ℝ (gradient (r t) x) (gradient ψ x) ∂ν) +
          ∫ x, r t x * inner ℝ (err x) (gradient ψ x) ∂ν) :
    HasDerivAt (fun u ↦ ∫ x, r u x * Real.log (r u x) ∂ν)
      (∫ x, rdot t x * (Real.log (r t x) + 1) ∂ν) t ∧
    (∫ x, rdot t x * (Real.log (r t x) + 1) ∂ν) ≤
      -(3 / 4 : ℝ) *
        (∫ x, r t x * ‖gradient (fun y ↦ Real.log (r t y)) x‖ ^ 2 ∂ν) +
        ∫ x, r t x * ‖err x‖ ^ 2 ∂ν := by
  have hd := data.hasDerivAt_entropy
  exact ⟨hd.2, entropy_production_le_of_forced_weak_identity ν (r t) (rdot t) err
    hpos hsmooth hd.1 hfisher_int henergy_int herror_meas hweak⟩

variable [BorelSpace E]

omit [CompleteSpace E] in
/-- Density-level regularity gives finite actual KL, before any real-valued
entropy comparison is made. -/
theorem klDiv_finite_of_localRegularity
    (ν : Measure E) [IsProbabilityMeasure ν] (r rdot : ℝ → E → ℝ) (t : ℝ)
    (data : LocalEntropyRegularity ν r rdot t)
    (hpos : ∀ x, 0 < r t x) (hsmooth : ContDiff ℝ 1 (r t)) :
    InformationTheory.klDiv (tiltedMeasure ν (r t)) ν ≠ ⊤ :=
  klDiv_tiltedMeasure_ne_top ν (r t) hsmooth.continuous.measurable
    (fun x ↦ (hpos x).le) data.integrable

omit [CompleteSpace E] in
/-- Continuity of actual KL along a normalized regular density path follows
from differentiation of its entropy integral and the KL density formula. -/
theorem densityEntropy_continuousOn_of_regular
    (ν : Measure E) [IsProbabilityMeasure ν] (r rdot : ℝ → E → ℝ) (T : ℝ)
    (data : ∀ t ∈ Icc 0 T, LocalEntropyRegularity ν r rdot t)
    (hpos : ∀ t ∈ Icc 0 T, ∀ x, 0 < r t x)
    (hsmooth : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (r t))
    (hprob : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (tiltedMeasure ν (r t))) :
    ContinuousOn (fun t ↦ densityEntropy ν (r t)) (Icc 0 T) := by
  have hcont : ContinuousOn (fun t ↦ ∫ x, r t x * Real.log (r t x) ∂ν)
      (Icc 0 T) := fun t ht ↦
    (data t ht).hasDerivAt_entropy.2.continuousAt.continuousWithinAt
  apply hcont.congr
  intro t ht
  exact densityEntropy_eq_integral ν (r t) (hsmooth t ht).continuous.measurable
    (fun x ↦ (hpos t ht x).le) (hprob t ht) (data t ht).integrable

omit [CompleteSpace E] in
/-- The right derivative of actual KL is computed from the density path.
Only times on the finite interpolation interval need to be normalized. -/
theorem densityEntropy_hasDerivWithinAt_of_regular
    (ν : Measure E) [IsProbabilityMeasure ν] (r rdot : ℝ → E → ℝ) (T t : ℝ)
    (ht : t ∈ Ico 0 T)
    (data : ∀ u ∈ Icc 0 T, LocalEntropyRegularity ν r rdot u)
    (hpos : ∀ u ∈ Icc 0 T, ∀ x, 0 < r u x)
    (hsmooth : ∀ u ∈ Icc 0 T, ContDiff ℝ 1 (r u))
    (hprob : ∀ u ∈ Icc 0 T, IsProbabilityMeasure (tiltedMeasure ν (r u))) :
    HasDerivWithinAt (fun u ↦ densityEntropy ν (r u))
      (∫ x, rdot t x * (Real.log (r t x) + 1) ∂ν) (Ici t) t := by
  have heq : ∀ u ∈ Icc 0 T, densityEntropy ν (r u) =
      ∫ x, r u x * Real.log (r u x) ∂ν := by
    intro u hu
    exact densityEntropy_eq_integral ν (r u) (hsmooth u hu).continuous.measurable
      (fun x ↦ (hpos u hu x).le) (hprob u hu) (data u hu).integrable
  have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  have hnear : (fun u ↦ densityEntropy ν (r u)) =ᶠ[𝓝[Ici t] t]
      (fun u ↦ ∫ x, r u x * Real.log (r u x) ∂ν) := by
    have hupp : ∀ᶠ u in 𝓝[Ici t] t, u < T :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)
    filter_upwards [self_mem_nhdsWithin, hupp] with u hu hupper
    exact heq u ⟨ht.1.trans hu, hupper.le⟩
  exact (data t ht').hasDerivAt_entropy.2.hasDerivWithinAt.congr_of_eventuallyEq
    hnear (heq t ht')

/-- The actual KL right derivative and its Fisher/drift bound follow from
local domination and the admissible weak equation. This discharges the
continuity/differentiation part of an entropy interpolation argument; a bound
on the remaining drift energy must still be proved separately. -/
theorem densityEntropy_derivative_bound_of_regular_weak_equation
    (ν : Measure E) [IsProbabilityMeasure ν] (r rdot : ℝ → E → ℝ) (T t : ℝ)
    (ht : t ∈ Ico 0 T) (err : E → E)
    (data : ∀ u ∈ Icc 0 T, LocalEntropyRegularity ν r rdot u)
    (hpos : ∀ u ∈ Icc 0 T, ∀ x, 0 < r u x)
    (hsmooth : ∀ u ∈ Icc 0 T, ContDiff ℝ 1 (r u))
    (hprob : ∀ u ∈ Icc 0 T, IsProbabilityMeasure (tiltedMeasure ν (r u)))
    (hfisher_int : Integrable
      (fun x ↦ ‖gradient (fun y ↦ Real.log (r t y)) x‖ ^ 2)
      (tiltedMeasure ν (r t)))
    (henergy_int : Integrable (fun x ↦ r t x * ‖err x‖ ^ 2) ν)
    (herror_meas : AEStronglyMeasurable
      (fun x ↦ r t x * inner ℝ (err x)
        (gradient (fun y ↦ Real.log (r t y)) x)) ν)
    (hweak : ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ →
      Integrable (fun x ↦ rdot t x * ψ x) ν →
      Integrable (fun x ↦ inner ℝ (gradient (r t) x) (gradient ψ x)) ν →
      Integrable (fun x ↦ r t x * inner ℝ (err x) (gradient ψ x)) ν →
      (∫ x, rdot t x * ψ x ∂ν) =
        -(∫ x, inner ℝ (gradient (r t) x) (gradient ψ x) ∂ν) +
          ∫ x, r t x * inner ℝ (err x) (gradient ψ x) ∂ν) :
    HasDerivWithinAt (fun u ↦ densityEntropy ν (r u))
      (∫ x, rdot t x * (Real.log (r t x) + 1) ∂ν) (Ici t) t ∧
    (∫ x, rdot t x * (Real.log (r t x) + 1) ∂ν) ≤
      -(3 / 4 : ℝ) * (relativeFisher ν (r t)).toReal +
        ∫ x, r t x * ‖err x‖ ^ 2 ∂ν := by
  have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  have hmeas := (hsmooth t ht').continuous.measurable
  have hr : ∀ x, 0 ≤ r t x := fun x ↦ (hpos t ht' x).le
  have hweighted : Integrable
      (fun x ↦ r t x * ‖gradient (fun y ↦ Real.log (r t y)) x‖ ^ 2) ν := by
    have hequiv := integrable_withDensity_iff_integrable_smul' (μ := ν)
      hmeas.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)
      (g := fun x ↦ ‖gradient (fun y ↦ Real.log (r t y)) x‖ ^ 2)
    have h := hequiv.mp hfisher_int
    simpa only [ENNReal.toReal_ofReal (hr _), smul_eq_mul] using h
  have hprod := entropy_derivative_bound_of_regular_weak_equation ν r rdot t err
    (data t ht') (hpos t ht') (hsmooth t ht') hweighted henergy_int herror_meas hweak
  rw [← relativeFisher_toReal_eq_integral ν (r t) hmeas hr hfisher_int] at hprod
  exact ⟨densityEntropy_hasDerivWithinAt_of_regular ν r rdot T t ht data
    hpos hsmooth hprob, hprod.2⟩

end ULA.LSI
