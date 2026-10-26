import LatentDiffusion.Density
import LatentDiffusion.SourceCalculus
import LatentDiffusion.SourceResults
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option linter.style.header false

/-! # Regular density models and the literal variational problem

All posterior laws below are constructed from the given densities. Arbitrary
finite-KL trial probability laws are represented by their actual Radon–Nikodym
derivatives. The additional assumptions are positivity, measurability,
normalization and finite entropy; a KL identity is never an input.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace LatentDiffusion.RegularVariational

variable {A Z : Type*} [MeasurableSpace Z] {M : ℕ}

/-- A regular unnormalized density model, with its actual positive normalizer. -/
structure DensityModel (A Z : Type*) [MeasurableSpace Z] (M : ℕ) (ν : Measure Z) where
  density : A → Fin M → Z → ℝ
  measurable : ∀ a i, Measurable (density a i)
  positive : ∀ a i z, 0 < density a i z
  integrable : ∀ a i, Integrable (density a i) ν
  mass_positive : ∀ a i, 0 < ∫ z, density a i z ∂ν

variable {ν : Measure Z}

def DensityModel.mass (D : DensityModel A Z M ν) (a : A) (i : Fin M) : ℝ :=
  ∫ z, D.density a i z ∂ν

def DensityModel.posterior (D : DensityModel A Z M ν) (a : A) (i : Fin M) :
    ProbabilityMeasure Z :=
  ⟨Density.posteriorMeasure ν (D.density a i) (D.mass a i),
    Density.posteriorMeasure_isProbability ν (D.density a i) (D.mass a i)
      (fun z ↦ (D.positive a i z).le) (D.mass_positive a i) (D.integrable a i) rfl⟩

def DensityModel.family (D : DensityModel A Z M ν) : PosteriorFamily A Z M where
  logEvidence a := (M : ℝ)⁻¹ * ∑ i, Real.log (D.mass a i)
  posterior := D.posterior

/-- The actual Radon–Nikodym density of an arbitrary trial law. -/
def relativeDensity (π q : ProbabilityMeasure Z) (z : Z) : ℝ :=
  ((q : Measure Z).rnDeriv (π : Measure Z) z).toReal

theorem rn_density_realizes (π q : ProbabilityMeasure Z)
    (hfinite : InformationTheory.klDiv (q : Measure Z) (π : Measure Z) ≠ ⊤) :
    Density.densityMeasure (π : Measure Z) (relativeDensity π q) = (q : Measure Z) := by
  obtain ⟨hac, _⟩ := InformationTheory.klDiv_ne_top_iff.mp hfinite
  rw [← Measure.withDensity_rnDeriv_eq (q : Measure Z) (π : Measure Z) hac]
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_lt_top (q : Measure Z) (π : Measure Z)] with z hz
  exact ENNReal.ofReal_toReal hz.ne

/-- Finite KL supplies the complete normalized, entropy-integrable RN domain. -/
theorem rn_density_domain (π q : ProbabilityMeasure Z)
    (hfinite : InformationTheory.klDiv (q : Measure Z) (π : Measure Z) ≠ ⊤) :
    Measurable (relativeDensity π q) ∧
    (∀ z, 0 ≤ relativeDensity π q z) ∧
    Integrable (relativeDensity π q) (π : Measure Z) ∧
    (∫ z, relativeDensity π q z ∂(π : Measure Z)) = 1 ∧
    Integrable (fun z ↦ relativeDensity π q z * Real.log (relativeDensity π q z))
      (π : Measure Z) := by
  obtain ⟨hac, hint⟩ := InformationTheory.klDiv_ne_top_iff.mp hfinite
  refine ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, Measure.integrable_toReal_rnDeriv, ?_, ?_⟩
  · simpa only [probReal_univ, relativeDensity] using Measure.integral_toReal_rnDeriv hac
  · exact (integrable_rnDeriv_mul_log_iff hac).mpr hint

/-- The trial density relative to the original reference measure. -/
def DensityModel.trialDensity (D : DensityModel A Z M ν) (a : A)
    (q : Fin M → ProbabilityMeasure Z) (i : Fin M) : Z → ℝ :=
  Density.trialDensity (D.density a i) (relativeDensity (D.posterior a i) (q i)) (D.mass a i)

/-- The literal density integral used in the source paper. -/
def DensityModel.literalEnergy (D : DensityModel A Z M ν) (a : A)
    (q : Fin M → ProbabilityMeasure Z) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i, ∫ z, D.trialDensity a q i z *
    Real.log (D.trialDensity a q i z / D.density a i z) ∂ν

/-- Every finite-KL trial law has the actual source base density and integral.
No prescribed relative density or desired normalization identity is assumed. -/
theorem DensityModel.literal_integral (D : DensityModel A Z M ν) (a : A)
    (q : Fin M → ProbabilityMeasure Z) (hadm : D.family.Admissible a q) (i : Fin M) :
    Density.densityMeasure ν (D.trialDensity a q i) = (q i : Measure Z) ∧
    Integrable (fun z ↦ D.trialDensity a q i z *
      Real.log (D.trialDensity a q i z / D.density a i z)) ν ∧
    (∫ z, D.trialDensity a q i z * Real.log (D.trialDensity a q i z / D.density a i z) ∂ν) =
      (InformationTheory.klDiv (q i : Measure Z) (D.posterior a i : Measure Z)).toReal -
        Real.log (D.mass a i) := by
  have hfinite := hadm i
  obtain ⟨hmeas, hnonneg, hint, hmass, hent⟩ :=
    rn_density_domain (D.posterior a i) (q i) hfinite
  have hreal := rn_density_realizes (D.posterior a i) (q i) hfinite
  have htrial := Density.trialMeasure_eq_relative ν (D.density a i)
    (relativeDensity (D.posterior a i) (q i)) (D.mass a i) (D.measurable a i) hmeas
    (fun z ↦ (D.positive a i z).le) (D.mass_positive a i)
  change Density.densityMeasure ν (D.trialDensity a q i) = _ at htrial
  have heq : Density.densityMeasure ν (D.trialDensity a q i) = (q i : Measure Z) :=
    htrial.trans hreal
  have h := Density.density_weighted_freeEnergy_eq_kl ν (D.density a i)
    (relativeDensity (D.posterior a i) (q i)) (D.mass a i) (D.measurable a i) hmeas
    (D.positive a i) hnonneg (D.mass_positive a i) (D.integrable a i) rfl hint hmass hent
  dsimp only at h
  change InformationTheory.klDiv (Density.densityMeasure ν (D.trialDensity a q i))
      (D.posterior a i : Measure Z) ≠ ⊤ ∧
    Integrable (fun z ↦ D.trialDensity a q i z *
      Real.log (D.trialDensity a q i z / D.density a i z)) ν ∧
    (∫ z, D.trialDensity a q i z * Real.log (D.trialDensity a q i z / D.density a i z) ∂ν) =
      (InformationTheory.klDiv (Density.densityMeasure ν (D.trialDensity a q i))
        (D.posterior a i : Measure Z)).toReal - Real.log (D.mass a i) at h
  rw [heq] at h
  exact ⟨heq, h.2.1, h.2.2⟩

theorem DensityModel.literalEnergy_eq (D : DensityModel A Z M ν) (a : A)
    (q : Fin M → ProbabilityMeasure Z) (hadm : D.family.Admissible a q) :
    D.literalEnergy a q = D.family.freeEnergy a q := by
  unfold literalEnergy
  simp_rw [(D.literal_integral a q hadm _).2.2]
  simp only [Finset.sum_sub_distrib, mul_sub, PosteriorFamily.freeEnergy, family]
  ring

/-- Corrected source Proposition: actual finite-KL laws and the literal
density integral, with the normalized posterior uniquely identified. -/
theorem DensityModel.literal_minimizers_iff (D : DensityModel A Z M ν) (hM : 0 < M)
    (a : A) (q : Fin M → ProbabilityMeasure Z) :
    (D.family.Admissible a q ∧ ∀ b r, D.family.Admissible b r →
      D.literalEnergy a q ≤ D.literalEnergy b r) ↔
    (∀ b, D.family.logEvidence b ≤ D.family.logEvidence a) ∧ q = D.posterior a := by
  have hequiv : (D.family.Admissible a q ∧ ∀ b r, D.family.Admissible b r →
      D.literalEnergy a q ≤ D.literalEnergy b r) ↔ D.family.IsGlobalMin a q := by
    constructor
    · rintro ⟨hadm, h⟩
      refine ⟨hadm, fun b r hr ↦ ?_⟩
      simpa only [D.literalEnergy_eq a q hadm, D.literalEnergy_eq b r hr] using h b r hr
    · rintro ⟨hadm, h⟩
      refine ⟨hadm, fun b r hr ↦ ?_⟩
      simpa only [D.literalEnergy_eq a q hadm, D.literalEnergy_eq b r hr] using h b r hr
  exact hequiv.trans (D.family.global_minimizers_iff hM a q)

/-- The same source equivalence on a specified law domain, in particular the
paper's finite-second-moment domain. Only posterior membership is needed; no
extension of the minimization problem to inadmissible trial laws is used. -/
theorem DensityModel.literal_minimizers_on_iff (D : DensityModel A Z M ν) (hM : 0 < M)
    (domain : (Fin M → ProbabilityMeasure Z) → Prop)
    (hposterior : ∀ a, domain (D.posterior a)) (a : A) (q : Fin M → ProbabilityMeasure Z) :
    (D.family.Admissible a q ∧ domain q ∧ ∀ b r, D.family.Admissible b r → domain r →
      D.literalEnergy a q ≤ D.literalEnergy b r) ↔
    (∀ b, D.family.logEvidence b ≤ D.family.logEvidence a) ∧ q = D.posterior a := by
  have hpostenergy (b : A) : D.family.freeEnergy b (D.posterior b) =
      -D.family.logEvidence b := D.family.posterior_freeEnergy b
  constructor
  · rintro ⟨hadm, _, hmin⟩
    have hpost := D.family.posterior_admissible a
    have he : D.family.freeEnergy a q = -D.family.logEvidence a := by
      apply le_antisymm _ (D.family.lower_bound a q)
      have h := hmin a (D.posterior a) hpost (hposterior a)
      rw [D.literalEnergy_eq a q hadm, D.literalEnergy_eq a (D.posterior a) hpost,
        hpostenergy] at h
      exact h
    refine ⟨fun b ↦ ?_, (D.family.equality_iff hM a q hadm).mp he⟩
    have h := hmin b (D.posterior b) (D.family.posterior_admissible b) (hposterior b)
    rw [D.literalEnergy_eq a q hadm,
      D.literalEnergy_eq b (D.posterior b) (D.family.posterior_admissible b),
      he, hpostenergy] at h
    linarith
  · rintro ⟨hmax, rfl⟩
    have hpost := D.family.posterior_admissible a
    refine ⟨hpost, hposterior a, fun b r hr _ ↦ ?_⟩
    rw [D.literalEnergy_eq a (D.posterior a) hpost,
      D.literalEnergy_eq b r hr, hpostenergy]
    exact (neg_le_neg (hmax b)).trans (D.family.lower_bound b r)

/-- Lower semicontinuity follows from primitive density convergence and an
integrable entropy-energy envelope, rather than being an assumed conclusion. -/
theorem literalEnergy_tendsto_of_dominated
    (ν : Measure Z) (q : ℕ → Z → ℝ) (q₀ : Z → ℝ)
    (U : ℕ → Z → ℝ) (U₀ bound : Z → ℝ)
    (hq : ∀ n, Measurable (q n)) (hU : ∀ n, Measurable (U n))
    (hbound : ∀ n, ∀ᵐ z ∂ν,
      |q n z * Real.log (q n z) + q n z * U n z| ≤ bound z)
    (hint : Integrable bound ν)
    (hqlim : ∀ᵐ z ∂ν, Tendsto (fun n ↦ q n z) atTop (𝓝 (q₀ z)))
    (hUlim : ∀ᵐ z ∂ν, Tendsto (fun n ↦ U n z) atTop (𝓝 (U₀ z))) :
    Tendsto (fun n ↦ SourceCalculus.densityFreeEnergy ν (q n) (U n)) atTop
      (𝓝 (SourceCalculus.densityFreeEnergy ν q₀ U₀)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := ν) (l := (atTop : Filter ℕ))
    (F := fun n z ↦ q n z * Real.log (q n z) + q n z * U n z)
    (f := fun z ↦ q₀ z * Real.log (q₀ z) + q₀ z * U₀ z) bound
    (Eventually.of_forall fun n ↦ ((hq n).mul (hq n).log |>.add ((hq n).mul (hU n))).aestronglyMeasurable)
    (Eventually.of_forall fun n ↦ by simpa only [Real.norm_eq_abs] using hbound n) hint ?_
  · simpa only [SourceCalculus.densityFreeEnergy, mul_add] using h
  · filter_upwards [hqlim, hUlim] with z hqz hUz
    exact ((Real.continuous_mul_log.continuousAt.tendsto.comp hqz).add (hqz.mul hUz))

section DensityTopology

variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]

/-- Pointwise continuous densities and potentials, with a common local
integrable envelope for entropy and potential energy. These are ordinary
dominated-convergence hypotheses; neither continuity nor semicontinuity of
the energy integral is assumed. X may carry the source product-Wasserstein
topology on a regular, uniformly dominated class of densities. -/
structure DominatedDensityChart (X Z : Type*) [TopologicalSpace X]
    [MeasurableSpace Z] (ν : Measure Z) where
  density : X → Z → ℝ
  potential : X → Z → ℝ
  density_measurable : ∀ x, Measurable (density x)
  potential_measurable : ∀ x, Measurable (potential x)
  density_continuous : ∀ z, Continuous (fun x ↦ density x z)
  potential_continuous : ∀ z, Continuous (fun x ↦ potential x z)
  envelope : ∀ x, ∃ bound : Z → ℝ, Integrable bound ν ∧
    ∀ᶠ y in 𝓝 x, ∀ᵐ z ∂ν,
      |density y z * Real.log (density y z) + density y z * potential y z| ≤ bound z

def DominatedDensityChart.energy (D : DominatedDensityChart X Z ν) (x : X) : ℝ :=
  SourceCalculus.densityFreeEnergy ν (D.density x) (D.potential x)

theorem DominatedDensityChart.continuous_energy (D : DominatedDensityChart X Z ν) :
    Continuous D.energy := by
  rw [continuous_iff_continuousAt]
  intro x
  change Tendsto (fun y ↦ D.energy y) (𝓝 x) (𝓝 (D.energy x))
  obtain ⟨bound, hint, hbound⟩ := D.envelope x
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := ν) (l := 𝓝 x)
    (F := fun y z ↦ D.density y z * Real.log (D.density y z) +
      D.density y z * D.potential y z)
    (f := fun z ↦ D.density x z * Real.log (D.density x z) +
      D.density x z * D.potential x z) bound
    (Eventually.of_forall fun y ↦
      ((D.density_measurable y).mul (D.density_measurable y).log |>.add
        ((D.density_measurable y).mul (D.potential_measurable y))).aestronglyMeasurable)
    (by simpa only [Real.norm_eq_abs] using hbound) hint
    (ae_of_all _ fun z ↦
      ((Real.continuous_mul_log.comp (D.density_continuous z)).tendsto x).add
        (((D.density_continuous z).tendsto x).mul ((D.potential_continuous z).tendsto x)))
  simpa only [energy, SourceCalculus.densityFreeEnergy, mul_add] using h

theorem DominatedDensityChart.lowerSemicontinuous_energy
    (D : DominatedDensityChart X Z ν) : LowerSemicontinuous D.energy :=
  D.continuous_energy.lowerSemicontinuous

/-- The corrected compactness result for the actual density energy. -/
theorem DominatedDensityChart.cauchy_minimizer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (D : DominatedDensityChart X Z ν) (Fstar : ℝ)
    (hstar : ∀ x, Fstar ≤ D.energy x) (x : ℕ → X) (hx : CauchySeq x)
    (hvalue : Tendsto (fun n ↦ D.energy (x n)) atTop (𝓝 Fstar)) :
    ∃ xstar, Tendsto x atTop (𝓝 xstar) ∧ D.energy xstar = Fstar ∧
      ∀ y, D.energy xstar ≤ D.energy y :=
  SourceResults.cauchy_minimizing_sequence D.energy Fstar
    D.lowerSemicontinuous_energy hstar x hx hvalue

end DensityTopology

end LatentDiffusion.RegularVariational
