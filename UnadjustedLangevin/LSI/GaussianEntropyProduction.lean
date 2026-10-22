import UnadjustedLangevin.LSI.GaussianEntropyIdentity
import UnadjustedLangevin.LSI.GaussianScorePairing
import UnadjustedLangevin.LSI.DriftError

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-! # Entropy production for the actual Gaussian interpolation

The Gaussian entropy identity supplies the actual a.e. time derivative.
Averaging the Gaussian component score gives relative Fisher information;
Young's inequality absorbs one quarter of that information and leaves the
sharp frozen-gradient discrepancy energy. All integrability and derivative
facts refer to the explicitly constructed interpolation law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace ULA.LSI
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem production_integrable_inner_of_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f g : Ω → E) (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω ↦ inner ℝ (f ω) (g ω)) P := by
  have hprod : MemLp (fun ω ↦ ‖f ω‖ * ‖g ω‖) 1 P := hf.norm.mul hg.norm
  apply (memLp_one_iff_integrable.mp hprod).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact ae_of_all _ fun ω ↦ norm_inner_le_norm (𝕜 := ℝ) _ _

/-- The relative-score energy on the independent initial/noise space is the
actual Fisher information. The map identity keeps the two integrals tied to
the concrete Gaussian interpolation. -/
theorem interpolationScoreAlongUpdate_energy_eq_fisher
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)] (L : ℝ≥0)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    (∫ p : E × E, ‖interpolationScoreAlongUpdate U μ t p‖ ^ 2
      ∂μ.prod (stdGaussian E)) =
      (relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)).toReal := by
  have hs := interpolationRelativeScore_memLp U μ L hU hLip hgrad t ht
  have hint := hs.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hY := ULA.malaProposal_measurable U t L hLip
  have hmap := integral_map hY.aemeasurable (hs.aestronglyMeasurable.norm.pow 2)
  have hpoint (p : E × E) : interpolationScoreAlongUpdate U μ t p =
      gradient (fun y ↦ Real.log (interpolationRelativeDensity U μ t y))
        (ULA.malaProposal U t p.1 p.2) :=
    interpolationRelativeScoreField_eq U μ L hU hLip t ht _
  calc
    _ = ∫ p : E × E, ‖gradient (fun y ↦ Real.log
        (interpolationRelativeDensity U μ t y)) (ULA.malaProposal U t p.1 p.2)‖ ^ 2
        ∂μ.prod (stdGaussian E) := by simp_rw [hpoint]
    _ = ∫ y, ‖gradient (fun y ↦ Real.log
        (interpolationRelativeDensity U μ t y)) y‖ ^ 2 ∂interpolationLaw U μ t := hmap.symm
    _ = _ := by
      rw [relativeFisher, tiltedMeasure_interpolationRelativeDensity U μ L hU hLip t ht,
        ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ ↦ sq_nonneg _),
        ENNReal.toReal_ofReal (integral_nonneg (fun _ ↦ sq_nonneg _))]

/-- The explicit state-space score energy is the same finite relative Fisher
information used in the logarithmic Sobolev inequality. -/
theorem interpolationRelativeScoreField_energy_eq_fisher
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)] (L : ℝ≥0)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    (∫ y, ‖interpolationRelativeScoreField U μ t y‖ ^ 2 ∂interpolationLaw U μ t) =
      (relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)).toReal := by
  have hR : MemLp (interpolationRelativeScoreField U μ t) 2 (interpolationLaw U μ t) := by
    convert interpolationRelativeScore_memLp U μ L hU hLip hgrad t ht using 1
    funext y
    exact interpolationRelativeScoreField_eq U μ L hU hLip t ht y
  have hmap := integral_map (ULA.malaProposal_measurable U t L hLip).aemeasurable
    (hR.aestronglyMeasurable.norm.pow 2)
  calc
    _ = ∫ p : E × E, ‖interpolationScoreAlongUpdate U μ t p‖ ^ 2
        ∂μ.prod (stdGaussian E) := hmap
    _ = _ := interpolationScoreAlongUpdate_energy_eq_fisher U μ L hU hLip hgrad t ht

/-- The actual frozen-gradient error/score cross term is integrable and
satisfies the one-quarter Fisher Young bound. -/
theorem interpolation_error_score_young
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)] (L : ℝ≥0)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun p : E × E ↦ inner ℝ (frozenGradientDiscrepancy U t p)
      (interpolationScoreAlongUpdate U μ t p)) (μ.prod (stdGaussian E)) ∧
      (∫ p : E × E, inner ℝ (frozenGradientDiscrepancy U t p)
        (interpolationScoreAlongUpdate U μ t p) ∂μ.prod (stdGaussian E)) ≤
        (1 / 4 : ℝ) *
          (relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)).toReal +
          t ^ 2 * (L : ℝ) ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
            2 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  let P := μ.prod (stdGaussian E)
  let D := frozenGradientDiscrepancy U t
  let S := interpolationScoreAlongUpdate U μ t
  have hY := ULA.malaProposal_measurable U t L hLip
  have hG := hgrad.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hE := frozen_gradient_error_energy μ U L hLip hG t ht.le
  have hEi : Integrable (fun p ↦ ‖D p‖ ^ 2) P := hE.1
  have hSi := (interpolationScoreAlongUpdate_memLp U μ L hU hLip hgrad t ht).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have hDm : AEStronglyMeasurable D P :=
    ((hLip.continuous.measurable.comp hY).sub
      (hLip.continuous.measurable.comp measurable_fst)).aestronglyMeasurable
  have hSm := (interpolationScoreAlongUpdate_memLp U μ L hU hLip hgrad t ht).aestronglyMeasurable
  have hCi : Integrable (fun p ↦ inner ℝ (D p) (S p)) P := by
    have h := integrable_weighted_inner_of_energy P (fun _ ↦ (1 : ℝ)) D S
      (fun _ ↦ zero_le_one) (by simpa only [one_mul] using hDm.inner hSm)
      (by simpa only [one_mul] using hSi) (by simpa only [one_mul] using hEi)
    simpa only [one_mul] using h
  refine ⟨hCi, ?_⟩
  have h := integral_weighted_inner_le_quarter_fisher_add_energy P (fun _ ↦ (1 : ℝ)) D S
    (fun _ ↦ zero_le_one) (by simpa only [one_mul] using hCi)
    (by simpa only [one_mul] using hSi) (by simpa only [one_mul] using hEi)
  simp only [one_mul] at h
  change (∫ p, inner ℝ (D p) (S p) ∂P) ≤ _
  have hF := interpolationScoreAlongUpdate_energy_eq_fisher U μ L hU hLip hgrad t ht
  change (∫ p, ‖S p‖ ^ 2 ∂P) = _ at hF
  rw [hF] at h
  have hEb : (∫ p, ‖D p‖ ^ 2 ∂P) ≤ (L : ℝ) ^ 2 *
      (t ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
        2 * t * (Module.finrank ℝ E : ℝ)) := hE.2
  nlinarith [hEb]

/-- Averaging the genuine Gaussian component score identifies the actual
entropy flux as Fisher dissipation plus the frozen-gradient discrepancy.
Every term is an integrable function of the independent initial/noise pair. -/
theorem interpolationRawEntropyFlux_eq_fisher_error
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)] (L : ℝ≥0)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    interpolationRawEntropyFlux U μ t =
      -(relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)).toReal +
        ∫ p : E × E, inner ℝ (frozenGradientDiscrepancy U t p)
          (interpolationScoreAlongUpdate U μ t p) ∂μ.prod (stdGaussian E) := by
  let P := μ.prod (stdGaussian E)
  let Y : E × E → E := fun p ↦ ULA.malaProposal U t p.1 p.2
  let R := interpolationRelativeScoreField U μ t
  let S := interpolationScoreAlongUpdate U μ t
  let GX : E × E → E := fun p ↦ gradient U p.1
  let GY : E × E → E := fun p ↦ gradient U (Y p)
  let N : E × E → E := fun p ↦ (-(1 / (2 * t)) * Real.sqrt (2 * t)) • p.2
  have hY := ULA.malaProposal_measurable U t L hLip
  have hReq : R = gradient (fun y ↦ Real.log (interpolationRelativeDensity U μ t y)) := by
    funext y
    exact interpolationRelativeScoreField_eq U μ L hU hLip t ht y
  have hRC : Continuous R := by
    rw [hReq]
    have hd := (interpolationRelativeDensity_contDiff U μ L hU hLip t ht).log
      (fun y ↦ (interpolationRelativeDensity_pos U μ L hU hLip t ht y).ne')
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hd.continuous_fderiv (by norm_num))
  have hR : MemLp R 2 (interpolationLaw U μ t) := by
    rw [hReq]
    exact interpolationRelativeScore_memLp U μ L hU hLip hgrad t ht
  have hS : MemLp S 2 P := interpolationScoreAlongUpdate_memLp U μ L hU hLip hgrad t ht
  have hGX : MemLp GX 2 P := hgrad.comp_fst (stdGaussian E)
  have hGYout := memLp_gradient_interpolationLaw U μ L hLip hgrad t ht.le
  have hGY : MemLp GY 2 P :=
    (memLp_map_measure_iff hGYout.aestronglyMeasurable hY.aemeasurable).mp hGYout
  have hz : MemLp (fun z : E ↦ z) 2 (stdGaussian E) :=
    IsGaussian.memLp_id (stdGaussian E) 2 (by norm_num)
  have hN : MemLp N 2 P :=
    (hz.comp_snd μ).const_smul (-(1 / (2 * t)) * Real.sqrt (2 * t))
  have hX := production_integrable_inner_of_memLp_two P GX S hGX hS
  have hG := production_integrable_inner_of_memLp_two P GY S hGY hS
  have hNoise := production_integrable_inner_of_memLp_two P N S hN hS
  have hOut := production_integrable_inner_of_memLp_two (interpolationLaw U μ t)
    (gradient U) R hGYout hR
  have hOutS := hR.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hMapG := integral_map hY.aemeasurable hOut.aestronglyMeasurable
  change (∫ y, inner ℝ (gradient U y) (R y) ∂interpolationLaw U μ t) =
    (∫ p, inner ℝ (GY p) (S p) ∂P) at hMapG
  have hMapS := integral_map hY.aemeasurable hOutS.aestronglyMeasurable
  change (∫ y, ‖R y‖ ^ 2 ∂interpolationLaw U μ t) = (∫ p, ‖S p‖ ^ 2 ∂P) at hMapS
  have hF := interpolationScoreAlongUpdate_energy_eq_fisher U μ L hU hLip hgrad t ht
  change (∫ p, ‖S p‖ ^ 2 ∂P) = _ at hF
  have hLeb (y : E) : inner ℝ
      (gradient (fun y ↦ Real.log (interpolationLebesgueDensity U μ t y)) y) (R y) =
        ‖R y‖ ^ 2 - inner ℝ (gradient U y) (R y) := by
    have he := gradient_log_interpolationRelativeDensity U μ L hU hLip t ht y
    rw [← hReq] at he
    have hi := congrArg (fun z : E ↦ inner ℝ z (R y)) he
    rw [inner_add_left, real_inner_self_eq_norm_sq] at hi
    linarith
  have hAvg := integral_frozenGaussianScore_pairing_independent U μ L hLip t ht R hRC hR
  change (∫ p, inner ℝ (N p) (S p) ∂P) = _ at hAvg
  have hAvg' : (∫ p, inner ℝ (N p) (S p) ∂P) =
      (relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)).toReal -
        ∫ p, inner ℝ (GY p) (S p) ∂P := by
    rw [hAvg]
    simp_rw [hLeb]
    rw [integral_sub hOutS hOut, hMapG, hMapS, hF]
  have hVel (p : E × E) : frozenGaussianVelocityField U t p = GX p + N p := by
    simp only [frozenGaussianVelocityField, GX, N, sub_eq_add_neg,
      neg_mul, neg_smul]
  have hRaw : interpolationRawEntropyFlux U μ t =
      -((∫ p, inner ℝ (GX p) (S p) ∂P) + (∫ p, inner ℝ (N p) (S p) ∂P)) := by
    unfold interpolationRawEntropyFlux
    simp_rw [hVel, inner_add_left]
    rw [integral_add hX hNoise]
  have hErr : (∫ p : E × E, inner ℝ (frozenGradientDiscrepancy U t p) (S p) ∂P) =
      (∫ p, inner ℝ (GY p) (S p) ∂P) - ∫ p, inner ℝ (GX p) (S p) ∂P := by
    change (∫ p, inner ℝ (GY p - GX p) (S p) ∂P) = _
    simp_rw [inner_sub_left]
    rw [integral_sub hG hX]
  rw [hRaw, hErr, hAvg']
  ring

/-- Pointwise entropy-production upper bound for the actual Gaussian flux.
The forcing is the exact frozen-displacement error bound. -/
theorem interpolationRawEntropyFlux_le
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)] (L : ℝ≥0)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hgrad : MemLp (gradient U) 2 μ) (t : ℝ) (ht : 0 < t) :
    interpolationRawEntropyFlux U μ t ≤
      -(3 / 4 : ℝ) *
        (relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)).toReal +
        t ^ 2 * (L : ℝ) ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
          2 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  rw [interpolationRawEntropyFlux_eq_fisher_error U μ L hU hLip hgrad t ht]
  have h := (interpolation_error_score_young U μ L hU hLip hgrad t ht).2
  linarith

/-- Actual entropy production holds almost everywhere on every finite
positive-time range. A countable family of interior intervals removes any
need for time-zero density smoothness or pointwise differentiability. -/
theorem interpolationEntropy_derivative_bound_ae
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (α : ℝ) (hα : 0 < α) (L : ℝ≥0)
    (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hLSI : IsLogSobolev (ULA.gibbsMeasure U) α)
    (hgrad : MemLp (gradient U) 2 μ) (T : ℝ) (hT : 0 < T) :
    ∀ᵐ t ∂volume, t ∈ Set.Ioo 0 T →
      deriv (actualInterpolationEntropy U μ) t ≤
        -(3 / 4 : ℝ) *
          (relativeFisher (ULA.gibbsMeasure U) (interpolationRelativeDensity U μ t)).toReal +
          t ^ 2 * (L : ℝ) ^ 2 * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
            2 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2 := by
  let : IsProbabilityMeasure (ULA.gibbsMeasure U) := hLSI.1
  have hderiv (n : ℕ) : ∀ᵐ t ∂volume, t ∈ Set.Ioo (1 / (n + 1 : ℝ)) (T + 1) →
      HasDerivAt (actualInterpolationEntropy U μ) (interpolationRawEntropyFlux U μ t) t := by
    have ha : 0 < 1 / (n + 1 : ℝ) := by positivity
    have hab : 1 / (n + 1 : ℝ) ≤ T + 1 := by
      have hden : (1 : ℝ) ≤ n + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hle : 1 / (n + 1 : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hden
      linarith
    exact (interpolationEntropy_local_chain_rule U μ α hα L hU hLip hLSI hgrad
      (1 / (n + 1 : ℝ)) (T + 1) ha hab).2
  have hall : ∀ᵐ t ∂volume, ∀ n : ℕ, t ∈ Set.Ioo (1 / (n + 1 : ℝ)) (T + 1) →
      HasDerivAt (actualInterpolationEntropy U μ) (interpolationRawEntropyFlux U μ t) t :=
    ae_all_iff.mpr hderiv
  filter_upwards [hall] with t ht
  intro ht0
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht0.1
  have hd := ht n ⟨hn, by linarith [ht0.2]⟩
  rw [hd.deriv]
  exact interpolationRawEntropyFlux_le U μ L hU hLip hgrad t ht0.1

end ULA.LSI
