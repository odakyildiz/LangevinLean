import UnadjustedLangevin.LSI.EntropyEndpoint
import UnadjustedLangevin.LSI.GibbsInterpolationBound

set_option linter.style.header false

/-! # The actual initial entropy endpoint

A locally continuous upper envelope for the actual interpolation entropy is
constructed from the initial KL and score moment. Its value at zero is exactly
the initial entropy. No regularity of the initial density, initial Fisher
information, state second moment, or entropy continuity assumption is needed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Explicit upper envelope for initial interpolation entropy. Its only
denominator is nonzero near zero, and its logarithm has argument one at zero. -/
def interpolationEntropyMajorant (U : E → ℝ) (L : ℝ≥0) (μ : Measure E) (t : ℝ) : ℝ :=
  (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal +
    -((Module.finrank ℝ E : ℝ) / 2) * Real.log (1 - 4 * t * (L : ℝ)) +
    (t / (1 - 4 * t * (L : ℝ)) / 4) *
      (2 * (1 + (L : ℝ) ^ 2 * t ^ 2) * (∫ x, ‖gradient U x‖ ^ 2 ∂μ) +
        4 * t * (Module.finrank ℝ E : ℝ) * (L : ℝ) ^ 2)

@[simp]
theorem interpolationEntropyMajorant_zero (U : E → ℝ) (L : ℝ≥0) (μ : Measure E) :
    interpolationEntropyMajorant U L μ 0 =
      (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal := by
  simp [interpolationEntropyMajorant]

/-- The envelope is continuous at the only endpoint relevant to the entropy
comparison, directly from its explicit elementary formula. -/
theorem interpolationEntropyMajorant_continuousAt_zero
    (U : E → ℝ) (L : ℝ≥0) (μ : Measure E) :
    ContinuousAt (interpolationEntropyMajorant U L μ) 0 := by
  unfold interpolationEntropyMajorant
  fun_prop (disch := norm_num)

/-- The actual interpolation has finite entropy and lies below the explicit
initial envelope whenever the Gaussian comparison time is positive. -/
theorem interpolationLaw_entropy_le_majorant
    (U : E → ℝ) (L : ℝ≥0) (hL : 0 < L) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤)
    (t : ℝ) (ht : 0 < t) (hδ : 0 < 1 - 4 * t * (L : ℝ)) :
    InformationTheory.klDiv (interpolationLaw U μ t) (ULA.gibbsMeasure U) ≠ ⊤ ∧
      (InformationTheory.klDiv (interpolationLaw U μ t) (ULA.gibbsMeasure U)).toReal ≤
        interpolationEntropyMajorant U L μ t := by
  let δ := 1 - 4 * t * (L : ℝ)
  let s := t / δ
  let b := -((Module.finrank ℝ E : ℝ) / 2) * Real.log δ
  let c := s / 4
  have hs : 0 < s := div_pos ht hδ
  have hscale : s * (1 - 4 * t * (L : ℝ)) = t := by
    dsimp [s, δ]
    exact div_mul_cancel₀ t hδ.ne'
  have htilt := tiltedMeasure_interpolationRelativeDensity U (ULA.gibbsMeasure U)
    L hU hLip t ht
  have href : interpolationLaw U (ULA.gibbsMeasure U) t ≪ ULA.gibbsMeasure U := by
    rw [← htilt]
    exact withDensity_absolutelyContinuous _ _
  have hrn :
      (interpolationLaw U (ULA.gibbsMeasure U) t).rnDeriv (ULA.gibbsMeasure U) =ᵐ[
        ULA.gibbsMeasure U] fun x ↦
          ENNReal.ofReal (interpolationRelativeDensity U (ULA.gibbsMeasure U) t x) := by
    rw [← htilt]
    exact Measure.rnDeriv_withDensity _
      (interpolationRelativeDensity_measurable U (ULA.gibbsMeasure U) L hU hLip t).ennreal_ofReal
  have hbound : ∀ᵐ x ∂ULA.gibbsMeasure U,
      ((interpolationLaw U (ULA.gibbsMeasure U) t).rnDeriv (ULA.gibbsMeasure U) x).toReal ≤
        Real.exp (b + c * ‖gradient U x‖ ^ 2) := by
    filter_upwards [hrn] with x hx
    rw [hx, ENNReal.toReal_ofReal
      (interpolationRelativeDensity_pos U (ULA.gibbsMeasure U) L hU hLip t ht x).le]
    apply (interpolationRelativeDensity_gibbs_le U L hU hLip t s ht hs hscale x).trans_eq
    rw [Real.rpow_def_of_pos (div_pos hs ht), ← Real.exp_add]
    have hratio : s / t = δ⁻¹ := by
      dsimp [s]
      field_simp
    rw [hratio, Real.log_inv]
    congr 1
    dsimp [b, c]
    ring
  obtain ⟨hfinite, hb⟩ := interpolationLaw_entropy_bound_of_density_bound
    U L hL hU hLip μ hKL t ht.le b c href hbound
  obtain ⟨hgrad, _⟩ := gibbs_gradient_moment_bound_of_finite_kl U L hL hU hLip μ hKL
  obtain ⟨_, hgradt⟩ := interpolationLaw_gradient_moment U L hLip μ hgrad t ht.le
  have hmult := mul_le_mul_of_nonneg_left hgradt (show 0 ≤ c by dsimp [c]; positivity)
  refine ⟨hfinite, hb.trans ?_⟩
  dsimp [interpolationEntropyMajorant, b, c, s, δ] at *
  linarith

/-- Near zero, actual entropy is eventually bounded by the explicit continuous
envelope. This is the complete initial endpoint input to scalar comparison. -/
theorem interpolationLaw_entropy_eventually_le_majorant
    (U : E → ℝ) (L : ℝ≥0) (hL : 0 < L) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (InformationTheory.klDiv (interpolationLaw U μ t) (ULA.gibbsMeasure U)).toReal ≤
        interpolationEntropyMajorant U L μ t := by
  have hL' : 0 < (L : ℝ) := hL
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 / (8 * (L : ℝ)) :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (8 * (L : ℝ)))).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht hsmall
  have hδ : 0 < 1 - 4 * t * (L : ℝ) := by
    have h := (lt_div_iff₀ (by positivity : 0 < 8 * (L : ℝ))).mp hsmall
    nlinarith
  exact (interpolationLaw_entropy_le_majorant U L hL hU hLip μ hKL t ht hδ).2

end ULA.LSI
