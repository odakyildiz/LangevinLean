import UnadjustedLangevin.LSI.GaussianTimeDerivative
import UnadjustedLangevin.LSI.ScoreCalculus

set_option linter.style.header false

/-! # Joint time-space measurability for Gaussian entropy calculus

The actual kernel and its explicit spatial derivative have measurable
parameter integrals. This provides a measurable relative-score field on all
times which agrees with the actual derivative at every positive time. The
extension at other times is used only for measurable integral notation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem interpolationLebesgueDensity_joint_measurable
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U)) :
    Measurable (fun p : ℝ × E ↦ interpolationLebesgueDensity U μ p.1 p.2) := by
  have hg := hLip.continuous.measurable
  have hn := gaussianProposalNormalizer_measurable (E := E)
  have hk : Measurable (fun p : (ℝ × E) × E ↦
      ULA.gaussianProposalDensity p.1.1 (p.2 - p.1.1 • gradient U p.2) p.1.2) := by
    unfold ULA.gaussianProposalDensity
    fun_prop
  exact hk.lintegral_prod_right.ennreal_toReal

theorem interpolationRelativeDensity_joint_measurable
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) :
    Measurable (fun p : ℝ × E ↦ interpolationRelativeDensity U μ p.1 p.2) := by
  have hp := interpolationLebesgueDensity_joint_measurable U μ L hLip
  have hUc := hU.continuous.measurable
  unfold interpolationRelativeDensity
  fun_prop

theorem interpolationLebesgueDensityDeriv_joint_stronglyMeasurable
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U)) :
    StronglyMeasurable (fun p : ℝ × E ↦ interpolationLebesgueDensityDeriv U μ p.1 p.2) := by
  have hg := hLip.continuous.measurable
  have hn := gaussianProposalNormalizer_measurable (E := E)
  change Measurable (fun t : ℝ ↦ ULA.radialGaussianNormalizer (H := E) (1 / (4 * t))) at hn
  have hk : StronglyMeasurable (fun p : (ℝ × E) × E ↦
      realGaussianKernelDeriv (1 / (4 * p.1.1))
        (p.2 - p.1.1 • gradient U p.2) p.1.2) := by
    unfold realGaussianKernelDeriv realGaussianKernel
    have hres : StronglyMeasurable (fun p : (ℝ × E) × E ↦
        p.1.2 - (p.2 - p.1.1 • gradient U p.2)) := by fun_prop
    have hinner := (innerSL ℝ (E := E)).continuous.comp_stronglyMeasurable hres
    have hnorm : Measurable (fun p : (ℝ × E) × E ↦
        ULA.radialGaussianNormalizer (H := E) (1 / (4 * p.1.1))) :=
      hn.comp measurable_fst.fst
    have hexp : Measurable (fun p : (ℝ × E) × E ↦
        Real.exp (-(1 / (4 * p.1.1)) * ‖p.1.2 - (p.2 - p.1.1 • gradient U p.2)‖ ^ 2)) := by
      fun_prop
    have hscalar : Measurable (fun p : (ℝ × E) × E ↦
        (ULA.radialGaussianNormalizer (H := E) (1 / (4 * p.1.1)) *
          Real.exp (-(1 / (4 * p.1.1)) * ‖p.1.2 - (p.2 - p.1.1 • gradient U p.2)‖ ^ 2)) *
            (-2 * (1 / (4 * p.1.1)))) :=
      (hnorm.mul hexp).mul (by fun_prop)
    exact hscalar.stronglyMeasurable.smul hinner
  exact hk.integral_prod_right

/-- A jointly measurable version of the relative score, identified with the
actual derivative at every positive time by the following theorem. -/
def interpolationRelativeScoreField (U : E → ℝ) (μ : Measure E) (t : ℝ) (y : E) : E :=
  gradient U y + (interpolationLebesgueDensity U μ t y)⁻¹ •
    (InnerProductSpace.toDual ℝ E).symm (interpolationLebesgueDensityDeriv U μ t y)

theorem interpolationRelativeScoreField_stronglyMeasurable
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U)) :
    StronglyMeasurable (fun p : ℝ × E ↦ interpolationRelativeScoreField U μ p.1 p.2) := by
  have hgrad := hLip.continuous.measurable
  have hp := interpolationLebesgueDensity_joint_measurable U μ L hLip
  have hD := interpolationLebesgueDensityDeriv_joint_stronglyMeasurable U μ L hLip
  unfold interpolationRelativeScoreField
  have hD' : StronglyMeasurable (fun p : ℝ × E ↦
      (InnerProductSpace.toDual ℝ E).symm (interpolationLebesgueDensityDeriv U μ p.1 p.2)) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp_stronglyMeasurable hD
  exact (hgrad.comp measurable_snd).stronglyMeasurable.add (hp.inv.stronglyMeasurable.smul hD')

theorem interpolationRelativeScoreField_eq
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (L : ℝ≥0) (hU : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (t : ℝ) (ht : 0 < t) (y : E) :
    interpolationRelativeScoreField U μ t y =
      gradient (fun y ↦ Real.log (interpolationRelativeDensity U μ t y)) y := by
  rw [gradient_log_interpolationRelativeDensity U μ L hU hLip t ht y,
    gradient_log_of_pos
      (hasFDerivAt_interpolationLebesgueDensity U μ L hLip t ht y).differentiableAt
      (interpolationLebesgueDensity_pos U μ L hLip t ht y)]
  unfold interpolationRelativeScoreField gradient
  rw [(hasFDerivAt_interpolationLebesgueDensity U μ L hLip t ht y).fderiv]

end ULA.LSI
