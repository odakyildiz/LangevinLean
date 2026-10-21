import UnadjustedLangevin.GaussianProposalDensity
import Mathlib.MeasureTheory.Measure.Prod

set_option linter.style.header false

/-! # Joint law of a state and its Gaussian Euler proposal

This is the product-measure transport step used to turn Metropolis acceptance
into a symmetric Lebesgue density on pairs of states.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The full current/proposal pair law has the pointwise Gaussian density.
Only measurability of its state-dependent center is required. -/
theorem gaussian_proposal_pair_density (μ : Measure H) (c : H → H)
    (hc : Measurable c) (h : ℝ) (hh : 0 < h) :
    (μ.prod (stdGaussian H)).map (fun z : H × H ↦
      (z.1, c z.1 + Real.sqrt (2 * h) • z.2)) =
      (μ.prod volume).withDensity (fun z : H × H ↦ gaussianProposalDensity h (c z.1) z.2) := by
  have hm : Measurable (fun z : H × H ↦
      (z.1, c z.1 + Real.sqrt (2 * h) • z.2)) := by fun_prop
  have hd : Measurable (fun z : H × H ↦ gaussianProposalDensity h (c z.1) z.2) := by
    unfold gaussianProposalDensity
    fun_prop
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply (hm hs),
    withDensity_apply _ hs, ← lintegral_indicator hs _,
    lintegral_prod _ (hd.indicator hs).aemeasurable]
  apply lintegral_congr_ae
  exact ae_of_all _ fun x ↦ by
    have hxs : MeasurableSet ((Prod.mk x) ⁻¹' s) := measurable_prodMk_left hs
    have hi : (fun y : H ↦ s.indicator
        (fun z : H × H ↦ gaussianProposalDensity h (c z.1) z.2) (x, y)) =
        ((Prod.mk x) ⁻¹' s).indicator (gaussianProposalDensity h (c x)) := by
      funext y
      rfl
    dsimp only
    rw [hi, lintegral_indicator hxs,
      ← withDensity_apply (gaussianProposalDensity h (c x)) hxs,
      ← gaussian_proposal_density h hh (c x),
      Measure.map_apply (by fun_prop) hxs]
    rfl

end ULA
