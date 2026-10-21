import UnadjustedLangevin.GibbsScore
import UnadjustedLangevin.LpDrift

set_option linter.style.header false

/-! # The reference score bound is derived from its Gibbs law

A random variable with Gibbs law inherits the sharp score moment proved from
the potential assumptions. Stationarity itself is not established by this
moment-transfer lemma.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace ULA

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The exact score norm used in Dalalyan's reference argument follows from
first-order smoothness and the stated Gibbs law, without a moment hypothesis. -/
theorem lpDrift_norm_le_of_gibbs_law
    (U : H → ℝ) (L : ℝ≥0) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (hZ : gibbsPartition U ≠ ⊤)
    (Y : Lp H 2 P) (hlaw : P.map Y = gibbsMeasure U) :
    ‖lpDrift P (gradient U) hLip Y‖ ≤
      Real.sqrt ((L : ℝ) * (Module.finrank ℝ H : ℝ)) := by
  have he : (∫ x, ‖gradient U x‖ ^ 2 ∂P.map Y) =
      ∫ ω, ‖gradient U (Y ω)‖ ^ 2 ∂P := by
    exact integral_map (Lp.aestronglyMeasurable Y).aemeasurable
      ((hLip.continuous.norm.pow 2).aestronglyMeasurable)
  rw [hlaw] at he
  apply lpDrift_norm_le_sqrt P (gradient U) hLip Y
  rw [← he]
  exact integral_norm_sq_gradient_gibbs_le U L hdiff hLip hZ

/-- The strong-convexity form also discharges finite normalization internally. -/
theorem lpDrift_norm_le_of_strongConvex_gibbs_law
    (U : H → ℝ) (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U))
    (Y : Lp H 2 P) (hlaw : P.map Y = gibbsMeasure U) :
    ‖lpDrift P (gradient U) hLip Y‖ ≤
      Real.sqrt ((L : ℝ) * (Module.finrank ℝ H : ℝ)) :=
  lpDrift_norm_le_of_gibbs_law P U L hdiff hLip
    (gibbsPartition_ne_top U m hm hdiff hsc) Y hlaw

end ULA
