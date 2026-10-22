import UnadjustedLangevin.Coupling
import UnadjustedLangevin.GibbsScore
import UnadjustedLangevin.LSI.InterpolationDensity

set_option linter.style.header false

/-! # Gradient moments from a finite-cost transport coupling

The target score moment follows from first-order smoothness in `GibbsScore`.
This file transports that estimate to another law and proves its gradient
square integrability. An explicit entropy-cost estimate gives the exact moment
coefficient used by the ULA theorem. The implication from LSI to that transport
estimate is not asserted here.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] in
/-- A Lipschitz gradient and a finite-cost coupling transfer the target's
square-integrable score to the first marginal and give the direct moment bound. -/
theorem gradient_moment_bound_of_coupling
    (U : E → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (μ ν : Measure E) (c : ULA.Coupling μ ν)
    (hcost : Integrable (fun p : E × E ↦ ‖p.1 - p.2‖ ^ 2) c.joint)
    (htarget : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) ν) :
    Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ ∧
      (∫ x, ‖gradient U x‖ ^ 2 ∂μ) ≤
        2 * (L : ℝ) ^ 2 * (∫ p : E × E, ‖p.1 - p.2‖ ^ 2 ∂c.joint) +
          2 * (∫ x, ‖gradient U x‖ ^ 2 ∂ν) := by
  have hgmeas := (hLip.continuous.norm.pow 2).stronglyMeasurable
  have hsecond : Integrable (fun p : E × E ↦ ‖gradient U p.2‖ ^ 2) c.joint := by
    have htarget' : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) (c.joint.map Prod.snd) := by
      rwa [c.snd]
    exact (integrable_map_measure hgmeas.aestronglyMeasurable
      measurable_snd.aemeasurable).mp htarget'
  have hpoint (p : E × E) : ‖gradient U p.1‖ ^ 2 ≤
      2 * (L : ℝ) ^ 2 * ‖p.1 - p.2‖ ^ 2 + 2 * ‖gradient U p.2‖ ^ 2 := by
    have hLip' : ‖gradient U p.1 - gradient U p.2‖ ≤ (L : ℝ) * ‖p.1 - p.2‖ := by
      simpa only [dist_eq_norm] using hLip.dist_le_mul p.1 p.2
    have htriangle := norm_add_le (gradient U p.1 - gradient U p.2) (gradient U p.2)
    rw [sub_add_cancel] at htriangle
    have hnonneg : 0 ≤ (L : ℝ) * ‖p.1 - p.2‖ := by positivity
    have hnorm : ‖gradient U p.1‖ ≤ (L : ℝ) * ‖p.1 - p.2‖ + ‖gradient U p.2‖ := by
      linarith
    have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
    nlinarith [sq_nonneg ((L : ℝ) * ‖p.1 - p.2‖ - ‖gradient U p.2‖)]
  have hmajor : Integrable (fun p : E × E ↦
      2 * (L : ℝ) ^ 2 * ‖p.1 - p.2‖ ^ 2 + 2 * ‖gradient U p.2‖ ^ 2) c.joint :=
    (hcost.const_mul _).add (hsecond.const_mul _)
  have hfirst : Integrable (fun p : E × E ↦ ‖gradient U p.1‖ ^ 2) c.joint := by
    apply hmajor.mono' (hgmeas.comp_measurable measurable_fst).aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint p
  have hμ : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ := by
    rw [← c.fst]
    exact (integrable_map_measure hgmeas.aestronglyMeasurable
      measurable_fst.aemeasurable).mpr hfirst
  have hfirst_marginal : (∫ p : E × E, ‖gradient U p.1‖ ^ 2 ∂c.joint) =
      ∫ x, ‖gradient U x‖ ^ 2 ∂μ := by
    have hmap := integral_map_of_stronglyMeasurable (μ := c.joint) measurable_fst hgmeas
    rw [c.fst] at hmap
    exact hmap.symm
  have hsecond_marginal : (∫ p : E × E, ‖gradient U p.2‖ ^ 2 ∂c.joint) =
      ∫ x, ‖gradient U x‖ ^ 2 ∂ν := by
    have hmap := integral_map_of_stronglyMeasurable (μ := c.joint) measurable_snd hgmeas
    rw [c.snd] at hmap
    exact hmap.symm
  refine ⟨hμ, ?_⟩
  have h := integral_mono hfirst hmajor hpoint
  rw [integral_add (hcost.const_mul _) (hsecond.const_mul _),
    integral_const_mul, integral_const_mul, hfirst_marginal, hsecond_marginal] at h
  exact h

/-- For the normalized Gibbs target the target score moment is derived from
smoothness, giving `Gμ ≤ 2 L² cost + 2 n L` and gradient square integrability. -/
theorem gibbs_gradient_moment_bound_of_coupling
    (U : E → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (μ : Measure E) (c : ULA.Coupling μ (ULA.gibbsMeasure U))
    (hcost : Integrable (fun p : E × E ↦ ‖p.1 - p.2‖ ^ 2) c.joint) :
    Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ ∧
      (∫ x, ‖gradient U x‖ ^ 2 ∂μ) ≤
        2 * (L : ℝ) ^ 2 * (∫ p : E × E, ‖p.1 - p.2‖ ^ 2 ∂c.joint) +
          2 * (Module.finrank ℝ E : ℝ) * (L : ℝ) := by
  have hZ := gibbsPartition_ne_top_of_probability U
  have ht := (ULA.memLp_gradient_gibbsMeasure U L hU hLip hZ).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  obtain ⟨hint, hbound⟩ := gradient_moment_bound_of_coupling U L hLip μ
    (ULA.gibbsMeasure U) c hcost ht
  have htarget := ULA.integral_norm_sq_gradient_gibbs_le U L hU hLip hZ
  exact ⟨hint, by nlinarith⟩

/-- An explicitly supplied entropy-cost coupling yields the precise gradient
moment estimate used by the LSI interpolation proof. The transport estimate
is a displayed hypothesis; this theorem does not prove LSI implies Talagrand. -/
theorem gibbs_gradient_moment_bound_of_entropy_coupling
    (U : E → ℝ) (L : ℝ≥0) (hU : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U))
    [IsProbabilityMeasure (ULA.gibbsMeasure U)]
    (μ : Measure E) (c : ULA.Coupling μ (ULA.gibbsMeasure U))
    (hcost : Integrable (fun p : E × E ↦ ‖p.1 - p.2‖ ^ 2) c.joint)
    (α : ℝ) (_hα : 0 < α)
    (_hKL : InformationTheory.klDiv μ (ULA.gibbsMeasure U) ≠ ⊤)
    (htransport : (∫ p : E × E, ‖p.1 - p.2‖ ^ 2 ∂c.joint) ≤
      (2 / α) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal) :
    Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ ∧
      (∫ x, ‖gradient U x‖ ^ 2 ∂μ) ≤
        (4 * (L : ℝ) ^ 2 / α) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal +
          2 * (Module.finrank ℝ E : ℝ) * (L : ℝ) := by
  obtain ⟨hint, hbound⟩ := gibbs_gradient_moment_bound_of_coupling U L hU hLip μ c hcost
  have htransport' := mul_le_mul_of_nonneg_left htransport
    (by positivity : 0 ≤ 2 * (L : ℝ) ^ 2)
  refine ⟨hint, hbound.trans ?_⟩
  have heq : 2 * (L : ℝ) ^ 2 *
      ((2 / α) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal) =
        (4 * (L : ℝ) ^ 2 / α) * (InformationTheory.klDiv μ (ULA.gibbsMeasure U)).toReal := by
    ring
  rw [heq] at htransport'
  linarith

end ULA.LSI
