import PBGSO.PartitionVariationBounds
import Mathlib.MeasureTheory.Integral.Prod

/-! # Fubini for localized pathwise drift work
Only the raw joint measurability, pathwise L¹ drift and the actual square
localization radius are needed. Time-L¹(L²) drift is not assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.PathwiseDriftFubini
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Absolute work is bounded by the original state radius times pathwise
variation, before taking any expectation. -/
theorem absolute_work_bound (T : ℝ≥0) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (x b : ℝ → E) (hx : ContinuousOn x (Icc 0 (T : ℝ)))
    (hb : IntervalIntegrable b volume 0 (T : ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc 0 (T : ℝ), ‖x t‖ ≤ C) :
    (∫ r in 0..(T : ℝ), ‖B (x r) (b r)‖) ≤
      (‖B‖ * C) * ∫ r in 0..(T : ℝ), ‖b r‖ := by
  have hi := IntegralQuadraticEnergy.bilinear_continuous_integrable B x b
    (by simpa only [uIcc_of_le T.coe_nonneg] using hx) hb
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on T.coe_nonneg hi.norm (hb.norm.const_mul _)
  intro r hr
  exact (B.le_opNorm₂ _ _).trans (by gcongr; exact hbound r hr)

/-- Original jointly measurable drift work is absolutely integrable on the
actual time/sample product, as a theorem of the localized path data. -/
theorem work_integrable (T : ℝ≥0) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (x b : ℝ → Ω → E) (C : Ω → ℝ)
    (hx : AEStronglyMeasurable (Function.uncurry x)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hb : AEStronglyMeasurable (Function.uncurry b)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hC : Integrable (fun ω => C ω ^ 2) Q)
    (hpaths : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)) ∧
      IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧ 0 ≤ C ω ∧
      (∀ t ∈ Icc 0 (T : ℝ), ‖x t ω‖ ≤ C ω) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ C ω) :
    Integrable (fun p : ℝ × Ω => B (x p.1 p.2) (b p.1 p.2))
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  let μ := volume.restrict (Ioc 0 (T : ℝ))
  let f := fun p : ℝ × Ω => B (x p.1 p.2) (b p.1 p.2)
  have hfm : AEStronglyMeasurable f (μ.prod Q) :=
    B.continuous₂.comp_aestronglyMeasurable (hx.prodMk hb)
  apply (integrable_prod_iff' hfm).mpr
  constructor
  · filter_upwards [hpaths] with ω hp
    have hi := IntegralQuadraticEnergy.bilinear_continuous_integrable B
      (fun r => x r ω) (fun r => b r ω)
      (by simpa only [uIcc_of_le T.coe_nonneg] using hp.1) hp.2.1
    exact hi.1
  · apply (hC.const_mul ‖B‖).mono' hfm.norm.prod_swap.integral_prod_right'
    filter_upwards [hpaths] with ω hp
    have hn : 0 ≤ ∫ r, ‖f (r, ω)‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    change ‖∫ r, ‖f (r, ω)‖ ∂μ‖ ≤ ‖B‖ * C ω ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    change (∫ r in Ioc 0 (T : ℝ), ‖B (x r ω) (b r ω)‖) ≤ ‖B‖ * C ω ^ 2
    rw [← intervalIntegral.integral_of_le T.coe_nonneg]
    apply (absolute_work_bound T B (fun r => x r ω) (fun r => b r ω)
      hp.1 hp.2.1 (C ω) hp.2.2.1 hp.2.2.2.1).trans
    nlinarith [mul_le_mul_of_nonneg_left hp.2.2.2.2
      (mul_nonneg (norm_nonneg B) hp.2.2.1)]

/-- The actual expected pathwise work equals the actual time integral of
expected original coefficient work, with all absolute integrability derived. -/
theorem integral_swap (T : ℝ≥0) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (x b : ℝ → Ω → E) (C : Ω → ℝ)
    (hx : AEStronglyMeasurable (Function.uncurry x)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hb : AEStronglyMeasurable (Function.uncurry b)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hC : Integrable (fun ω => C ω ^ 2) Q)
    (hpaths : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)) ∧
      IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧ 0 ≤ C ω ∧
      (∀ t ∈ Icc 0 (T : ℝ), ‖x t ω‖ ≤ C ω) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ C ω) :
    (∫ ω, (∫ r in 0..(T : ℝ), B (x r ω) (b r ω)) ∂Q) =
      ∫ r in 0..(T : ℝ), (∫ ω, B (x r ω) (b r ω) ∂Q) := by
  have hi := work_integrable Q T B x b C hx hb hC hpaths
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  exact (integral_integral_swap hi).symm

end PBGSO.PathwiseDriftFubini
