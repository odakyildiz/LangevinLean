import UnadjustedLangevin.Projection

set_option linter.style.header false


/-! # Moving the center of a finite projected quadratic error

The extended norm inequality is proved first. Finite moments are retained
before converting to real numbers or a square-root integral.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ProximalLangevin

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Minkowski controls the change of a parameter center, with infinite
moments still represented by the extended norm. -/
theorem projectedRMS_center_le (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E →L[ℝ] F) (a b : F) :
    ULA.Hilbert.projectedRMS μ T a ≤
      ULA.Hilbert.projectedRMS μ T b + ENNReal.ofReal ‖b - a‖ := by
  have heq : (fun x ↦ T x - a) = (fun x ↦ T x - b) + (fun _ : E ↦ b - a) := by
    funext x
    simp only [Pi.add_apply]
    abel
  unfold ULA.Hilbert.projectedRMS
  rw [heq]
  have h := eLpNorm_add_le (μ := μ) (f := fun x ↦ T x - b)
    (g := fun _ : E ↦ b - a) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simpa [eLpNorm_const', ofReal_norm] using h

/-- A finite error about one center implies finiteness about every center. -/
theorem projectedRMS_center_finite (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E →L[ℝ] F) (a b : F)
    (hb : ULA.Hilbert.projectedRMS μ T b ≠ ⊤) :
    ULA.Hilbert.projectedRMS μ T a ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hb, ENNReal.ofReal_ne_top⟩)
    (projectedRMS_center_le μ T a b)

/-- The usual real-valued center-change inequality, guarded by a proved
finite moment at the comparison center. -/
theorem projectedRMSReal_center_le (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E →L[ℝ] F) (a b : F)
    (hb : ULA.Hilbert.projectedRMS μ T b ≠ ⊤) :
    ULA.Hilbert.projectedRMSReal μ T a ≤
      ULA.Hilbert.projectedRMSReal μ T b + ‖b - a‖ := by
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hb, ENNReal.ofReal_ne_top⟩)
    (projectedRMS_center_le μ T a b)
  simpa only [ULA.Hilbert.projectedRMSReal, ENNReal.toReal_add hb ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (norm_nonneg _)] using h

/-- The integral form follows after both finite quadratic moments have been
established. -/
theorem sqrt_integral_center_le (μ : Measure E) [IsProbabilityMeasure μ]
    (T : E →L[ℝ] F) (a b : F)
    (hb : ULA.Hilbert.projectedRMS μ T b ≠ ⊤) :
    Real.sqrt (∫ x, ‖T x - a‖ ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, ‖T x - b‖ ^ 2 ∂μ) + ‖b - a‖ := by
  have ha := projectedRMS_center_finite μ T a b hb
  simpa only [ULA.Hilbert.projectedRMSReal_eq_sqrt_integral μ T a ha,
    ULA.Hilbert.projectedRMSReal_eq_sqrt_integral μ T b hb] using
      projectedRMSReal_center_le μ T a b hb

end ProximalLangevin
