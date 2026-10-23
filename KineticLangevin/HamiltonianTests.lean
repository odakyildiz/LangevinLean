import KineticLangevin.HamiltonianWeak
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Bounded-test control from exact corrected invariance

An invariant corrected proposal provides a weak approximation without an
incorrect small-jump assumption on rejection. The rejection jump may flip
the entire velocity; a bounded test still changes by at most twice its bound.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal ENNReal
namespace KineticLangevin

variable {H : Type*} [MeasurableSpace H]

/-- Splitting an initial measure into acceptance and rejection weights
retains all of its mass. -/
theorem acceptance_measure_split (π : Measure H) (a : H → ℝ) (ha : Measurable a)
    (ha0 : ∀ z, 0 ≤ a z) (ha1 : ∀ z, a z ≤ 1) :
    π.withDensity (fun z ↦ ENNReal.ofReal (a z)) +
      π.withDensity (fun z ↦ ENNReal.ofReal (1-a z)) = π := by
  rw [← withDensity_add_left ha.ennreal_ofReal]
  have he : (fun z ↦ ENNReal.ofReal (a z)+ENNReal.ofReal (1-a z)) = 1 := by
    funext z
    rw [← ENNReal.ofReal_add (ha0 z) (sub_nonneg.mpr (ha1 z))]
    simp
  change π.withDensity (fun z ↦ ENNReal.ofReal (a z)+ENNReal.ofReal (1-a z)) = π
  rw [he,withDensity_one]

/-- An exact corrected measure identity gives the corresponding ordinary
integral identity for every bounded measurable complex test. -/
theorem correctedMeasure_test_identity (π : Measure H) [IsFiniteMeasure π]
    (V R : H → H) (hV : Measurable V) (hR : Measurable R)
    (a : H → ℝ) (ha : Measurable a) (ha0 : ∀ z, 0 ≤ a z) (ha1 : ∀ z, a z ≤ 1)
    (hstationary : (π.withDensity (fun z ↦ ENNReal.ofReal (a z))).map V +
      (π.withDensity (fun z ↦ ENNReal.ofReal (1-a z))).map R = π)
    (F : H → ℂ) (hF : Measurable F) (C : ℝ) (hbound : ∀ z, ‖F z‖ ≤ C) :
    (∫ z, F z ∂π) = (∫ z, a z • F (V z) ∂π) +
      (∫ z, (1-a z) • F (R z) ∂π) := by
  let A := π.withDensity (fun z ↦ ENNReal.ofReal (a z))
  let B := π.withDensity (fun z ↦ ENNReal.ofReal (1-a z))
  have hsplit : A+B=π := acceptance_measure_split π a ha ha0 ha1
  have hA : A ≤ π := by rw [← hsplit]; exact Measure.le_add_right le_rfl
  have hB : B ≤ π := by rw [← hsplit]; exact Measure.le_add_left le_rfl
  letI : IsFiniteMeasure A := isFiniteMeasure_of_le π hA
  letI : IsFiniteMeasure B := isFiniteMeasure_of_le π hB
  have hiA : Integrable F (A.map V) :=
    Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hbound)
  have hiB : Integrable F (B.map R) :=
    Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ hbound)
  have heA : (∫ z, F z ∂A.map V) = ∫ z, a z • F (V z) ∂π := by
    rw [integral_map hV.aemeasurable hF.aestronglyMeasurable]
    dsimp [A]
    rw [integral_withDensity_eq_integral_toReal_smul ha.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (ha0 _),Complex.real_smul]
  have heB : (∫ z, F z ∂B.map R) = ∫ z, (1-a z) • F (R z) ∂π := by
    rw [integral_map hR.aemeasurable hF.aestronglyMeasurable]
    dsimp [B]
    rw [integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun z ↦ ENNReal.ofReal (1-a z)) from
        ((measurable_const.sub ha).ennreal_ofReal))
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (sub_nonneg.mpr (ha1 _)),Complex.real_smul]
  calc
    _ = ∫ z, F z ∂(A.map V+B.map R) := by rw [hstationary]
    _ = (∫ z, F z ∂A.map V)+(∫ z, F z ∂B.map R) := integral_add_measure hiA hiB
    _ = _ := by rw [heA,heB]

/-- A bounded test controls the actual rejected velocity flip, yielding a
weak one-step error bounded by twice the test bound times rejection mass. -/
theorem correctedMeasure_weak_error (π : Measure H) [IsFiniteMeasure π]
    (V R : H → H) (hV : Measurable V) (hR : Measurable R)
    (a : H → ℝ) (ha : Measurable a) (ha0 : ∀ z, 0 ≤ a z) (ha1 : ∀ z, a z ≤ 1)
    (hstationary : (π.withDensity (fun z ↦ ENNReal.ofReal (a z))).map V +
      (π.withDensity (fun z ↦ ENNReal.ofReal (1-a z))).map R = π)
    (F : H → ℂ) (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z, ‖F z‖ ≤ C) :
    ‖(∫ z, F (V z) ∂π)-(∫ z, F z ∂π)‖ ≤ 2*C*(∫ z, 1-a z ∂π) := by
  have hb (z : H) : 0 ≤ 1-a z := sub_nonneg.mpr (ha1 z)
  have hb1 (z : H) : 1-a z ≤ 1 := by linarith [ha0 z]
  have hFV : Integrable (fun z ↦ F (V z)) π :=
    Integrable.of_bound (hF.comp hV).aestronglyMeasurable C
      (ae_of_all _ fun z ↦ hbound (V z))
  have hA : Integrable (fun z ↦ a z • F (V z)) π := by
    apply Integrable.of_bound (ha.smul (hF.comp hV)).aestronglyMeasurable C
    filter_upwards [] with z
    change ‖a z • F (V z)‖ ≤ C
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (ha0 z)]
    nlinarith [hbound (V z),norm_nonneg (F (V z)),ha0 z,ha1 z]
  have hB : Integrable (fun z ↦ (1-a z) • F (R z)) π := by
    apply Integrable.of_bound ((measurable_const.sub ha).smul (hF.comp hR)).aestronglyMeasurable C
    filter_upwards [] with z
    change ‖(1-a z : ℝ) • F (R z)‖ ≤ C
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hb z)]
    nlinarith [hbound (R z),norm_nonneg (F (R z)),hb z,hb1 z]
  have hrej : Integrable (fun z ↦ 1-a z) π := by
    apply Integrable.of_bound (measurable_const.sub ha).aestronglyMeasurable 1
    filter_upwards [] with z
    change ‖(1-a z : ℝ)‖ ≤ 1
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hb z)] using hb1 z
  have hidentity := correctedMeasure_test_identity π V R hV hR a ha ha0 ha1
    hstationary F hF C hbound
  have he : (∫ z, F (V z) ∂π)-(∫ z, F z ∂π) =
      ∫ z, (1-a z) • (F (V z)-F (R z)) ∂π := by
    rw [hidentity,← integral_add hA hB]
    have hs := integral_sub hFV (hA.add hB)
    simp only [Pi.add_apply] at hs
    rw [← hs]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  have hint : Integrable (fun z ↦ (1-a z) • (F (V z)-F (R z))) π := by
    convert hFV.sub (hA.add hB) using 1
    funext z
    simp only [Pi.sub_apply,Pi.add_apply,Complex.real_smul,Complex.ofReal_sub,Complex.ofReal_one]
    ring
  rw [he]
  calc
    _ ≤ ∫ z, ‖(1-a z) • (F (V z)-F (R z))‖ ∂π := norm_integral_le_integral_norm _
    _ ≤ ∫ z, (2*C)*(1-a z) ∂π := by
      apply integral_mono hint.norm (hrej.const_mul (2*C))
      intro z
      change ‖(1-a z : ℝ) • (F (V z)-F (R z))‖ ≤ (2*C)*(1-a z)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hb z)]
      have hs := (norm_sub_le (F (V z)) (F (R z))).trans
        (add_le_add (hbound (V z)) (hbound (R z)))
      nlinarith [mul_le_mul_of_nonneg_left hs (hb z)]
    _ = _ := integral_const_mul _ _

end KineticLangevin
