import PBGSO.DoobStrongL2
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # An actual square-integrable radius from increasing finite maxima -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace PBGSO.MonotoneSquareRadius
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)

/-- A uniformly bounded sequence of actual increasing finite maximal
moments constructs a measurable L² radius; it is not supplied as data. -/
theorem exists_radius (u : ℕ → Ω → ℝ) (hu : ∀ n, Measurable (u n))
    (h2 : ∀ n, MemLp (u n) 2 Q) (h0 : ∀ n ω, 0 ≤ u n ω)
    (hmono : ∀ ω, Monotone (fun n => u n ω)) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n, (∫ ω, (u n ω) ^ 2 ∂Q) ≤ R) :
    ∃ C : Ω → ℝ, Measurable C ∧ (∀ ω, 0 ≤ C ω) ∧ MemLp C 2 Q ∧
      (∫ ω, C ω ^ 2 ∂Q) ≤ R ∧ ∀ᵐ ω ∂Q, ∀ n, u n ω ≤ C ω := by
  let S (ω : Ω) : ℝ≥0∞ := ⨆ n, ENNReal.ofReal ((u n ω) ^ 2)
  have hS : Measurable S := Measurable.iSup (fun n => (hu n).pow_const 2 |>.ennreal_ofReal)
  have hsq (n : ℕ) : Integrable (fun ω => (u n ω) ^ 2) Q := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm (h2 n).aestronglyMeasurable).mp (h2 n)
  have hsum : (∫⁻ ω, S ω ∂Q) ≤ ENNReal.ofReal R := by
    rw [lintegral_iSup (fun n => (hu n).pow_const 2 |>.ennreal_ofReal)]
    · apply iSup_le
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hsq n) (ae_of_all _ (fun _ => sq_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (hbound n)
    · intro i j hij ω
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (h0 i ω) (hmono ω hij) 2)
  have hf : (∫⁻ ω, S ω ∂Q) ≠ ∞ := (hsum.trans_lt ENNReal.ofReal_lt_top).ne
  have hfin : ∀ᵐ ω ∂Q, S ω < ∞ := ae_lt_top hS hf
  let C (ω : Ω) := Real.sqrt (S ω).toReal
  have hCm : Measurable C := Real.continuous_sqrt.measurable.comp hS.ennreal_toReal
  have hC0 (ω : Ω) : 0 ≤ C ω := Real.sqrt_nonneg _
  have hCsq (ω : Ω) : C ω ^ 2 = (S ω).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hCi : Integrable (fun ω => C ω ^ 2) Q :=
    (integrable_toReal_of_lintegral_ne_top hS.aemeasurable hf).congr (ae_of_all _ (fun ω => (hCsq ω).symm))
  have hC2 : MemLp C 2 Q := by
    apply (memLp_two_iff_integrable_sq_norm hCm.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using hCi
  have hCB : (∫ ω, C ω ^ 2 ∂Q) ≤ R := by
    apply ENNReal.ofReal_le_ofReal_iff hR |>.mp
    rw [ofReal_integral_eq_lintegral_ofReal hCi (ae_of_all _ (fun _ => sq_nonneg _))]
    apply le_trans _ hsum
    apply lintegral_mono_ae
    filter_upwards [hfin] with ω hω
    rw [hCsq, ENNReal.ofReal_toReal hω.ne]
  refine ⟨C, hCm, hC0, hC2, hCB, ?_⟩
  filter_upwards [hfin] with ω hω
  intro n
  have he : ENNReal.ofReal ((u n ω) ^ 2) ≤ S ω := le_iSup (fun n => ENNReal.ofReal ((u n ω) ^ 2)) n
  have hr := ENNReal.toReal_mono hω.ne he
  rw [ENNReal.toReal_ofReal (sq_nonneg _), ← hCsq] at hr
  exact (sq_le_sq₀ (h0 n ω) (hC0 ω)).mp hr

end PBGSO.MonotoneSquareRadius
