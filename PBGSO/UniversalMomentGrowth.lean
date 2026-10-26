import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! Universal integrability against finite-moment laws forces a genuine
pointwise growth bound. This separates a finite signed-work interpretation
of an assumption from a conditional Bochner-integral inequality. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace PBGSO.UniversalMomentGrowth
variable {E F : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
  [NormedAddCommGroup F]

theorem growth_of_finite_measure_integrability (w : E → ℝ) (hw : ∀ x, 1 ≤ w x)
    (f : E → F)
    (h : ∀ μ : Measure E, IsFiniteMeasure μ → Integrable w μ → Integrable f μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * w x := by
  by_contra hn
  push Not at hn
  have hx : ∀ n : ℕ, ∃ x : E, (2 : ℝ)^n * w x < ‖f x‖ := by
    intro n
    exact hn (2^n) (by positivity)
  choose x hx using hx
  let c : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ n / w (x n)
  have hwpos (n : ℕ) : 0 < w (x n) := lt_of_lt_of_le zero_lt_one (hw _)
  have hc (n : ℕ) : 0 ≤ c n := div_nonneg (by positivity) (hwpos n).le
  have hc_le (n : ℕ) : c n ≤ (2 : ℝ)⁻¹ ^ n := by
    exact div_le_self (by positivity) (hw _)
  have hcs : Summable c := Summable.of_nonneg_of_le hc hc_le
    (by simpa only [one_div] using summable_geometric_two)
  let μ : Measure E := Measure.sum (fun n => ENNReal.ofReal (c n) • Measure.dirac (x n))
  have hconst : Integrable (fun _ : E => (1 : ℝ)) μ := by
    apply integrable_sum_dirac (fun n => ENNReal.ofReal_ne_top)
    simpa only [ENNReal.toReal_ofReal (hc _), norm_one, mul_one] using hcs
  haveI : IsFiniteMeasure μ := (integrable_const_iff_isFiniteMeasure one_ne_zero).mp hconst
  have hwm : Integrable w μ := by
    apply integrable_sum_dirac (fun n => ENNReal.ofReal_ne_top)
    convert (show Summable (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) by
      simpa only [one_div] using summable_geometric_two) using 1
    ext n
    rw [ENNReal.toReal_ofReal (hc _), Real.norm_of_nonneg (hwpos n).le]
    exact div_mul_cancel₀ _ (hwpos n).ne'
  have hf := (h μ inferInstance hwm).summable_of_dirac
  have hlarge (n : ℕ) : 1 ≤ (ENNReal.ofReal (c n)).toReal * ‖f (x n)‖ := by
    rw [ENNReal.toReal_ofReal (hc _)]
    have hp : 0 < (2 : ℝ)^n := by positivity
    have he : c n * ((2 : ℝ)^n * w (x n)) = 1 := by
      dsimp [c]
      rw [inv_pow]
      field_simp [hp.ne', (hwpos n).ne']
    calc
      1 = c n * ((2 : ℝ)^n * w (x n)) := he.symm
      _ ≤ c n * ‖f (x n)‖ := mul_le_mul_of_nonneg_left (hx n).le (hc n)
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => zero_le_one) hlarge hf
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hs.tendsto_atTop_zero)

theorem growth_of_probability_integrability (w : E → ℝ) (hw : ∀ x, 1 ≤ w x)
    (f : E → F)
    (h : ∀ μ : Measure E, IsProbabilityMeasure μ → Integrable w μ → Integrable f μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * w x := by
  apply growth_of_finite_measure_integrability w hw f
  intro μ hμ hwm
  letI : IsFiniteMeasure μ := hμ
  by_cases hzero : μ = 0
  · simp [hzero]
  have hm0 : μ univ ≠ 0 := fun hz => hzero (Measure.measure_univ_eq_zero.mp hz)
  have hmfin : μ univ ≠ ∞ := measure_ne_top _ _
  let ν := (μ univ)⁻¹ • μ
  haveI : IsProbabilityMeasure ν := ⟨by
    dsimp [ν]
    exact ENNReal.inv_mul_cancel hm0 hmfin⟩
  have hwν : Integrable w ν := hwm.smul_measure (ENNReal.inv_ne_top.mpr hm0)
  have hfν := h ν inferInstance hwν
  exact (integrable_inv_smul_measure hm0 hmfin).mp hfν

end PBGSO.UniversalMomentGrowth
