import KineticLangevin.OBABOLaw
import KineticLangevin.OBABOLocalCost

/-! # The explicit first-order OBABO bias coefficient -/

noncomputable section
set_option linter.style.header false
open MeasureTheory
open scoped ENNReal NNReal
namespace KineticLangevin

theorem obaboContractionRate_lt_one (m γ h : ℝ) (hm : 0 < m) (hγ : 0 < γ) (hh : 0 < h) :
    (obaboContractionRate m γ h : ℝ) < 1 := by
  change Real.sqrt (1 - m * h / (3 * γ)) < 1
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
  have hp : 0 < m * h / (3 * γ) := by positivity
  nlinarith only [hp]

theorem obabo_rate_gap_bound (m γ h : ℝ) (hm : 0 < m) (hγ : 0 < γ) (hh : 0 < h)
    (hq : 0 ≤ 1 - m * h / (3 * γ)) :
    m * h / (6 * γ) ≤ 1 - (obaboContractionRate m γ h : ℝ) := by
  have hr := obaboContractionRate_lt_one m γ h hm hγ hh
  have hs : (obaboContractionRate m γ h : ℝ) ^ 2 = 1 - m * h / (3 * γ) := Real.sq_sqrt hq
  have hprod : (1 - (obaboContractionRate m γ h : ℝ)) *
      (1 + (obaboContractionRate m γ h : ℝ)) = m * h / (3 * γ) := by nlinarith only [hs]
  have hle : 0 ≤ (1 - (obaboContractionRate m γ h : ℝ)) ^ 2 := sq_nonneg _
  simp only [div_eq_mul_inv,mul_inv_rev] at hs hprod ⊢
  norm_num at hs hprod ⊢
  nlinarith only [hprod,hle]

theorem obaboLocalBudget_simplify (M h d : ℝ) (hM : 0 ≤ M) :
    obaboLocalBudget M h d = h ^ 2 * Real.sqrt d * (4 * Real.sqrt M + M * h / 2) := by
  unfold obaboLocalBudget
  rw [Real.sqrt_mul hM]
  have hs := Real.sq_sqrt hM
  have hmul : Real.sqrt M * Real.sqrt M = M := by nlinarith only [hs]
  calc
    _ = h ^ 2 * Real.sqrt d * (4 * Real.sqrt M + (Real.sqrt M * Real.sqrt M) * h / 2) := by ring
    _ = _ := by rw [hmul]

theorem obaboLocalBudget_div_gap (m M γ h : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hγ : 0 < γ) (hh : 0 < h) (hq : 0 ≤ 1 - m * h / (3 * γ)) (d : ℝ) :
    obaboLocalBudget M h d / (1 - (obaboContractionRate m γ h : ℝ)) ≤
      (6 * γ / m) * h * Real.sqrt d * (4 * Real.sqrt M + M * h / 2) := by
  have hgap := obabo_rate_gap_bound m γ h hm hγ hh hq
  have hgapPos : 0 < m * h / (6 * γ) := by positivity
  have hb := obaboLocalBudget_nonneg M h d hh.le
  have hdiv := div_le_div_of_nonneg_left hb hgapPos hgap
  rw [obaboLocalBudget_simplify M h d hM] at hdiv
  rw [obaboLocalBudget_simplify M h d hM]
  convert hdiv using 1 <;> field_simp <;> ring

end KineticLangevin
