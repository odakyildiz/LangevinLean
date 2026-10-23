import UnadjustedLangevin.LpDrift
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false

/-!
# Bounded observations on the actual `L²` process

Uniformly continuous bounded scalar tests induce uniformly continuous
weighted expectations on `L²`, including arbitrary bounded measurable
functions of the initialization. The estimate uses only the actual second
moment of the difference of the two random variables.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory
open scoped NNReal ENNReal

namespace AverageLMC

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- A bounded weighted test evaluated at an actual `L²` random variable. -/
def lpWeightedTest (w : Ω → ℝ) (F : H → ℝ) (X : Lp H 2 P) : ℝ :=
  ∫ a, w a * F (X a) ∂P

theorem lpWeightedTest_integrable
    (w : Ω → ℝ) (hw : Measurable w) (A : ℝ) (hA : 0 ≤ A)
    (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (F : H → ℝ) (hF : Continuous F) (C : ℝ) (hC : 0 ≤ C)
    (hFC : ∀ x, |F x| ≤ C) (X : Lp H 2 P) :
    Integrable (fun a ↦ w a * F (X a)) P := by
  apply (MemLp.of_bound
    (hw.aestronglyMeasurable.mul (hF.comp_aestronglyMeasurable (Lp.aestronglyMeasurable X)))
    (A * C) ?_ : MemLp _ 1 P).integrable le_rfl
  filter_upwards [hwA] with a ha
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
  exact mul_le_mul ha (hFC _) (abs_nonneg _) hA

/-- Uniform continuity can be integrated against a bounded weight using an
explicit quadratic tail bound. -/
theorem lpWeightedTest_difference_le
    (w : Ω → ℝ) (hw : Measurable w) (A : ℝ) (hA : 0 ≤ A)
    (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (F : H → ℝ) (hF : Continuous F) (C ε δ : ℝ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hδ : 0 < δ)
    (hFC : ∀ x, |F x| ≤ C)
    (hmod : ∀ x y, ‖x - y‖ ≤ δ → |F x - F y| ≤ ε)
    (X Y : Lp H 2 P) :
    |lpWeightedTest P w F X - lpWeightedTest P w F Y| ≤
      A * (ε + (2 * C / δ ^ 2) * ‖X - Y‖ ^ 2) := by
  let β := 2 * C / δ ^ 2
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hp (x y : H) : |F x - F y| ≤ ε + β * ‖x - y‖ ^ 2 := by
    by_cases hxy : ‖x - y‖ ≤ δ
    · exact (hmod x y hxy).trans (by nlinarith [mul_nonneg hβ (sq_nonneg ‖x - y‖)])
    · have hdist : δ ^ 2 ≤ ‖x - y‖ ^ 2 :=
        (sq_le_sq₀ hδ.le (norm_nonneg _)).mpr (le_of_lt (lt_of_not_ge hxy))
      have ht : 2 * C ≤ β * ‖x - y‖ ^ 2 := by
        dsimp [β]
        have hmul := mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 2 * C / δ ^ 2)
        have he : 2 * C / δ ^ 2 * δ ^ 2 = 2 * C := div_mul_cancel₀ _ (by positivity)
        rwa [he] at hmul
      exact ((abs_sub _ _).trans (add_le_add (hFC x) (hFC y))).trans (by linarith)
  have hwiX := lpWeightedTest_integrable P w hw A hA hwA F hF C hC hFC X
  have hwiY := lpWeightedTest_integrable P w hw A hA hwA F hF C hC hFC Y
  have hdiff : Integrable (fun a ↦ w a * (F (X a) - F (Y a))) P := by
    exact (hwiX.sub hwiY).congr (ae_of_all _ (fun a ↦ by
      change w a * F (X a) - w a * F (Y a) = w a * (F (X a) - F (Y a))
      ring))
  have hsq : Integrable (fun a ↦ ‖X a - Y a‖ ^ 2) P :=
    ((Lp.memLp X).sub (Lp.memLp Y)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hnorm : ‖X - Y‖ ^ 2 = ∫ a, ‖X a - Y a‖ ^ 2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub X Y] with a ha
    rw [ha, Pi.sub_apply, real_inner_self_eq_norm_sq]
  have hpoint : ∀ᵐ a ∂P, |w a * (F (X a) - F (Y a))| ≤
      A * (ε + β * ‖X a - Y a‖ ^ 2) := by
    filter_upwards [hwA] with a ha
    rw [abs_mul]
    exact mul_le_mul ha (hp _ _) (abs_nonneg _) hA
  have he : lpWeightedTest P w F X - lpWeightedTest P w F Y =
      ∫ a, w a * (F (X a) - F (Y a)) ∂P := by
    rw [lpWeightedTest, lpWeightedTest, ← integral_sub hwiX hwiY]
    apply integral_congr_ae
    exact ae_of_all _ fun a ↦ by ring
  rw [he]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ a, A * (ε + β * ‖X a - Y a‖ ^ 2) ∂P :=
      integral_mono_ae hdiff.abs (((integrable_const ε).add (hsq.const_mul β)).const_mul A) hpoint
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_const ε) (hsq.const_mul β),
        integral_const_mul, integral_const]
      simp only [probReal_univ, one_smul, ← hnorm, β]

/-- Every bounded uniformly continuous test induces a uniformly continuous
weighted expectation on the actual `L²` space. -/
theorem lpWeightedTest_uniformContinuous
    (w : Ω → ℝ) (hw : Measurable w) (A : ℝ) (hA : 0 ≤ A)
    (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (F : H → ℝ) (hF : UniformContinuous F) (C : ℝ) (hC : 0 ≤ C)
    (hFC : ∀ x, |F x| ≤ C) : UniformContinuous (lpWeightedTest P w F) := by
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  let η := ε / (2 * (A + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηscale : η * (2 * (A + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp hF η hη
  let β := 2 * C / (δ / 2) ^ 2
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  let r := Real.sqrt (ε / (2 * (A * β + 1)))
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hε (by positivity))
  refine ⟨r, hr, fun X Y hXY ↦ ?_⟩
  have hb := lpWeightedTest_difference_le P w hw A hA hwA F hF.continuous
    C η (δ / 2) hC hη.le (by positivity) hFC (fun x y hxy ↦ by
      have hd : dist x y < δ := by rw [dist_eq_norm]; linarith
      simpa only [Real.dist_eq] using (hmod hd).le) X Y
  have hsq : ‖X - Y‖ ^ 2 < ε / (2 * (A * β + 1)) := by
    have hx : ‖X - Y‖ < r := by simpa only [dist_eq_norm] using hXY
    have hs := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hx
    rwa [Real.sq_sqrt (by positivity)] at hs
  have hmul := mul_lt_mul_of_pos_left hsq (by positivity : 0 < 2 * (A * β + 1))
  have hcancel : 2 * (A * β + 1) * (ε / (2 * (A * β + 1))) = ε :=
    mul_div_cancel₀ ε (by positivity)
  rw [hcancel] at hmul
  rw [Real.dist_eq]
  change |lpWeightedTest P w F X - lpWeightedTest P w F Y| < ε
  dsimp only [β] at hmul
  nlinarith [sq_nonneg ‖X - Y‖]

end AverageLMC
