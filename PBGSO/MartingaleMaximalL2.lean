import PBGSO.MartingaleL2Limit
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-! # Maximal control from actual square-integrable martingales
Conditional Jensen produces the squared-norm submartingale. Doob's maximal
inequality then bounds any finite observation grid by its terminal L² energy.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace PBGSO.MartingaleMaximalL2
variable {Ω H ι : Type*} [mΩ : MeasurableSpace Ω] [Preorder ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ι mΩ)
  (X : ι → Ω → H) (hX : Martingale X F Q)
  (h2 : ∀ t, MemLp (X t) 2 Q)

include hX h2 in
/-- Squared norms of actual square-integrable martingales are submartingales. -/
theorem norm_sq_submartingale : Submartingale (fun t ω => ‖X t ω‖ ^ 2) F Q := by
  have hi (t : ι) : Integrable (fun ω => ‖X t ω‖ ^ 2) Q :=
    (memLp_two_iff_integrable_sq_norm (h2 t).aestronglyMeasurable).mp (h2 t)
  refine ⟨fun t => (hX.stronglyAdapted t).norm.pow 2, ?_, hi⟩
  intro s t hst
  have hj := _root_.Integrable.norm_condExp_rpow_le (μ := Q) (m := F s) (f := X t)
    (by norm_num : (1 : ℝ) ≤ 2) (by simpa only [Real.rpow_two] using hi t)
  simp only [Real.rpow_two] at hj
  filter_upwards [hj, hX.condExp_ae_eq hst] with ω hω he
  rw [he] at hω
  exact hω

variable {F X}

/-- A monotone observation grid carries the actual sampled filtration. -/
def sampledFiltration (τ : ℕ → ι) (hτ : Monotone τ) : Filtration ℕ mΩ where
  seq n := F (τ n)
  mono' _ _ h := F.mono (hτ h)
  le' n := F.le (τ n)

include hX in
theorem sampled_martingale (τ : ℕ → ι) (hτ : Monotone τ) :
    Martingale (fun n => X (τ n)) (sampledFiltration (F := F) τ hτ) Q :=
  ⟨fun n => hX.stronglyAdapted (τ n), fun i j h => hX.condExp_ae_eq (hτ h)⟩

include hX h2 in
/-- Weak L² maximal inequality on every finite monotone observation grid.
This applies to actual computed Itô martingales without a maximal-bound premise. -/
theorem maximal_grid (τ : ℕ → ι) (hτ : Monotone τ) (a : ℝ≥0) (n : ℕ) :
    (a : ℝ≥0∞) * Q {ω | (a : ℝ) ≤
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => ‖X (τ k) ω‖ ^ 2)} ≤
      ENNReal.ofReal (∫ ω, ‖X (τ n) ω‖ ^ 2 ∂Q) := by
  have hm := norm_sq_submartingale Q (sampledFiltration (F := F) τ hτ)
    (fun n => X (τ n)) (sampled_martingale Q hX τ hτ) (fun n => h2 (τ n))
  have hd := maximal_ineq hm (fun _ _ => sq_nonneg _) (ε := a) n
  exact hd.trans (ENNReal.ofReal_le_ofReal (setIntegral_le_integral (hm.integrable n)
    (Eventually.of_forall fun _ => sq_nonneg _)))

end PBGSO.MartingaleMaximalL2
