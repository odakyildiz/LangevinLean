import AverageLMC.GLMCounterexample
import AverageLMC.Assumptions
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

set_option linter.style.header false

/-! # Counterexamples to two intermediate claims of the manuscript

The first concerns the uniform empirical fourth-moment event in the GLM proof.
The second concerns an SGLD transient comparison under only `mh ≤ 1/3`.
Neither refutes a separate main sampling theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace AverageLMC

/-- The empirical fourth moment in the direction of one design row retains
that row's fourth power, regardless of all other rows. -/
theorem norm_fourth_le_empirical_direction {p n : ℕ} (X : Fin n → State p)
    (i : Fin n) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ u : State p, ‖u‖ = 1 → ∑ j, (inner ℝ (X j) u) ^ 4 ≤ C) :
    ‖X i‖ ^ 4 ≤ C := by
  by_cases hz : X i = 0
  · simpa [hz] using hC
  have hp : 0 < ‖X i‖ := norm_pos_iff.mpr hz
  let u : State p := ‖X i‖⁻¹ • X i
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, hp.ne']
  have hin : inner ℝ (X i) u = ‖X i‖ := by
    simp only [u, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hs : (inner ℝ (X i) u) ^ 4 ≤ ∑ j, (inner ℝ (X j) u) ^ 4 :=
    Finset.single_le_sum (f := fun j ↦ (inner ℝ (X j) u) ^ 4)
      (fun j _ ↦ by positivity) (Finset.mem_univ i)
  rw [hin] at hs
  exact hs.trans (hb u hu)

/-- A fourth-power bound of order p implies a cubic one with a fixed,
dimension independent constant. -/
theorem cube_le_of_fourth_le {r C q : ℝ} (hr : 0 ≤ r) (_hC : 0 ≤ C)
    (hq : 1 ≤ q) (hb : r ^ 4 ≤ C * q) : r ^ 3 ≤ (C + 1) * q := by
  have hbase : r ^ 3 ≤ 1 + r ^ 4 := by
    by_cases h : r ≤ 1
    · have hp := pow_le_pow_left₀ hr h 3
      norm_num at hp
      linarith [pow_nonneg hr 4]
    · have h := le_of_not_ge h
      have hm := mul_nonneg (pow_nonneg hr 3) (sub_nonneg.mpr h)
      nlinarith
  nlinarith

/-- The source's proposed simultaneous empirical fourth-moment event has
probability below one half for sufficiently large square Gaussian designs. -/
theorem gaussian_empirical_fourth_event_fails (p : ℕ) (i : Fin p) (C : ℝ)
    (hC : 0 ≤ C) (hp : 16 < p) (hlarge : 8 * (C + 1) ^ 2 < (p : ℝ)) :
    gaussianDesignLaw p {X | ∀ u : State p, ‖u‖ = 1 →
      ∑ j, (inner ℝ (X j) u) ^ 4 ≤ C * (p : ℝ)} < (1 / 2 : ℝ≥0∞) := by
  have hsub : {X : GaussianDesign p | ∀ u : State p, ‖u‖ = 1 →
      ∑ j, (inner ℝ (X j) u) ^ 4 ≤ C * (p : ℝ)} ⊆
      {X | ‖X i‖ ^ 3 ≤ (C + 1) * (p : ℝ)} := by
    intro X hX
    apply cube_le_of_fourth_le (norm_nonneg _) hC (by exact_mod_cast (by omega : 1 ≤ p))
    exact norm_fourth_le_empirical_direction X i (C * (p : ℝ)) (by positivity) hX
  have hrow := (gaussianDesign_row_law p i).measure_eq
    (p := fun z : State p ↦ ‖z‖ ^ 3 ≤ (C + 1) * (p : ℝ)) (by measurability)
  exact ((measure_mono hsub).trans_eq hrow).trans_lt
    (stdGaussian_cube_bound_fails p (C + 1) (by linarith) hp hlarge)

/-- The exponential series certifies the concrete logarithmic iteration
threshold in the transient counterexample. -/
theorem log_two_hundred_le : Real.log 200 ≤ (16 : ℝ) / 3 := by
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 16 / 3) 16
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 200)).mpr
  linarith

/-- Under the immediately stated restriction `a ≤ 1/3`, the displayed
iteration threshold does not ensure the claimed `0.6 ε²` transient.
The later, stricter precision-dependent step choice is a different claim. -/
theorem sgld_transient_comparison_counterexample :
    (0 : ℝ) < 1 / 3 ∧ (1 : ℝ) / 3 ≤ 1 / 3 ∧
    (0 : ℝ) < 1 / 10 ∧ (1 : ℝ) / 10 ≤ 1 ∧
    16 ≥ (1 / ((1 : ℝ) / 3)) * Real.log (2 * (1 / ((1 : ℝ) / 10) ^ 2)) ∧
    ((1 + (1 : ℝ) / 3)⁻¹) ^ 16 > (3 / 5 : ℝ) * ((1 : ℝ) / 10) ^ 2 := by
  have hlog := log_two_hundred_le
  norm_num at hlog ⊢
  linarith

end AverageLMC
