import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option linter.style.header false

/-! # Third-order remainder for the weak Langevin expansion

The compact smooth tests determining probability laws have bounded derivatives.
This file proves the pointwise Taylor estimate used when averaging Gaussian
Langevin increments. The derivative bound is derived for compact smooth tests;
it is not an extra assumption on the potential.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped ContDiff

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The quadratic Taylor polynomial at displacement `v`. -/
def secondOrderExpansion (φ : H → ℝ) (x v : H) : ℝ :=
  φ x + fderiv ℝ φ x v + (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 φ x (fun _ ↦ v)

/-- The exact cubic-order bound for the second-order Taylor remainder. -/
theorem secondOrderExpansion_remainder_le
    (φ : H → ℝ) (hφ : ContDiff ℝ 3 φ) (C : ℝ)
    (hC : ∀ x, ‖iteratedFDeriv ℝ 3 φ x‖ ≤ C) (x v : H) :
    |φ (x + v) - secondOrderExpansion φ x v| ≤ C / 6 * ‖v‖ ^ 3 := by
  let line : ℝ → H := fun t ↦ x + t • v
  let q : ℝ → ℝ := fun t ↦ φ (line t)
  have hline : ContDiff ℝ 3 line := by dsimp [line]; fun_prop
  have hq : ContDiff ℝ 3 q := hφ.comp hline
  have hlineD : deriv line = fun _ ↦ v := by
    funext t
    simpa [line] using (((hasDerivAt_id t).smul_const v).const_add x).deriv
  have hline2 : iteratedDeriv 2 line = fun _ ↦ 0 := by
    simp only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ', hlineD]
    funext t
    exact deriv_const t v
  have hline3 : iteratedDeriv 3 line = fun _ ↦ 0 := by
    rw [show 3 = 2 + 1 from rfl, iteratedDeriv_succ, hline2]
    funext t
    exact deriv_const t 0
  have hqD (t : ℝ) : HasDerivAt q (fderiv ℝ φ (line t) v) t := by
    have hl : HasDerivAt line v t := by
      simpa only [line, one_smul, id_eq] using (((hasDerivAt_id t).smul_const v).const_add x)
    exact (hφ.differentiable (by norm_num) (line t)).hasFDerivAt.comp_hasDerivAt t hl
  have hq2 (t : ℝ) : iteratedDeriv 2 q t =
      iteratedFDeriv ℝ 2 φ (line t) (fun _ ↦ v) := by
    simpa only [Function.comp_def, hlineD, hline2, map_zero, add_zero] using
      iteratedDeriv_vcomp_two (hφ.of_le (by norm_num)).contDiffAt
        (hline.of_le (by norm_num)).contDiffAt (x := t)
  have hq3 (t : ℝ) : iteratedDeriv 3 q t =
      iteratedFDeriv ℝ 3 φ (line t) (fun _ ↦ v) := by
    have hz0 : (iteratedFDeriv ℝ 2 φ (line t)) ![0, v] = 0 :=
      (iteratedFDeriv ℝ 2 φ (line t)).map_coord_zero (0 : Fin 2) (by rfl)
    have hz1 : (iteratedFDeriv ℝ 2 φ (line t)) ![v, 0] = 0 :=
      (iteratedFDeriv ℝ 2 φ (line t)).map_coord_zero (1 : Fin 2) (by rfl)
    simpa only [Function.comp_def, hlineD, hline2, hline3, map_zero, add_zero,
      hz0, hz1, smul_zero] using
      iteratedDeriv_vcomp_three hφ.contDiffAt hline.contDiffAt (x := t)
  have hu : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc (by norm_num)
  have hq1at : iteratedDerivWithin 1 q (uIcc 0 1) 0 = fderiv ℝ φ x v := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hq.of_le (by norm_num)).contDiffAt
      (by norm_num), iteratedDeriv_one, (hqD 0).deriv]
    simp [line]
  have hq2at : iteratedDerivWithin 2 q (uIcc 0 1) 0 =
      iteratedFDeriv ℝ 2 φ x (fun _ ↦ v) := by
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (hq.of_le (by norm_num)).contDiffAt
      (by norm_num), hq2]
    simp [line]
  have hpoly : taylorWithinEval q 2 (uIcc 0 1) 0 1 = secondOrderExpansion φ x v := by
    rw [taylorWithinEval_succ q 1 (uIcc 0 1) 0 1,
      taylorWithinEval_succ q 0 (uIcc 0 1) 0 1, taylor_within_zero_eval,
      hq1at, hq2at]
    norm_num [q, line, secondOrderExpansion, smul_eq_mul]
  obtain ⟨u, hu, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := q) (n := 2) (x₀ := 0) (x := 1) (by norm_num) hq.contDiffOn
  have hb : |iteratedDeriv 3 q u| ≤ C * ‖v‖ ^ 3 := by
    rw [hq3, ← Real.norm_eq_abs]
    calc
      _ ≤ ‖iteratedFDeriv ℝ 3 φ (line u)‖ * ∏ _ : Fin 3, ‖v‖ :=
        (iteratedFDeriv ℝ 3 φ (line u)).le_opNorm (fun _ ↦ v)
      _ = ‖iteratedFDeriv ℝ 3 φ (line u)‖ * ‖v‖ ^ 3 := by simp
      _ ≤ C * ‖v‖ ^ 3 := mul_le_mul_of_nonneg_right (hC _) (by positivity)
  have he' : φ (x + v) - secondOrderExpansion φ x v = iteratedDeriv 3 q u / 6 := by
    rw [hpoly] at he
    norm_num [q, line] at he
    exact he
  rw [he', abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  nlinarith

/-- Every smooth compact test has a uniform cubic Taylor-remainder bound,
derived from its compact support and smoothness. -/
theorem compactSmooth_secondOrderExpansion_remainder
    (φ : H → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x v,
      |φ (x + v) - secondOrderExpansion φ x v| ≤ C * ‖v‖ ^ 3 := by
  obtain ⟨C, hC, hb⟩ := hc.exists_bound_iteratedFDeriv hφ 3
  refine ⟨C / 6, by positivity, fun x v ↦ ?_⟩
  exact secondOrderExpansion_remainder_le φ (hφ.of_le (by simp)) C
    (fun z ↦ hb 3 le_rfl z) x v

end ULA
