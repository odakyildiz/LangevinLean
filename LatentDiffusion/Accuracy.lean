import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Explicit accuracy choices for the scalar budget in `MainResults`.
These are arithmetic corollaries; stochastic/reference hypotheses must still
be supplied to the actual particle theorem. Complexity interpretations require
that the displayed constants remain bounded independently of K and h. -/
noncomputable section
namespace LatentDiffusion
namespace Accuracy

theorem geometric_le_exp (m h : ℝ) (hq : 0 ≤ 1 - m * h / 2) (n : ℕ) :
    (1 - m * h / 2) ^ n ≤ Real.exp (-m * h * n / 2) := by
  have hb : 1 - m * h / 2 ≤ Real.exp (-m * h / 2) := by
    have := Real.add_one_le_exp (-m * h / 2)
    linarith
  have hp := pow_le_pow_left₀ hq hb n
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

/-- Logarithmic burn-in, valid also when R0=0 or the initial error is already
below the allocated tolerance. -/
theorem burnin (m h R0 epsilon : ℝ) (hR : 0 ≤ R0) (he : 0 < epsilon)
    (hq : 0 ≤ 1 - m * h / 2) (n : ℕ)
    (hn : Real.log (max 1 (5 * R0 / epsilon)) ≤ m * h * n / 2) :
    (1 - m * h / 2) ^ n * R0 ≤ epsilon / 5 := by
  have hx : 0 < max 1 (5 * R0 / epsilon) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb := Real.exp_le_exp.mpr hn
  rw [Real.exp_log hx] at hb
  have hc : 5 * R0 ≤ epsilon * Real.exp (m * h * n / 2) := by
    have hd := (le_max_right 1 (5 * R0 / epsilon)).trans hb
    exact (div_le_iff₀ he).mp hd |>.trans_eq (mul_comm _ _)
  have hp := mul_le_mul_of_nonneg_left hc (Real.exp_nonneg (-m * h * n / 2))
  have hexp : Real.exp (-m * h * n / 2) * Real.exp (m * h * n / 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    congr 1
    ring
  have hfinal : Real.exp (-m * h * n / 2) * R0 ≤ epsilon / 5 := by
    nlinarith [hexp]
  exact (mul_le_mul_of_nonneg_right (geometric_le_exp m h hq n) hR).trans hfinal

private theorem scaled_sqrt_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hs : a ^ 2 * c ≤ b ^ 2) : a * Real.sqrt c ≤ b := by
  have hr := Real.sq_sqrt hc
  have hp : 0 ≤ a * Real.sqrt c := by positivity
  nlinarith [sq_nonneg (a * Real.sqrt c - b)]

/-- Five equal allocations of epsilon. Criteria are division-free, allowing
zero drift, noise and variance constants without exceptional cases. -/
theorem budget_le_epsilon
    (m h R0 V L G W sigma epsilon K E : ℝ) (n : ℕ)
    (hm : 0 < m) (hh : 0 ≤ h) (hR : 0 ≤ R0) (hV : 0 ≤ V)
    (hL : 0 ≤ L) (_hG : 0 ≤ G) (hW : 0 ≤ W) (hK : 0 < K) (he : 0 < epsilon)
    (hq : 0 ≤ 1 - m * h / 2)
    (hn : Real.log (max 1 (5 * R0 / epsilon)) ≤ m * h * n / 2)
    (hparticles : 100 * V ≤ m ^ 2 * epsilon ^ 2 * K)
    (hdrift : 5 * L * h * G ≤ m * epsilon)
    (hnoise : 400 * L ^ 2 * W ^ 2 * h ≤ 9 * m ^ 2 * epsilon ^ 2)
    (horacle : 25 * h * sigma ^ 2 ≤ m * epsilon ^ 2)
    (hbudget : E ≤ (1 - m * h / 2) ^ n * R0 + (2 / m) * Real.sqrt (V / K) +
      L / m * (h * G + (4 / 3 : ℝ) * W * Real.sqrt h) +
      Real.sqrt (h * sigma ^ 2 / m)) : E ≤ epsilon := by
  have hb := burnin m h R0 epsilon hR he hq n hn
  have hp : (2 / m) * Real.sqrt (V / K) ≤ epsilon / 5 := by
    apply scaled_sqrt_le (by positivity) (by positivity) (by positivity)
    field_simp
    nlinarith
  have hd : L / m * (h * G) ≤ epsilon / 5 := by
    field_simp
    nlinarith
  have hw : (L / m * (4 / 3 : ℝ) * W) * Real.sqrt h ≤ epsilon / 5 := by
    apply scaled_sqrt_le (by positivity) (by positivity) hh
    field_simp
    nlinarith
  have ho : Real.sqrt (h * sigma ^ 2 / m) ≤ epsilon / 5 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    apply (div_le_iff₀ hm).mpr
    nlinarith
  nlinarith

end Accuracy
end LatentDiffusion
