import UnadjustedLangevin.Recurrence
import Mathlib.Tactic

set_option linter.style.header false

/-! # Corrected scalar recurrence for the proximal splitting analysis

The one-step inequality for an actual PIPGLA law remains a separate analytic
obligation. These are scalar consequences, not that stochastic theorem.
The squared-gradient remainder is not divided by the particle count. This
matches the corrected scaling in v3 Corollary A.12; the strict denominator
condition below additionally repairs the endpoint included in v3.
-/


noncomputable section

namespace ProximalLangevin

/-- The contraction coefficient used in the paper's splitting argument. -/
def splittingRatio (μ γ lam : ℝ) : ℝ := lam * (1 - μ * γ) / γ

/-- Correct scaling for noise variance `2γ/N` and the unscaled squared-norm
bound `C` on the convex potential's selected subgradient in v3. -/
def splittingForcing (N D γ lam L C : ℝ) : ℝ :=
  lam * (2 * γ * L * D / N + lam * C)

theorem splittingRatio_nonneg (μ γ lam : ℝ) (hγ : 0 < γ)
    (hlam : 0 ≤ lam) (hμγ : μ * γ ≤ 1) :
    0 ≤ splittingRatio μ γ lam := by
  unfold splittingRatio
  positivity

/-- The upper endpoint has to be strict for a geometric error floor. -/
theorem splittingRatio_lt_one_iff (μ γ lam : ℝ)
    (hγ : 0 < γ) (hμγ : μ * γ < 1) :
    splittingRatio μ γ lam < 1 ↔ lam < γ / (1 - μ * γ) := by
  unfold splittingRatio
  rw [div_lt_iff₀ hγ, lt_div_iff₀ (sub_pos.mpr hμγ)]
  simp

theorem splittingForcing_nonneg (N D γ lam L C : ℝ)
    (hN : 0 ≤ N) (hD : 0 ≤ D) (hγ : 0 ≤ γ) (hlam : 0 ≤ lam)
    (hL : 0 ≤ L) (hC : 0 ≤ C) :
    0 ≤ splittingForcing N D γ lam L C := by
  unfold splittingForcing
  positivity

/-- The finite sum is meaningful at the endpoint `q=1`, too. -/
theorem splitting_recurrence_sum (e : ℕ → ℝ) (N D μ γ lam L C : ℝ)
    (hq : 0 ≤ splittingRatio μ γ lam)
    (hstep : ∀ n, e (n + 1) ≤ splittingRatio μ γ lam * e n +
      splittingForcing N D γ lam L C) (n : ℕ) :
    e n ≤ splittingRatio μ γ lam ^ n * e 0 +
      splittingForcing N D γ lam L C *
        ∑ j ∈ Finset.range n, splittingRatio μ γ lam ^ j :=
  ULA.affine_recurrence_sum e _ _ hq hstep n

/-- Exact finite-horizon bound in the strict contraction regime. -/
theorem splitting_recurrence_exact (e : ℕ → ℝ) (N D μ γ lam L C : ℝ)
    (hq : 0 ≤ splittingRatio μ γ lam) (hq1 : splittingRatio μ γ lam < 1)
    (hstep : ∀ n, e (n + 1) ≤ splittingRatio μ γ lam * e n +
      splittingForcing N D γ lam L C) (n : ℕ) :
    e n ≤ splittingRatio μ γ lam ^ n * e 0 +
      splittingForcing N D γ lam L C * (1 - splittingRatio μ γ lam ^ n) /
        (1 - splittingRatio μ γ lam) :=
  ULA.affine_recurrence_exact e _ _ hq hq1 hstep n

/-- Corrected error floor. The forcing's gradient contribution is `lam² C`,
whereas its Gaussian contribution is `2lamγLD/N`. -/
theorem splitting_recurrence_bound (e : ℕ → ℝ) (N D μ γ lam L C : ℝ)
    (hq : 0 ≤ splittingRatio μ γ lam) (hq1 : splittingRatio μ γ lam < 1)
    (hc : 0 ≤ splittingForcing N D γ lam L C)
    (hstep : ∀ n, e (n + 1) ≤ splittingRatio μ γ lam * e n +
      splittingForcing N D γ lam L C) (n : ℕ) :
    e n ≤ splittingRatio μ γ lam ^ n * e 0 +
      splittingForcing N D γ lam L C / (1 - splittingRatio μ γ lam) :=
  ULA.affine_recurrence_bound e _ _ hq hq1 hc hstep n

/-- At the noncontracting endpoint, retain the linear finite-horizon bound. -/
theorem splitting_recurrence_endpoint (e : ℕ → ℝ) (c : ℝ)
    (hstep : ∀ n, e (n + 1) ≤ e n + c) (n : ℕ) :
    e n ≤ e 0 + (n : ℝ) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
      push_cast
      nlinarith [hstep n]

/-- When `lam=γ`, the corrected error floor takes this particularly simple
form, with no `1/N` multiplying `C`. -/
theorem splitting_bias_equal_steps (N D μ γ L C : ℝ)
    (hN : N ≠ 0) (hμ : μ ≠ 0) (hγ : γ ≠ 0) :
    splittingForcing N D γ γ L C / (1 - splittingRatio μ γ γ) =
      γ / μ * (2 * L * D / N + C) := by
  unfold splittingForcing splittingRatio
  field_simp
  ring

end ProximalLangevin
