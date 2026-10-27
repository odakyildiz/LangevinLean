import LatentDiffusion.Cloud
import LatentDiffusion.Lift

/-! # Uniform numerical error with a stationary reference and a noisy oracle

The exact reference may have a different force: for a frozen posterior cloud,
its parameter force is zero, whereas the interacting force uses an empirical
parameter gradient. The difference is a sampling residual. This module derives
the full numerical error from actual integral equations, primitive moment bounds,
and this residual; neither a numerical error nor its recurrence is a premise.

All statements are valid in a real Hilbert space, in particular genuine L².
Construction of a stationary frozen posterior process and its moment estimates
is an explicit application obligation, not inferred from the word stationary.
-/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace LatentDiffusion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A Lipschitz reference force suffices for the local integral remainder; it
need not contract in coordinates that stay fixed, such as the parameters. -/
theorem reference_local_defect (R : H → H) (h G Wbound : ℝ) (L : ℝ≥0)
    (hR : LipschitzWith L R) (hh : 0 ≤ h)
    (y : ℕ → H) (ξ : ℕ → H) (Y W : ℕ → ℝ → H)
    (hr : IntegralReference R h G Wbound y ξ Y W) (n : ℕ) :
    ‖y (n + 1) - eulerStep R h (y n) (ξ n)‖ ≤
      (L : ℝ) * (h ^ 2 * G / 2 + (2 / 3 : ℝ) * h * Real.sqrt h * Wbound) := by
  have hid := ULA.localDefect_euler_identity R (Y n) (W n) h
    (hr.integrable n) (hr.equation n h ⟨hh, le_rfl⟩)
  rw [hr.starts n, hr.ends n, hr.noise_end n] at hid
  have he : y (n + 1) - eulerStep R h (y n) (ξ n) = -ULA.localDefect R (Y n) h := by
    rw [hid]
    unfold eulerStep
    module
  rw [he, norm_neg]
  exact ULA.localDefect_bound R (Y n) (W n) L h G Wbound hh hR
    (hr.drift_radius n) (hr.noise_growth n) (hr.equation n)

/-- Explicit all-iteration error. `B` is the empirical-force residual, `G` the
reference drift RMS radius, and `Wbound sqrt(t)` its noise increment radius.
The reference's strong contraction is not assumed. -/
theorem equilibrium_reference_error (F R : H → H) (m h B G Wbound : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hR : LipschitzWith L R)
    (hs : StableStep m L h) (hB : 0 ≤ B) (hG : 0 ≤ G) (hW : 0 ≤ Wbound)
    (y : ℕ → H) (ξ : ℕ → H) (Y W : ℕ → ℝ → H) (x₀ : H)
    (hr : IntegralReference R h G Wbound y ξ Y W)
    (hres : ∀ n, ‖F (y n) - R (y n)‖ ≤ B) (n : ℕ) :
    ‖eulerTrajectory F h ξ x₀ n - y n‖ ≤
      (1 - m * h / 2) ^ n * ‖x₀ - y 0‖ +
        2 * B / m + (L : ℝ) / m * (h * G + (4 / 3 : ℝ) * Wbound * Real.sqrt h) := by
  let D := (L : ℝ) * (h ^ 2 * G / 2 + (2 / 3 : ℝ) * h * Real.sqrt h * Wbound)
  have hlocal (k : ℕ) : ‖y (k+1) - eulerStep F h (y k) (ξ k)‖ ≤ h * B + D := by
    have he : eulerStep R h (y k) (ξ k) - eulerStep F h (y k) (ξ k) =
        h • (F (y k) - R (y k)) := by unfold eulerStep; module
    calc
      _ ≤ ‖y (k+1) - eulerStep R h (y k) (ξ k)‖ +
          ‖eulerStep R h (y k) (ξ k) - eulerStep F h (y k) (ξ k)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ D + h * B := by
        apply add_le_add (reference_local_defect R h G Wbound L hR hs.positive.le
          y ξ Y W hr k)
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hs.positive]
        exact mul_le_mul_of_nonneg_left (hres k) hs.positive.le
      _ = _ := by ring
  have hstep (k : ℕ) : ‖eulerTrajectory F h ξ x₀ (k+1) - y (k+1)‖ ≤
      (1 - m*h/2) * ‖eulerTrajectory F h ξ x₀ k - y k‖ + (h*B+D) := by
    simpa only [eulerTrajectory, mul_zero, add_zero] using
      euler_local_comparison F F m h 0 (h*B+D) L hF hs
        (eulerTrajectory F h ξ x₀ k) (y k) (y (k+1)) (ξ k) (by simp) (hlocal k)
  have hq : 0 ≤ 1-m*h/2 := by linarith [hs.scaled_monotonicity]
  have hq1 : 1-m*h/2 < 1 := by nlinarith [hs.monotonicity_positive, hs.positive]
  have hb : 0 ≤ h*B+D := by dsimp [D]; have hh := hs.positive.le; positivity
  have hbnd := ULA.affine_recurrence_bound (fun k => ‖eulerTrajectory F h ξ x₀ k-y k‖)
    (1-m*h/2) (h*B+D) hq hq1 hb hstep n
  have heq : (h*B+D)/(1-(1-m*h/2)) =
      2*B/m+(L:ℝ)/m*(h*G+(4/3:ℝ)*Wbound*Real.sqrt h) := by
    dsimp [D]
    field_simp [ne_of_gt hs.positive, ne_of_gt hs.monotonicity_positive]
    ring
  simpa only [eulerTrajectory, heq, add_assoc] using hbnd

/-- Numerical, finite-cloud, and stochastic-gradient errors separated in one
uniform estimate. Conditional centering is used only for the stochastic term,
which is of order sqrt(h), rather than an order-one worst-case force bias. -/
theorem stochastic_equilibrium_error (F R : H → H) (m h B G Wbound σ : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hR : LipschitzWith L R)
    (hs : StableStep m L h) (hB : 0 ≤ B) (hG : 0 ≤ G) (hW : 0 ≤ Wbound)
    (y : ℕ → H) (ξ ζ : ℕ → H) (Y W : ℕ → ℝ → H) (x₀ : H)
    (hr : IntegralReference R h G Wbound y ξ Y W)
    (hres : ∀ n, ‖F (y n) - R (y n)‖ ≤ B)
    (hc : HilbertInnovationControl F h σ ξ ζ x₀ x₀) (n : ℕ) :
    ‖eulerTrajectory F h (fun k => ξ k + h • ζ k) x₀ n - y n‖ ≤
      (1 - m * h / 2) ^ n * ‖x₀ - y 0‖ +
        2 * B / m + (L : ℝ) / m * (h * G + (4 / 3 : ℝ) * Wbound * Real.sqrt h) +
        Real.sqrt (h * σ ^ 2 / m) := by
  have hn := hilbert_innovation_sq_bound F m h σ L hF hs ξ ζ x₀ x₀ hc n
  simp only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add] at hn
  have hroot : ‖eulerTrajectory F h (fun k => ξ k + h • ζ k) x₀ n -
      eulerTrajectory F h ξ x₀ n‖ ≤ Real.sqrt (h * σ ^ 2 / m) := by
    simpa only [Real.sqrt_sq (norm_nonneg
      (eulerTrajectory F h (fun k => ξ k + h • ζ k) x₀ n -
        eulerTrajectory F h ξ x₀ n))] using Real.sqrt_le_sqrt hn
  have he := equilibrium_reference_error F R m h B G Wbound L hF hR hs hB hG hW
    y ξ Y W x₀ hr hres n
  exact (norm_sub_le_norm_sub_add_norm_sub _ (eulerTrajectory F h ξ x₀ n) _).trans (by linarith)

/-- Any norm-one output projection, including the parameter block, inherits
the same bound whenever the reference output is the specified target. -/
theorem stochastic_equilibrium_output
    {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (C : H →L[ℝ] A) (hC : ‖C‖ ≤ 1) (target : A)
    (F R : H → H) (m h B G Wbound σ : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hR : LipschitzWith L R)
    (hs : StableStep m L h) (hB : 0 ≤ B) (hG : 0 ≤ G) (hW : 0 ≤ Wbound)
    (y : ℕ → H) (ξ ζ : ℕ → H) (Y W : ℕ → ℝ → H) (x₀ : H)
    (hr : IntegralReference R h G Wbound y ξ Y W)
    (hres : ∀ n, ‖F (y n) - R (y n)‖ ≤ B)
    (hc : HilbertInnovationControl F h σ ξ ζ x₀ x₀)
    (htarget : ∀ n, C (y n) = target) (n : ℕ) :
    ‖C (eulerTrajectory F h (fun k => ξ k + h • ζ k) x₀ n) - target‖ ≤
      (1 - m * h / 2) ^ n * ‖x₀ - y 0‖ +
        2 * B / m + (L : ℝ) / m * (h * G + (4 / 3 : ℝ) * Wbound * Real.sqrt h) +
        Real.sqrt (h * σ ^ 2 / m) := by
  rw [← htarget n, ← map_sub]
  apply le_trans (le_trans (C.le_opNorm _) (mul_le_of_le_one_left (norm_nonneg _) hC))
  exact stochastic_equilibrium_error F R m h B G Wbound σ L hF hR hs hB hG hW
    y ξ ζ Y W x₀ hr hres hc n

end LatentDiffusion
