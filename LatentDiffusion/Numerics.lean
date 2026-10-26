import UnadjustedLangevin.GradientStep
import UnadjustedLangevin.Recurrence
import UnadjustedLangevin.LocalError
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Quantitative stability and discretization error for latent Euler algorithms

These results concern actual Euler updates on a real inner product space.  In the
paper's interacting algorithm that space can be the latent parameter / particle
cloud with its particle-normalized inner product.  Neither contraction nor an
error recurrence is included among the hypotheses.

The reference-path consistency hypothesis below is a *local defect bound*.  An
SDE application must establish it from the drift and Brownian regularity; this
file does not claim that such a bound follows from monotonicity alone.
-/

open scoped NNReal

namespace LatentDiffusion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Added regularity assumption on the positive force, i.e. minus the SDE drift.
The constant `L` is nonnegative by its type. -/
structure ForceRegularity (F : H → H) (m : ℝ) (L : ℝ≥0) : Prop where
  monotone : ∀ x y, m * ‖x - y‖ ^ 2 ≤ inner ℝ (F x - F y) (x - y)
  lipschitz : ∀ x y, ‖F x - F y‖ ≤ (L : ℝ) * ‖x - y‖

/-- A step restriction stated without division, including degenerate spaces. -/
structure StableStep (m : ℝ) (L : ℝ≥0) (h : ℝ) : Prop where
  positive : 0 < h
  monotonicity_positive : 0 < m
  scaled_monotonicity : m * h ≤ 1
  scaled_lipschitz : h * (L : ℝ) ^ 2 ≤ m

/-- The Euler update, with the entire additive noise increment supplied as `ξ`.
For IPLD it is `sqrt (2h)` times the appropriately scaled Gaussian cloud. -/
def eulerStep (F : H → H) (h : ℝ) (x ξ : H) : H := x - h • F x + ξ

/-- The actual numerical trajectory, rather than an assumed error recurrence. -/
def eulerTrajectory (F : H → H) (h : ℝ) (ξ : ℕ → H) (x₀ : H) : ℕ → H
  | 0 => x₀
  | n + 1 => eulerStep F h (eulerTrajectory F h ξ x₀ n) (ξ n)

/-- Shared additive noise cancels, and strong monotonicity yields the sharp
quadratic one-step coefficient. -/
theorem euler_sq_contraction (F : H → H) (m h : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hh : 0 ≤ h) (x y ξ : H) :
    ‖eulerStep F h x ξ - eulerStep F h y ξ‖ ^ 2 ≤
      (1 - 2 * m * h + (L : ℝ) ^ 2 * h ^ 2) * ‖x - y‖ ^ 2 := by
  simpa [eulerStep, add_sub_add_right_eq_sub, mul_comm, mul_left_comm, mul_assoc]
    using ULA.gradient_step_sq_bound x y (F x) (F y) m h L hh
      (hF.monotone x y) (hF.lipschitz x y)

/-- A simpler squared contraction with a transparent step restriction. -/
theorem euler_sq_contraction_stable (F : H → H) (m h : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h) (x y ξ : H) :
    ‖eulerStep F h x ξ - eulerStep F h y ξ‖ ^ 2 ≤
      (1 - m * h) * ‖x - y‖ ^ 2 := by
  have hc : 1 - 2 * m * h + (L : ℝ) ^ 2 * h ^ 2 ≤ 1 - m * h := by
    nlinarith [mul_le_mul_of_nonneg_right hs.scaled_lipschitz hs.positive.le]
  exact (euler_sq_contraction F m h L hF hs.positive.le x y ξ).trans
    (mul_le_mul_of_nonneg_right hc (sq_nonneg _))

/-- Norm contraction sufficient for robust coupling and numerical consistency. -/
theorem euler_contraction (F : H → H) (m h : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h) (x y ξ : H) :
    ‖eulerStep F h x ξ - eulerStep F h y ξ‖ ≤
      (1 - m * h / 2) * ‖x - y‖ := by
  have hsq := euler_sq_contraction_stable F m h L hF hs x y ξ
  have hq : 0 ≤ 1 - m * h / 2 := by linarith [hs.scaled_monotonicity]
  have hr : 0 ≤ (1 - m * h / 2) * ‖x - y‖ := mul_nonneg hq (norm_nonneg _)
  have hc : (1 - m * h) * ‖x - y‖ ^ 2 ≤
      ((1 - m * h / 2) * ‖x - y‖) ^ 2 := by
    nlinarith [sq_nonneg (m * h * ‖x - y‖)]
  nlinarith [hsq.trans hc, norm_nonneg (eulerStep F h x ξ - eulerStep F h y ξ)]

/-- The familiar minimum step restriction implies the division-free one. -/
theorem stableStep_of_min (m h : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hL : 0 < (L : ℝ)) (hh : 0 < h)
    (hsmall : h ≤ min (1 / m) (m / (L : ℝ) ^ 2)) : StableStep m L h where
  positive := hh
  monotonicity_positive := hm
  scaled_monotonicity := by
    have ht := (le_div_iff₀ hm).mp (hsmall.trans (min_le_left _ _))
    nlinarith
  scaled_lipschitz :=
    (le_div_iff₀ (sq_pos_of_pos hL)).mp (hsmall.trans (min_le_right _ _))

/-- A single update separates force approximation error from the reference's
local discretization defect. No stochastic independence is required. -/
theorem euler_local_comparison (F G : H → H) (m h B R : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h)
    (x y yNext ξ : H) (hforce : ‖G x - F x‖ ≤ B)
    (hdefect : ‖yNext - eulerStep F h y ξ‖ ≤ R) :
    ‖eulerStep G h x ξ - yNext‖ ≤
      (1 - m * h / 2) * ‖x - y‖ + h * B + R := by
  have hG : ‖eulerStep G h x ξ - eulerStep F h x ξ‖ ≤ h * B := by
    rw [show eulerStep G h x ξ - eulerStep F h x ξ = -h • (G x - F x) by
      unfold eulerStep; module]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (neg_nonpos.mpr hs.positive.le), neg_neg]
    exact mul_le_mul_of_nonneg_left hforce hs.positive.le
  have hd : ‖eulerStep F h y ξ - yNext‖ ≤ R := by simpa [norm_sub_rev] using hdefect
  calc
    ‖eulerStep G h x ξ - yNext‖ ≤
        ‖eulerStep G h x ξ - eulerStep F h x ξ‖ +
          ‖eulerStep F h x ξ - eulerStep F h y ξ‖ +
          ‖eulerStep F h y ξ - yNext‖ := by
      calc
        _ = ‖(eulerStep G h x ξ - eulerStep F h x ξ) +
          (eulerStep F h x ξ - eulerStep F h y ξ) +
          (eulerStep F h y ξ - yNext)‖ := by congr 1; module
        _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ _ := by linarith [euler_contraction F m h L hF hs x y ξ]

/-- Finite-horizon robust numerical bound, including the exact geometric factor.
`G` is the implemented force; `F` is the reference force. The reference can be an
exact SDE skeleton once the stated local defect estimate has been established. -/
theorem trajectory_error_exact (F G : H → H) (m h B D : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h)
    (ξ : ℕ → H) (x₀ : H) (y : ℕ → H)
    (hforce : ∀ n, ‖G (eulerTrajectory G h ξ x₀ n) - F (eulerTrajectory G h ξ x₀ n)‖ ≤ B)
    (hdefect : ∀ n, ‖y (n + 1) - eulerStep F h (y n) (ξ n)‖ ≤ D * h * Real.sqrt h)
    (n : ℕ) :
    ‖eulerTrajectory G h ξ x₀ n - y n‖ ≤
      (1 - m * h / 2) ^ n * ‖x₀ - y 0‖ +
        (h * B + D * h * Real.sqrt h) *
          (1 - (1 - m * h / 2) ^ n) / (1 - (1 - m * h / 2)) := by
  have hq : 0 ≤ 1 - m * h / 2 := by linarith [hs.scaled_monotonicity]
  have hq1 : 1 - m * h / 2 < 1 := by nlinarith [hs.positive, hs.monotonicity_positive]
  apply ULA.affine_recurrence_exact (fun k ↦ ‖eulerTrajectory G h ξ x₀ k - y k‖)
    (1 - m * h / 2) (h * B + D * h * Real.sqrt h) hq hq1
    (fun k ↦ ?_) n
  simpa [eulerTrajectory, add_assoc] using euler_local_comparison F G m h B
    (D * h * Real.sqrt h) L hF hs (eulerTrajectory G h ξ x₀ k) (y k)
    (y (k + 1)) (ξ k) (hforce k) (hdefect k)

/-- Uniform numerical and model bias: `2 B / m + (2 D / m) sqrt h`.
The dimension and number of particles do not enter this algebraic estimate. -/
theorem trajectory_error_bound (F G : H → H) (m h B D : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (ξ : ℕ → H) (x₀ : H) (y : ℕ → H)
    (hforce : ∀ n, ‖G (eulerTrajectory G h ξ x₀ n) - F (eulerTrajectory G h ξ x₀ n)‖ ≤ B)
    (hdefect : ∀ n, ‖y (n + 1) - eulerStep F h (y n) (ξ n)‖ ≤ D * h * Real.sqrt h)
    (n : ℕ) :
    ‖eulerTrajectory G h ξ x₀ n - y n‖ ≤
      (1 - m * h / 2) ^ n * ‖x₀ - y 0‖ +
        (2 / m) * (B + D * Real.sqrt h) := by
  have hq : 0 ≤ 1 - m * h / 2 := by linarith [hs.scaled_monotonicity]
  have hq1 : 1 - m * h / 2 < 1 := by nlinarith [hs.positive, hs.monotonicity_positive]
  have hr := ULA.affine_recurrence_bound (fun k ↦ ‖eulerTrajectory G h ξ x₀ k - y k‖)
    (1 - m * h / 2) (h * B + D * h * Real.sqrt h) hq hq1
    (by have hh := hs.positive.le; positivity) (fun k ↦ ?_) n
  · simpa only [eulerTrajectory] using (hr.trans_eq (by
      congr 1
      field_simp [ne_of_gt hs.positive, ne_of_gt hs.monotonicity_positive]
      ; ring))
  · simpa [eulerTrajectory, add_assoc] using euler_local_comparison F G m h B
      (D * h * Real.sqrt h) L hF hs (eulerTrajectory G h ξ x₀ k) (y k)
      (y (k + 1)) (ξ k) (hforce k) (hdefect k)

end LatentDiffusion

namespace LatentDiffusion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Squared coupling error averaged over a finite probability space. -/
def finiteMeanSq {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (z : Ω → H) : ℝ :=
  ∑ ω, p ω * ‖z ω‖ ^ 2

/-- Explicit finite probability weights. Normalization gives the expression its
usual expectation interpretation; the algebraic estimates only need positivity. -/
structure ProbabilityWeights {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) : Prop where
  nonnegative : ∀ ω, 0 ≤ p ω
  total : ∑ ω, p ω = 1

/-- Euler with a shared additive increment and an additional stochastic force
innovation `ζ`, multiplied by the step size. -/
def noisyEulerTrajectory {Ω : Type*} (F : H → H) (h : ℝ)
    (ξ ζ : ℕ → Ω → H) (x₀ : Ω → H) (n : ℕ) (ω : Ω) : H :=
  eulerTrajectory F h (fun k ↦ ξ k ω + h • ζ k ω) (x₀ ω) n

/-- The zero cross moment needed from a centered innovation is stated on the
current Euler displacement. Conditional mean zero given the current states and
shared increment is a sufficient probabilistic condition for this assumption. -/
structure CenteredInnovationControl {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (F : H → H) (h σ : ℝ) (ξ ζ : ℕ → Ω → H)
    (x₀ y₀ : Ω → H) : Prop where
  orthogonal : ∀ n, ∑ ω, p ω * inner ℝ
    (eulerStep F h (noisyEulerTrajectory F h ξ ζ x₀ n ω) (ξ n ω) -
      eulerStep F h (eulerTrajectory F h (fun k ↦ ξ k ω) (y₀ ω) n) (ξ n ω))
    (ζ n ω) = 0
  variance : ∀ n, finiteMeanSq p (ζ n) ≤ σ ^ 2

/-- Pythagorean identity after averaging: only the explicit cross moment is used. -/
theorem finiteMeanSq_orthogonal_add {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (a z : Ω → H) (h : ℝ)
    (horth : ∑ ω, p ω * inner ℝ (a ω) (z ω) = 0) :
    finiteMeanSq p (fun ω ↦ a ω + h • z ω) =
      finiteMeanSq p a + h ^ 2 * finiteMeanSq p z := by
  have hp (ω : Ω) : p ω * ‖a ω + h • z ω‖ ^ 2 =
      p ω * ‖a ω‖ ^ 2 + (2 * h) * (p ω * inner ℝ (a ω) (z ω)) +
        h ^ 2 * (p ω * ‖z ω‖ ^ 2) := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  simp_rw [finiteMeanSq, hp, Finset.sum_add_distrib, ← Finset.mul_sum, horth]
  ring

/-- Centered stochastic force error has a mean-square floor of order `h`, rather
than the order-one floor for an arbitrary bounded force error. The result is for
actual coupled Euler recursions on any finite probability space. -/
theorem centered_noise_mean_square_bound {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ProbabilityWeights p)
    (F : H → H) (m h σ : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h)
    (ξ ζ : ℕ → Ω → H) (x₀ y₀ : Ω → H)
    (hc : CenteredInnovationControl p F h σ ξ ζ x₀ y₀) (n : ℕ) :
    finiteMeanSq p (fun ω ↦ noisyEulerTrajectory F h ξ ζ x₀ n ω -
      eulerTrajectory F h (fun k ↦ ξ k ω) (y₀ ω) n) ≤
        (1 - m * h) ^ n * finiteMeanSq p (fun ω ↦ x₀ ω - y₀ ω) +
          h * σ ^ 2 / m := by
  let X : ℕ → Ω → H := noisyEulerTrajectory F h ξ ζ x₀
  let Y : ℕ → Ω → H := fun k ω ↦ eulerTrajectory F h (fun j ↦ ξ j ω) (y₀ ω) k
  let A : ℕ → Ω → H := fun k ω ↦
    eulerStep F h (X k ω) (ξ k ω) - eulerStep F h (Y k ω) (ξ k ω)
  have hstep (k : ℕ) : finiteMeanSq p (fun ω ↦ X (k + 1) ω - Y (k + 1) ω) ≤
      (1 - m * h) * finiteMeanSq p (fun ω ↦ X k ω - Y k ω) + h ^ 2 * σ ^ 2 := by
    have hupdate : (fun ω ↦ X (k + 1) ω - Y (k + 1) ω) =
        (fun ω ↦ A k ω + h • ζ k ω) := by
      funext ω
      dsimp [X, Y, A, noisyEulerTrajectory, eulerTrajectory, eulerStep]
      module
    rw [hupdate, finiteMeanSq_orthogonal_add p (A k) (ζ k) h (hc.orthogonal k)]
    have hcontract : finiteMeanSq p (A k) ≤
        (1 - m * h) * finiteMeanSq p (fun ω ↦ X k ω - Y k ω) := by
      unfold finiteMeanSq
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro ω _
      have ht := mul_le_mul_of_nonneg_left
        (euler_sq_contraction_stable F m h L hF hs (X k ω) (Y k ω) (ξ k ω))
        (hp.nonnegative ω)
      simpa [A, mul_assoc, mul_comm, mul_left_comm] using ht
    exact add_le_add hcontract (mul_le_mul_of_nonneg_left (hc.variance k) (sq_nonneg h))
  have hq : 0 ≤ 1 - m * h := by linarith [hs.scaled_monotonicity]
  have hq1 : 1 - m * h < 1 := by nlinarith [hs.monotonicity_positive, hs.positive]
  have hr := ULA.affine_recurrence_bound
    (fun k ↦ finiteMeanSq p (fun ω ↦ X k ω - Y k ω))
    (1 - m * h) (h ^ 2 * σ ^ 2) hq hq1 (by positivity) hstep n
  have halgebra : h ^ 2 * σ ^ 2 / (1 - (1 - m * h)) = h * σ ^ 2 / m := by
    field_simp [ne_of_gt hs.monotonicity_positive, ne_of_gt hs.positive]
    ring
  rw [halgebra] at hr
  simpa [X, Y, noisyEulerTrajectory, eulerTrajectory] using hr

end LatentDiffusion

namespace LatentDiffusion

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Primitive assumptions on exact integral reference segments. In an `L²`
realization `G` bounds the drift root mean square and `N sqrt t` bounds the
Brownian-increment root mean square. These are moment assumptions, not a local
numerical error or contraction assumption. `W` is the additive noise path. -/
structure IntegralReference (F : H → H) (h G N : ℝ) (y : ℕ → H)
    (ξ : ℕ → H) (Y W : ℕ → ℝ → H) : Prop where
  starts : ∀ n, Y n 0 = y n
  ends : ∀ n, Y n h = y (n + 1)
  noise_end : ∀ n, W n h = ξ n
  integrable : ∀ n, IntervalIntegrable (fun t ↦ F (Y n t)) volume 0 h
  drift_radius : ∀ n t, t ∈ Set.Icc 0 h → ‖F (Y n t)‖ ≤ G
  noise_growth : ∀ n t, t ∈ Set.Icc 0 h → ‖W n t‖ ≤ N * Real.sqrt t
  equation : ∀ n t, t ∈ Set.Icc 0 h →
    Y n t - Y n 0 = -(∫ s in 0..t, F (Y n s)) + W n t

/-- The local consistency bound is derived from the exact integral equation,
the drift moment bound, and the square-root noise increment bound. -/
theorem integral_reference_local_defect (F : H → H) (m h G N : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hh : 0 ≤ h)
    (y : ℕ → H) (ξ : ℕ → H) (Y W : ℕ → ℝ → H)
    (hr : IntegralReference F h G N y ξ Y W) (n : ℕ) :
    ‖y (n + 1) - eulerStep F h (y n) (ξ n)‖ ≤
      (L : ℝ) * (h ^ 2 * G / 2 + (2 / 3 : ℝ) * h * Real.sqrt h * N) := by
  have hlip : LipschitzWith L F := LipschitzWith.of_dist_le_mul fun x z ↦ by
    simpa only [dist_eq_norm] using hF.lipschitz x z
  have hid := ULA.localDefect_euler_identity F (Y n) (W n) h (hr.integrable n)
    (hr.equation n h ⟨hh, le_rfl⟩)
  have hn : y (n + 1) - eulerStep F h (y n) (ξ n) = -ULA.localDefect F (Y n) h := by
    rw [hr.starts n, hr.ends n, hr.noise_end n] at hid
    unfold eulerStep
    rw [hid]
    module
  rw [hn, norm_neg]
  exact ULA.localDefect_bound F (Y n) (W n) L h G N hh hlip
    (hr.drift_radius n) (hr.noise_growth n) (hr.equation n)

/-- Nonasymptotic Euler error derived from primitive integral-path moment bounds,
with separate numerical bias `O(h G + N sqrt h)` and force-model bias `O(B)`.
The ambient space can be an `L²` Hilbert space, in which case this is an RMS
coupling estimate. An SDE existence theorem and verification of its stated
moment and lifted-force assumptions are separate obligations. -/
theorem integral_reference_error_bound (F A : H → H) (m h B G N : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h)
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hN : 0 ≤ N)
    (y : ℕ → H) (ξ : ℕ → H) (Y W : ℕ → ℝ → H) (x₀ : H)
    (hr : IntegralReference F h G N y ξ Y W)
    (hforce : ∀ n, ‖A (eulerTrajectory A h ξ x₀ n) - F (eulerTrajectory A h ξ x₀ n)‖ ≤ B)
    (n : ℕ) :
    ‖eulerTrajectory A h ξ x₀ n - y n‖ ≤
      (1 - m * h / 2) ^ n * ‖x₀ - y 0‖ +
        2 * B / m + (L : ℝ) / m * (h * G + (4 / 3 : ℝ) * N * Real.sqrt h) := by
  let R : ℝ := (L : ℝ) * (h ^ 2 * G / 2 + (2 / 3 : ℝ) * h * Real.sqrt h * N)
  have hq : 0 ≤ 1 - m * h / 2 := by linarith [hs.scaled_monotonicity]
  have hq1 : 1 - m * h / 2 < 1 := by nlinarith [hs.positive, hs.monotonicity_positive]
  have hb : 0 ≤ h * B + R := by dsimp [R]; have hh := hs.positive.le; positivity
  have hstep (k : ℕ) : ‖eulerTrajectory A h ξ x₀ (k + 1) - y (k + 1)‖ ≤
      (1 - m * h / 2) * ‖eulerTrajectory A h ξ x₀ k - y k‖ + (h * B + R) := by
    simpa only [eulerTrajectory, add_assoc] using euler_local_comparison F A m h B R L
      hF hs (eulerTrajectory A h ξ x₀ k) (y k) (y (k + 1)) (ξ k) (hforce k)
      (integral_reference_local_defect F m h G N L hF hs.positive.le y ξ Y W hr k)
  have ht := ULA.affine_recurrence_bound (fun k ↦ ‖eulerTrajectory A h ξ x₀ k - y k‖)
    (1 - m * h / 2) (h * B + R) hq hq1 hb hstep n
  have halgebra : (h * B + R) / (1 - (1 - m * h / 2)) =
      2 * B / m + (L : ℝ) / m * (h * G + (4 / 3 : ℝ) * N * Real.sqrt h) := by
    dsimp [R]
    field_simp [ne_of_gt hs.positive, ne_of_gt hs.monotonicity_positive]
    ring
  rw [halgebra] at ht
  simpa [eulerTrajectory, add_assoc] using ht

end LatentDiffusion

namespace LatentDiffusion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Centered local force innovations in a Hilbert space. On `L²(Ω,P;E)`, the
orthogonality field is exactly a zero expected cross term, and the variance
field is a second-moment bound on the stochastic force innovation. -/
structure HilbertInnovationControl (F : H → H) (h σ : ℝ)
    (ξ ζ : ℕ → H) (x₀ y₀ : H) : Prop where
  orthogonal : ∀ n, inner ℝ
    (eulerStep F h (eulerTrajectory F h (fun k ↦ ξ k + h • ζ k) x₀ n) (ξ n) -
      eulerStep F h (eulerTrajectory F h ξ y₀ n) (ξ n)) (ζ n) = 0
  variance : ∀ n, ‖ζ n‖ ^ 2 ≤ σ ^ 2

/-- Uniform second-moment stability for centered stochastic force errors in an
arbitrary real Hilbert space, including genuine `L²` probability spaces. -/
theorem hilbert_innovation_sq_bound (F : H → H) (m h σ : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h)
    (ξ ζ : ℕ → H) (x₀ y₀ : H) (hc : HilbertInnovationControl F h σ ξ ζ x₀ y₀)
    (n : ℕ) :
    ‖eulerTrajectory F h (fun k ↦ ξ k + h • ζ k) x₀ n - eulerTrajectory F h ξ y₀ n‖ ^ 2 ≤
      (1 - m * h) ^ n * ‖x₀ - y₀‖ ^ 2 + h * σ ^ 2 / m := by
  let X : ℕ → H := eulerTrajectory F h (fun k ↦ ξ k + h • ζ k) x₀
  let Y : ℕ → H := eulerTrajectory F h ξ y₀
  have hstep (k : ℕ) : ‖X (k + 1) - Y (k + 1)‖ ^ 2 ≤
      (1 - m * h) * ‖X k - Y k‖ ^ 2 + h ^ 2 * σ ^ 2 := by
    have hid : X (k + 1) - Y (k + 1) =
        (eulerStep F h (X k) (ξ k) - eulerStep F h (Y k) (ξ k)) + h • ζ k := by
      dsimp [X, Y, eulerTrajectory, eulerStep]
      module
    rw [hid, norm_add_sq_real, real_inner_smul_right, hc.orthogonal k,
      mul_zero, mul_zero, add_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact add_le_add (euler_sq_contraction_stable F m h L hF hs (X k) (Y k) (ξ k))
      (mul_le_mul_of_nonneg_left (hc.variance k) (sq_nonneg h))
  have hq : 0 ≤ 1 - m * h := by linarith [hs.scaled_monotonicity]
  have hq1 : 1 - m * h < 1 := by nlinarith [hs.monotonicity_positive, hs.positive]
  have ht := ULA.affine_recurrence_bound (fun k ↦ ‖X k - Y k‖ ^ 2)
    (1 - m * h) (h ^ 2 * σ ^ 2) hq hq1 (by positivity) hstep n
  have halgebra : h ^ 2 * σ ^ 2 / (1 - (1 - m * h)) = h * σ ^ 2 / m := by
    field_simp [ne_of_gt hs.monotonicity_positive, ne_of_gt hs.positive]
    ring
  rw [halgebra] at ht
  simpa [X, Y, eulerTrajectory] using ht

section ArbitraryProbability

open MeasureTheory

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Actual expectation interpretation of the Hilbert squared norm. `Lp` ensures
square integrability of every variable; no totalized nonintegrable expectation
is used as an error metric. -/
theorem l2_norm_sq_eq_expectation (X : Lp E 2 P) :
    ‖X‖ ^ 2 = ∫ ω, ‖X ω‖ ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun ω ↦ real_inner_self_eq_norm_sq _)

/-- Nonasymptotic mean-square stochastic-oracle bound on an arbitrary probability
space, permitting Gaussian innovations. `F` is the explicitly supplied force
on actual `L²` random variables and its monotonicity/Lipschitz assumptions must
hold in `L²`; pointwise cloud assumptions can be lifted separately. -/
theorem l2_innovation_mean_square_bound
    (F : Lp E 2 P → Lp E 2 P) (m h σ : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h)
    (ξ ζ : ℕ → Lp E 2 P) (x₀ y₀ : Lp E 2 P)
    (hc : HilbertInnovationControl F h σ ξ ζ x₀ y₀) (n : ℕ) :
    (∫ ω, ‖(eulerTrajectory F h (fun k ↦ ξ k + h • ζ k) x₀ n -
      eulerTrajectory F h ξ y₀ n) ω‖ ^ 2 ∂P) ≤
        (1 - m * h) ^ n * (∫ ω, ‖(x₀ - y₀) ω‖ ^ 2 ∂P) + h * σ ^ 2 / m := by
  simpa only [← l2_norm_sq_eq_expectation] using
    hilbert_innovation_sq_bound F m h σ L hF hs ξ ζ x₀ y₀ hc n

end ArbitraryProbability

end LatentDiffusion
