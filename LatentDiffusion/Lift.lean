import LatentDiffusion.Numerics
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# From pointwise cloud forces to actual square-integrable random variables

The force at the origin need not vanish. We center the force before applying
mathlib's Lipschitz composition operator on `L²`, then add its constant value
back. The resulting operator is proved to agree almost everywhere with the
original pointwise force. Its strong monotonicity and Lipschitz constants are
derived by integration; they are not added assumptions on a random-force map.
-/

noncomputable section
open MeasureTheory
open scoped NNReal

namespace LatentDiffusion

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- A genuine constant square-integrable random variable. -/
def constantL2 (v : E) : Lp E 2 P :=
  (memLp_const v).toLp (fun _ : Ω ↦ v)

theorem constantL2_coe (v : E) :
    constantL2 P v =ᵐ[P] fun _ : Ω ↦ v :=
  (memLp_const v).coeFn_toLp

/-- The centered pointwise force always takes zero to zero. -/
def centeredForce (F : E → E) (x : E) : E := F x - F 0

theorem centeredForce_lipschitz (F : E → E) (m : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) : LipschitzWith L (centeredForce F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [dist_eq_norm, centeredForce, sub_sub_sub_cancel_right] using hF.lipschitz x y

/-- The actual force acting on `L²` random variables; no zero-force condition. -/
def liftedForce {F : E → E} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L) (X : Lp E 2 P) : Lp E 2 P :=
  (centeredForce_lipschitz F m L hF).compLp (by simp [centeredForce]) X +
    constantL2 P (F 0)

/-- This operator really evaluates the given pointwise force almost everywhere. -/
theorem liftedForce_coe {F : E → E} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L) (X : Lp E 2 P) :
    liftedForce P hF X =ᵐ[P] fun ω ↦ F (X ω) := by
  unfold liftedForce
  filter_upwards [Lp.coeFn_add
    ((centeredForce_lipschitz F m L hF).compLp (by simp [centeredForce]) X)
      (constantL2 P (F 0)),
    (centeredForce_lipschitz F m L hF).coeFn_compLp (by simp [centeredForce]) X,
    constantL2_coe P (F 0)] with ω ha hf hc
  simp only [ha, Pi.add_apply, hf, Function.comp_apply, centeredForce, hc,
    sub_add_cancel]

/-- Pointwise joint monotonicity and global Lipschitz continuity lift with exactly
the same constants, on every probability space. -/
theorem liftedForce_regular {F : E → E} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L) : ForceRegularity (liftedForce P hF) m L where
  lipschitz X Y := by
    unfold liftedForce
    simpa only [add_sub_add_right_eq_sub] using
      (centeredForce_lipschitz F m L hF).norm_compLp_sub_le
        (by simp [centeredForce]) X Y
  monotone X Y := by
    rw [l2_norm_sq_eq_expectation P (X - Y), L2.inner_def]
    rw [← integral_const_mul]
    have hi : Integrable (fun ω ↦ m * ‖(X - Y) ω‖ ^ 2) P :=
      ((Lp.memLp (X - Y)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul m
    apply integral_mono_ae hi (L2.integrable_inner
      (liftedForce P hF X - liftedForce P hF Y) (X - Y))
    filter_upwards [Lp.coeFn_sub (liftedForce P hF X) (liftedForce P hF Y),
      Lp.coeFn_sub X Y, liftedForce_coe P hF X, liftedForce_coe P hF Y]
      with ω hforce hxy hfx hfy
    simpa only [hforce, hxy, hfx, hfy, Pi.sub_apply] using hF.monotone (X ω) (Y ω)

/-- An `L²` Euler step is the actual pointwise Euler step almost everywhere. -/
theorem lifted_eulerStep_coe {F : E → E} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L) (h : ℝ) (X Ξ : Lp E 2 P) :
    eulerStep (liftedForce P hF) h X Ξ =ᵐ[P]
      fun ω ↦ eulerStep F h (X ω) (Ξ ω) := by
  unfold eulerStep
  filter_upwards [Lp.coeFn_add (X - h • liftedForce P hF X) Ξ,
    Lp.coeFn_sub X (h • liftedForce P hF X),
    Lp.coeFn_smul h (liftedForce P hF X), liftedForce_coe P hF X]
    with ω ha hs hsm hf
  simp only [ha, hs, hsm, hf, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

/-- Every iterate represents the pointwise recursion, for arbitrary square-
integrable increments, including actual Gaussian innovations. -/
theorem lifted_eulerTrajectory_coe {F : E → E} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L) (h : ℝ) (ξ : ℕ → Lp E 2 P)
    (x₀ : Lp E 2 P) (n : ℕ) :
    eulerTrajectory (liftedForce P hF) h ξ x₀ n =ᵐ[P]
      fun ω ↦ eulerTrajectory F h (fun k ↦ ξ k ω) (x₀ ω) n := by
  induction n with
  | zero => exact Filter.EventuallyEq.rfl
  | succ n ih =>
    change eulerStep (liftedForce P hF) h
      (eulerTrajectory (liftedForce P hF) h ξ x₀ n) (ξ n) =ᵐ[P] _
    refine (lifted_eulerStep_coe P hF h _ _).trans ?_
    filter_upwards [ih] with ω hω
    simp only [eulerTrajectory, hω]

/-- Mean-square numerical robustness is now a consequence of assumptions on the
original pointwise force, with no independently assumed `L²` force regularity. -/
theorem pointwise_force_mean_square_bound (F : E → E) (m h σ : ℝ) (L : ℝ≥0)
    (hF : ForceRegularity F m L) (hs : StableStep m L h)
    (ξ ζ : ℕ → Lp E 2 P) (x₀ y₀ : Lp E 2 P)
    (hc : HilbertInnovationControl (liftedForce P hF) h σ ξ ζ x₀ y₀) (n : ℕ) :
    (∫ ω, ‖(eulerTrajectory (liftedForce P hF) h
      (fun k ↦ ξ k + h • ζ k) x₀ n -
      eulerTrajectory (liftedForce P hF) h ξ y₀ n) ω‖ ^ 2 ∂P) ≤
        (1 - m * h) ^ n * (∫ ω, ‖(x₀ - y₀) ω‖ ^ 2 ∂P) + h * σ ^ 2 / m :=
  l2_innovation_mean_square_bound P (liftedForce P hF) m h σ L
    (liftedForce_regular P hF) hs ξ ζ x₀ y₀ hc n

end LatentDiffusion
