import KineticLangevin.Integrator
import KineticLangevin.LocalError

/-! # Exact local error of the exponential integrator

Starting with the variation-of-constants identity for the exact velocity and
the kinematic identity for position, this file identifies the error of the
actual `exponentialStep` with the weighted velocity and position defects.
Both components use the same additive convolution path: the phase innovation
is `(B(h), ∫₀ʰ B(s) ds)`. Brownian stochastic convolution construction and its
joint Gaussian law are separate probabilistic obligations.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The weighted force defect is exactly the force convolution minus its
frozen-force approximation. -/
theorem velocityDefect_eq_integral_sub (g : E → E) (hg : Continuous g)
    (x : ℝ → E) (hx : Continuous x) (γ t : ℝ) :
    velocityDefect g x γ t =
      (∫ s in 0..t, Real.exp (-γ * (t - s)) • g (x s)) - psi γ 1 t • g (x 0) := by
  have hi : IntervalIntegrable (fun s ↦ Real.exp (-γ * (t - s)) • g (x s)) volume 0 t :=
    (by fun_prop : Continuous (fun s ↦ Real.exp (-γ * (t - s)) • g (x s))).intervalIntegrable _ _
  have hi0 : IntervalIntegrable (fun s : ℝ ↦ Real.exp (-γ * (t - s)) • g (x 0)) volume 0 t :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ * (t - s)) • g (x 0))).intervalIntegrable _ _
  simp only [velocityDefect, smul_sub]
  rw [intervalIntegral.integral_sub hi hi0, intervalIntegral.integral_smul_const,
    integral_reverse_exponential]

/-- A mild exact velocity and its frozen-force approximation differ by the
explicit defect, with their common convolution noise cancelling algebraically. -/
theorem frozenVelocity_error (g : E → E) (hg : Continuous g)
    (x : ℝ → E) (hx : Continuous x) (γ t : ℝ) (v0 V B : E)
    (hmild : V = psi γ 0 t • v0 -
      (∫ s in 0..t, Real.exp (-γ * (t - s)) • g (x s)) + B) :
    frozenVelocity γ v0 (g (x 0)) t + B - V = velocityDefect g x γ t := by
  rw [velocityDefect_eq_integral_sub g hg x hx, hmild]
  unfold frozenVelocity
  abel

/-- Integrating the exact frozen-force velocity gives the implemented
position formula. This identity also holds at zero friction. -/
theorem integral_frozenVelocity (γ t : ℝ) (x v force : E) :
    (∫ s in 0..t, frozenVelocity γ v force s) = frozenPosition γ x v force t - x := by
  have hi : IntervalIntegrable (frozenVelocity γ v force) volume 0 t :=
    (((continuous_psi γ 0).smul continuous_const).sub
      ((continuous_psi γ 1).smul continuous_const)).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ ↦ hasDerivAt_frozenPosition γ x v force s) hi
  simpa [frozenPosition] using he

/-- The actual exponential step error is exactly the pair of defects.
The noise in position is the integral of the same velocity convolution. -/
theorem exponentialStep_error_identity
    (g : E → E) (hg : Continuous g) (x V B : ℝ → E)
    (hx : Continuous x) (hV : Continuous V) (hB : Continuous B)
    (γ h : ℝ) (hh : 0 ≤ h)
    (hmild : ∀ t ∈ Icc 0 h, V t = psi γ 0 t • V 0 -
      (∫ s in 0..t, Real.exp (-γ * (t - s)) • g (x s)) + B t)
    (hkin : x h - x 0 = ∫ s in 0..h, V s) :
    exponentialStep g γ h (V 0, x 0) (B h, ∫ s in 0..h, B s) - (V h, x h) =
      (velocityDefect g x γ h, positionDefect g x γ h) := by
  have hv (t : ℝ) (ht : t ∈ Icc 0 h) :
      frozenVelocity γ (V 0) (g (x 0)) t + B t - V t = velocityDefect g x γ t :=
    frozenVelocity_error g hg x hx γ t (V 0) (V t) (B t) (hmild t ht)
  have hiFrozen : IntervalIntegrable (frozenVelocity γ (V 0) (g (x 0))) volume 0 h :=
    (((continuous_psi γ 0).smul continuous_const).sub
      ((continuous_psi γ 1).smul continuous_const)).intervalIntegrable _ _
  have hiB : IntervalIntegrable B volume 0 h := hB.intervalIntegrable _ _
  have hiV : IntervalIntegrable V volume 0 h := hV.intervalIntegrable _ _
  have hp : frozenPosition γ (x 0) (V 0) (g (x 0)) h +
      (∫ s in 0..h, B s) - x h = positionDefect g x γ h := by
    unfold positionDefect
    have he : (∫ s in 0..h, velocityDefect g x γ s) =
        ∫ s in 0..h, frozenVelocity γ (V 0) (g (x 0)) s + B s - V s := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hh] at hs
      exact (hv s hs).symm
    rw [he, intervalIntegral.integral_sub (hiFrozen.add hiB) hiV,
      intervalIntegral.integral_add hiFrozen hiB, integral_frozenVelocity γ h (x 0), ← hkin]
    abel
  ext
  · exact hv h ⟨hh, le_rfl⟩
  · exact hp

/-- The actual implemented exponential step satisfies the `3Mh²C/4` local
transformed-norm bound from its mild exact reference and bounded velocity. -/
theorem exponentialStep_localNorm_bound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (g : F → F) (M : ℝ≥0) (hg : LipschitzWith M g) (x V B : ℝ → F)
    (hx : Continuous x) (hV : Continuous V) (hB : Continuous B)
    (γ h C : ℝ) (hγ : 0 ≤ γ) (hh : 0 ≤ h) (hC : 0 ≤ C) (hsmall : γ * h ≤ 1 / 4)
    (hmild : ∀ t ∈ Icc 0 h, V t = psi γ 0 t • V 0 -
      (∫ s in 0..t, Real.exp (-γ * (t - s)) • g (x s)) + B t)
    (hkin : ∀ t ∈ Icc 0 h, x t - x 0 = ∫ s in 0..t, V s)
    (hvelocity : ∀ t ∈ Icc 0 h, ‖V t‖ ≤ C) :
    transformNorm γ 0
      (exponentialStep g γ h (V 0, x 0) (B h, ∫ s in 0..h, B s) - (V h, x h)) ≤
        (3 / 4 : ℝ) * (M : ℝ) * C * h ^ 2 := by
  rw [exponentialStep_error_identity g hg.continuous x V B hx hV hB γ h hh hmild
    (hkin h ⟨hh, le_rfl⟩)]
  exact transformNorm_le_of_energy_le γ 0 _ _ (by positivity)
    (localDefect_energy_bound g M hg x V γ h C hγ hh hC hsmall hvelocity hkin)

end KineticLangevin
