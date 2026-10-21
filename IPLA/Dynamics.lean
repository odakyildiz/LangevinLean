import IPLA.Model

set_option linter.style.header false

/-! # Exact pointwise IPLA recursion

This module connects the L² representation used in the convergence proof to
the explicit pointwise algorithm. It also expands both coordinate updates and
the lifted potential in the original parameter-particle pair notation.
-/


noncomputable section
open MeasureTheory
open scoped NNReal
namespace IPLA

/-- A joint extraction is exactly the original parameter-particle pair after
unscaling its particle. -/
theorem joint_eq_pair {N dθ dx : ℕ} (i : Fin N) (z : State N dθ dx) :
    joint i z = pair (parameterCLM z) (Real.sqrt N • block z i) := by
  ext a
  cases a <;> simp [joint, pair, block]

/-- The lifted potential is the sum of the original pair potential, with
physical particles equal to `sqrt N` times the scaled particle blocks. -/
theorem potential_eq_pair_sum {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (z : State N dθ dx) :
    potential U z = ∑ i : Fin N,
      U (pair (parameterCLM z) (Real.sqrt N • block z i)) := by
  simp only [potential, joint_eq_pair]

/-- IPLA as an ordinary recursion on scaled states and noise vectors. -/
def scaledChain {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ)
    (initial : State N dθ dx) (noise : ℕ → State N dθ dx) : ℕ → State N dθ dx
  | 0 => initial
  | k + 1 => scaledUpdate U γ (scaledChain U γ initial noise k) (noise k)

@[simp] theorem scaledChain_zero {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ)
    (initial : State N dθ dx) (noise : ℕ → State N dθ dx) :
    scaledChain U γ initial noise 0 = initial := rfl

@[simp] theorem scaledChain_succ {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ)
    (initial : State N dθ dx) (noise : ℕ → State N dθ dx) (k : ℕ) :
    scaledChain U γ initial noise (k + 1) =
      scaledUpdate U γ (scaledChain U γ initial noise k) (noise k) := rfl

/-- The parameter recurrence in the pointwise IPLA chain. -/
theorem scaledChain_parameter {N dθ dx : ℕ} {U : Joint dθ dx → ℝ}
    (hU : Differentiable ℝ U) (γ : ℝ) (initial : State N dθ dx)
    (noise : ℕ → State N dθ dx) (k : ℕ) (j : Fin dθ) :
    scaledChain U γ initial noise (k + 1) (Sum.inl j) =
      scaledChain U γ initial noise k (Sum.inl j) -
        (γ / N) * ∑ i : Fin N, gradient U (joint i (scaledChain U γ initial noise k))
          (Sum.inl j) + Real.sqrt (2 * γ / N) * noise k (Sum.inl j) :=
  scaledUpdate_parameter hU γ _ _ j

/-- The physical-particle recurrence in the pointwise IPLA chain. -/
theorem scaledChain_particle {N dθ dx : ℕ} {U : Joint dθ dx → ℝ}
    (hN : 0 < N) (hU : Differentiable ℝ U) (γ : ℝ) (initial : State N dθ dx)
    (noise : ℕ → State N dθ dx) (k : ℕ) (i : Fin N) (j : Fin dx) :
    Real.sqrt N * scaledChain U γ initial noise (k + 1) (Sum.inr (i, j)) =
      Real.sqrt N * scaledChain U γ initial noise k (Sum.inr (i, j)) -
        γ * gradient U (joint i (scaledChain U γ initial noise k)) (Sum.inr j) +
        Real.sqrt (2 * γ) * noise k (Sum.inr (i, j)) :=
  scaledUpdate_particle hN hU γ _ _ i j

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The L² chain represents the explicit IPLA recursion almost everywhere.
This includes the exact identity between `sqrt (2 * (γ/N))` and the noise
coefficient `sqrt (2*γ/N)` in the displayed IPLA update. -/
theorem lpChain_coe {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P) (k : ℕ) :
    lpChain P (potential U) (γ / N) (potential_gradient_lipschitz hdiff hLip)
      initial noise k =ᵐ[P]
      fun ω ↦ scaledChain U γ (initial ω) (fun n ↦ noise n ω) k := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ ↦ rfl
  | succ k ih =>
      filter_upwards [ULA.lpUlaUpdate_coe P (potential U) (γ / N)
        (potential_gradient_lipschitz hdiff hLip)
        (lpChain P (potential U) (γ / N) (potential_gradient_lipschitz hdiff hLip)
          initial noise k) (noise k), ih] with ω hupdate hprev
      simpa only [lpChain_succ, scaledChain_succ, scaledUpdate, hprev,
        mul_div_assoc] using hupdate

/-- The laws appearing in the final theorem are exactly the laws of the
explicit, noise-driven, pointwise IPLA recursion. -/
theorem laws_eq_scaledChain {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) (γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P) (k : ℕ) :
    laws P U γ L hdiff hLip initial noise k =
      P.map (fun ω ↦ scaledChain U γ (initial ω) (fun n ↦ noise n ω) k) := by
  exact Measure.map_congr (lpChain_coe P U γ L hdiff hLip initial noise k)

end IPLA
