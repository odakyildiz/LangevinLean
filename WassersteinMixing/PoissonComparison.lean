import WassersteinMixing.PoissonProcess
import WassersteinMixing.LocalError
import WassersteinMixing.ShiftedEnergy
import WassersteinMixing.Recurrence
import UnadjustedLangevin.Coupling

set_option linter.style.header false

/-! # The stationary Poisson comparison estimate

The general comparison lemma is assembled below from
stationary evaluations, the exact synchronous equation, curvature, adaptation,
and primitive score increments. Corrector, defect and martingale bounds, the
shifted energy recurrence, and the final transport estimate are conclusions.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory

namespace WassersteinMixing

variable {H E Ω : Type*} [m0 : MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]
  {Q : Measure Ω} {P : Parameters}

/-- Primitive comparison data. None of the derived constants 3, 18, 19, or
the final Wasserstein bias estimate is a field of this structure. -/
structure PoissonComparison (S : PoissonProcess H E Q P.step P.step_pos) (score : H) where
  reference : ℕ → Lp E 2 Q
  chain : ℕ → Lp E 2 Q
  increment : ℕ → ℝ → Lp E 2 Q
  curvature : ℕ → Lp E 2 Q →L[ℝ] Lp E 2 Q
  score_bound : ‖score‖ ^ 2 ≤ P.beta * P.dimension
  reference_stationary : ∀ n, Q.map (reference n) = Q.map (reference 0)
  initial_equal : reference 0 = chain 0
  increment_memLp : ∀ n,
    MemLp (increment n) 2 (volume.restrict (Set.Ioc 0 P.step))
  increment_bound : ∀ n, ∀ s ∈ Set.Ioc 0 P.step,
    ‖increment n s‖ ^ 2 ≤ 6 * s * P.beta ^ 2 * P.dimension
  increment_endpoint : ∀ n,
    increment n P.step = S.eval n score - S.eval (n + 1) score
  defect_mean : ∀ n,
    (condExpL2 E ℝ (S.filtration.le n)
      (stationaryLocalDefect (increment n) P.step) : Lp E 2 Q) =
      S.eval n (S.poissonSource score)
  error_step : ∀ n,
    reference (n + 1) - chain (n + 1) =
      (reference n - chain n) - P.step • curvature n (reference n - chain n) +
        stationaryLocalDefect (increment n) P.step
  error_adapted : ∀ n,
    AEStronglyMeasurable[S.filtration n] (reference n - chain n) Q
  curvature_adapted : ∀ n (U : Lp E 2 Q),
    AEStronglyMeasurable[S.filtration n] U Q →
      AEStronglyMeasurable[S.filtration n] (curvature n U) Q
  curvature_symmetric : ∀ n u v,
    inner ℝ (curvature n u) v = inner ℝ u (curvature n v)
  curvature_lower : ∀ n u,
    P.alpha * ‖u‖ ^ 2 ≤ inner ℝ u (curvature n u)
  curvature_upper : ∀ n u,
    inner ℝ u (curvature n u) ≤ P.beta * ‖u‖ ^ 2

namespace PoissonComparison
variable {S : PoissonProcess H E Q P.step P.step_pos} {score : H}
  (C : PoissonComparison S score)

/-- The actual error between the two supplied random variables. -/
def error (n : ℕ) : Lp E 2 Q := C.reference n - C.chain n

/-- The defect is a genuine time integral of score increments. -/
def defect (n : ℕ) : Lp E 2 Q := stationaryLocalDefect (C.increment n) P.step

/-- The predictable shifted drift. -/
def predictable (n : ℕ) : Lp E 2 Q :=
  (C.error n + S.correctorAt score n) -
    P.step • C.curvature n (C.error n + S.correctorAt score n) +
      P.step • C.curvature n (S.correctorAt score n)

include C in
theorem corrector_energy (n : ℕ) :
    ‖S.correctorAt score n‖ ^ 2 ≤ P.correctorBudget := by
  have h := S.correctorAt_norm_sq_le score (P.beta * P.dimension) C.score_bound n
  simpa only [Parameters.correctorBudget, mul_assoc] using h

theorem defect_energy (n : ℕ) : ‖C.defect n‖ ^ 2 ≤ 3 * P.step ^ 3 * P.beta ^ 2 * P.dimension :=
  stationaryLocalDefect_energy_le (C.increment n) P.step P.beta P.dimension
    P.step_pos.le (C.increment_memLp n) (C.increment_bound n)

include C in
theorem score_increment_energy (n : ℕ) :
    ‖S.eval (n + 1) score - S.eval n score‖ ^ 2 ≤
      6 * P.step * P.beta ^ 2 * P.dimension := by
  have h := C.increment_bound n P.step ⟨P.step_pos, le_rfl⟩
  rw [C.increment_endpoint n, norm_sub_rev] at h
  exact h

theorem martingale_energy (n : ℕ) :
    ‖S.martingaleAt score C.defect n‖ ^ 2 ≤ 18 * P.step ^ 3 * P.beta ^ 2 * P.dimension :=
  S.martingaleAt_energy_le score C.defect P.beta P.dimension n
    (C.defect_energy n) (C.score_increment_energy n)

theorem predictable_adapted (n : ℕ) :
    AEStronglyMeasurable[S.filtration n] (C.predictable n) Q := by
  let : Fact (S.filtration n ≤ m0) := ⟨S.filtration.le n⟩
  let M := lpMeas E ℝ (S.filtration n) 2 Q
  have hz : C.error n ∈ M :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr (C.error_adapted n)
  have hg : S.correctorAt score n ∈ M :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr (S.correctorAt_adapted score n)
  have hu := M.add_mem hz hg
  have ha : C.curvature n (C.error n + S.correctorAt score n) ∈ M :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr
      (C.curvature_adapted n _ (mem_lpMeas_iff_aestronglyMeasurable.mp hu))
  have hag : C.curvature n (S.correctorAt score n) ∈ M :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr
      (C.curvature_adapted n _ (mem_lpMeas_iff_aestronglyMeasurable.mp hg))
  exact mem_lpMeas_iff_aestronglyMeasurable.mp
    (M.add_mem (M.sub_mem hu (M.smul_mem P.step ha)) (M.smul_mem P.step hag))

/-- The exact shifted stochastic equation for the constructed residual. -/
theorem shifted_equation (n : ℕ) :
    C.error (n + 1) + S.correctorAt score (n + 1) =
      C.predictable n + S.martingaleAt score C.defect n := by
  exact shifted_error_identity (C.curvature n) P.step (C.error n) (C.error (n + 1))
    (S.correctorAt score n) (S.correctorAt score (n + 1)) (C.defect n)
    (S.martingaleAt score C.defect n) (C.error_step n)
    (S.defect_decomposition score C.defect n)

/-- The complete shifted energy recurrence follows from the primitive data. -/
theorem shifted_energy_step (n : ℕ) :
    ‖C.error (n + 1) + S.correctorAt score (n + 1)‖ ^ 2 ≤
      P.contraction * ‖C.error n + S.correctorAt score n‖ ^ 2 + P.energyForcing := by
  have hp := curvature_weighted_interpolation P (C.curvature n)
    (C.curvature_symmetric n) (C.curvature_lower n) (C.curvature_upper n)
    (C.error n + S.correctorAt score n) (S.correctorAt score n)
  change ‖C.predictable n‖ ^ 2 ≤ _ at hp
  have hc := S.martingaleAt_inner_eq_zero score C.defect n (C.defect_mean n)
    (C.predictable n) (C.predictable_adapted n)
  rw [C.shifted_equation n, centered_energy_identity _ _ hc]
  have hg := mul_le_mul_of_nonneg_left (C.corrector_energy n)
    (mul_nonneg P.step_pos.le P.beta_pos.le)
  have hm := C.martingale_energy n
  dsimp [Parameters.correctorBudget, Parameters.energyForcing] at hg ⊢
  nlinarith

theorem shifted_energy_bound (n : ℕ) :
    ‖C.error n + S.correctorAt score n‖ ^ 2 ≤ P.energyFloor := by
  apply shifted_energy_uniform P
    (fun n ↦ ‖C.error n + S.correctorAt score n‖ ^ 2) _ C.shifted_energy_step n
  simpa only [error, C.initial_equal, sub_self, zero_add] using C.corrector_energy 0

/-- The paper's numerical constant bounds every stationary-start error. -/
theorem error_norm_le_bias (n : ℕ) : ‖C.error n‖ ≤ P.bias :=
  shifted_norm_le_bias P (C.error n) (S.correctorAt score n)
    (C.shifted_energy_bound n) (C.corrector_energy n)

/-- The transport bound is for the actual pushforward laws of the supplied
comparison variables, not an arbitrary function named Wasserstein distance. -/
theorem stationary_transport_bound [BorelSpace E] [SecondCountableTopology E] (n : ℕ) :
    ULA.wasserstein2Real (Q.map (C.reference 0)) (Q.map (C.chain n)) ≤ P.bias := by
  rw [← C.reference_stationary n]
  exact (ULA.wasserstein2_le_Lp_cost_real Q (C.reference n) (C.chain n)).trans
    (C.error_norm_le_bias n)

/-- Finiteness is proved from the actual coupling before any real conversion. -/
theorem stationary_transport_finite [BorelSpace E] [SecondCountableTopology E] (n : ℕ) :
    ULA.wasserstein2 (Q.map (C.reference 0)) (Q.map (C.chain n)) ≠ ⊤ := by
  rw [← C.reference_stationary n]
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (ULA.wasserstein2_le_Lp_cost Q (C.reference n) (C.chain n))

end PoissonComparison
end WassersteinMixing
