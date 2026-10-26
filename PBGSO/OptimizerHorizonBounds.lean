import PBGSO.IntegralQuadraticEnergy

/-! # Derived finite-horizon parameter bounds
The original optimizer integral equation with merely L¹ drift supplies
continuity and an actual bound for every continuous parameter projection.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO.OptimizerHorizonBounds
variable {S Θ : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/-- The original optimizer ODE supplies path continuity; no derivative or
regularity of its integrand at individual times is required. -/
theorem continuousOn (T : ℝ≥0) (a g : ℝ → S)
    (hg : IntervalIntegrable g volume 0 (T : ℝ))
    (heq : ∀ t ∈ Icc 0 (T : ℝ), a t = a 0 + ∫ r in 0..t, g r) :
    ContinuousOn a (Icc 0 (T : ℝ)) := by
  have hi := (IntegralQuadraticEnergy.integral_absolutelyContinuous g hg).continuousOn
  rw [uIcc_of_le T.coe_nonneg] at hi
  exact (continuousOn_const.add hi).congr (fun t ht => heq t ht)

/-- The finite parameter bound used in original linear-growth assumptions
is chosen from the actual optimizer trajectory, rather than supplied. -/
theorem exists_parameter_bound (T : ℝ≥0) (a g : ℝ → S) (parameter : S → Θ)
    (hp : Continuous parameter) (hg : IntervalIntegrable g volume 0 (T : ℝ))
    (heq : ∀ t ∈ Icc 0 (T : ℝ), a t = a 0 + ∫ r in 0..t, g r) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ t ∈ Icc 0 (T : ℝ), ‖parameter (a t)‖ ≤ P := by
  have ha := hp.comp_continuousOn (continuousOn T a g hg heq)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn ha
  exact ⟨max 0 C, le_max_left _ _, fun t ht => (hC t ht).trans (le_max_right _ _)⟩

end PBGSO.OptimizerHorizonBounds
