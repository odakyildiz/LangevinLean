import GradientDescent.StrongConvexity
import GradientDescent.Step

/-! # Existence and uniqueness of the minimizer

An auxiliary small gradient step is a contraction on the complete Hilbert space.
Its Banach fixed point is stationary, hence is the unique global minimizer.
The auxiliary step does not restrict the step used in the convergence theorem.
-/

open scoped NNReal

noncomputable section

namespace GradientDescent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Strong convexity and a globally Lipschitz gradient imply existence of a stationary point. -/
theorem exists_stationary {f : H → ℝ} {m : ℝ} {L : ℝ≥0}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hm : 0 < m) (hLip : LipschitzWith L (gradient f)) :
    ∃ z : H, gradient f z = 0 := by
  let α : ℝ := m / ((L : ℝ) ^ 2 + m ^ 2)
  have hden : 0 < (L : ℝ) ^ 2 + m ^ 2 := by positivity
  have hα : 0 < α := div_pos hm hden
  have hsmall : α * (L : ℝ) ^ 2 < 2 * m := by
    dsimp [α]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith [sq_nonneg (L : ℝ), mul_pos hm (sq_pos_of_pos hm)]
  have hc := contracting_gradient_step (gradient f) m α L hα hsmall
    (strong_gradient_monotone hdiff hsc) hLip
  obtain ⟨z, hz, _⟩ := hc.exists_fixedPoint (0 : H) (edist_ne_top _ _)
  have hz' : z - α • gradient f z = z := hz
  have hzero : α • gradient f z = 0 := by
    apply (sub_eq_self.mp hz')
  exact ⟨z, (smul_eq_zero.mp hzero).resolve_left (ne_of_gt hα)⟩

/-- A stationary point of a strongly convex function is its unique global minimizer. -/
theorem stationary_unique_minimizer {f : H → ℝ} {m : ℝ}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f) (hm : 0 < m)
    {z : H} (hz : gradient f z = 0) :
    (∀ x, f z ≤ f x) ∧ (∀ y, (∀ x, f y ≤ f x) → y = z) := by
  constructor
  · intro x
    have h := strong_lower_gap hdiff hsc hz x
    have hn : 0 ≤ m / 2 * ‖x - z‖ ^ 2 := by positivity
    linarith
  · intro y hy
    have h := strong_lower_gap hdiff hsc hz y
    have hsq : ‖y - z‖ ^ 2 = 0 := by
      have hnonneg := sq_nonneg ‖y - z‖
      have hmin := hy z
      nlinarith
    have hn : ‖y - z‖ = 0 := (sq_eq_zero_iff).mp hsq
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The assumptions imply a unique global minimizer, without assuming attainment. -/
theorem exists_unique_minimizer {f : H → ℝ} {m : ℝ} {L : ℝ≥0}
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hm : 0 < m) (hLip : LipschitzWith L (gradient f)) :
    ∃! z : H, ∀ x : H, f z ≤ f x := by
  obtain ⟨z, hz⟩ := exists_stationary hdiff hsc hm hLip
  obtain ⟨hmin, huniq⟩ := stationary_unique_minimizer hdiff hsc hm hz
  exact ⟨z, hmin, huniq⟩

end GradientDescent
