import ProximalLangevin.Moreau
import ProximalLangevin.Corrections
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option linter.style.header false

/-!
# A conditional consistency check for the full-potential PIPULA assumptions

If the appendix's `g₁ = 0` specialization also carries A3 onto `U = g₂`,
then global value Lipschitzness and a positive global B1 deficit are
incompatible in positive dimension. This concerns that literal specialization,
not a blanket interpretation of the paper's original split decomposition.
-/

noncomputable section
open Set
open scoped NNReal RealInnerProductSpace
namespace ProximalLangevin

/-- A globally bounded field cannot have a positive strong-monotonicity
constant on a nontrivial real Hilbert space. -/
theorem bounded_field_not_stronglyMonotone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nontrivial E]
    (R : E → E) (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K)
    (hbound : ∀ x, ‖R x‖ ≤ K)
    (hmono : ∀ x y, c * ‖x - y‖ ^ 2 ≤ ⟪x - y, R x - R y⟫) : False := by
  let r := 2 * K / c + 1
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨x, hx⟩ := exists_norm_eq E hr.le
  have hR : ‖R x - R 0‖ ≤ 2 * K := by
    have ht := norm_sub_le (R x) (R 0)
    linarith [hbound x, hbound 0]
  have hm := hmono x 0
  rw [sub_zero] at hm
  have hi : ⟪x, R x - R 0⟫ ≤ ‖x‖ * (2 * K) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hR (norm_nonneg _))
  have hrc : c * r = 2 * K + c := by
    dsimp [r]
    field_simp
  rw [hx] at hm hi
  nlinarith

/-- Under a literal full-potential globally Lipschitz reading, B1 cannot hold
with positive deficit in positive dimension. The separate PIPULA theorem
therefore does not assume global Lipschitzness of the full strongly convex U. -/
theorem lipschitz_full_potential_not_proximal_deficit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    {U : E → ℝ} (hU : ConvexOn ℝ univ U) (hb : ∃ b, ∀ x, b ≤ U x)
    {K : ℝ≥0} (hK : LipschitzWith K U) (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ)
    (hB : ∀ x y, ⟪x - y, prox U γ x - prox U γ y⟫ ≤
      (1 - μ) * ‖x - y‖ ^ 2) : False := by
  apply bounded_field_not_stronglyMonotone (residual U γ) (μ / γ) (K : ℝ)
    (div_pos hμ hγ) K.coe_nonneg (residual_norm_le hU hb hγ hK)
  intro x y
  exact Corrections.proximal_displacement_strong_monotonicity (prox U γ) μ γ hγ hB x y

end ProximalLangevin
