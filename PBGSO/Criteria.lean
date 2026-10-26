import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # Algebraic sufficient conditions from the PBGSO appendix

These estimates are valid for nonconservative forces. The quantities in the
scalar comparison lemmas are the separate optimiser and sampler contributions;
the lemmas do not assume a stochastic energy identity or assert SDE existence.
-/

noncomputable section
open scoped RealInnerProductSpace
namespace PBGSO

/-- Diagonal dominance gives an explicit small-gain rate, without a spectral
eigenvalue computation. Here `a,b` are the two squared-energy square roots. -/
theorem small_gain_diagonal (a b rOpt rSam cross diffusion ρ : ℝ)
    (hc : 0 ≤ cross) (ho : ρ ≤ rOpt - diffusion - cross / 2)
    (hs : ρ ≤ rSam - diffusion - cross / 2) :
    -rOpt * a ^ 2 - rSam * b ^ 2 + cross * a * b +
      diffusion * (a ^ 2 + b ^ 2) ≤ -ρ * (a ^ 2 + b ^ 2) := by
  have hcross := mul_nonneg hc (sq_nonneg (a - b))
  have hOpt := mul_nonneg (sub_nonneg.mpr ho) (sq_nonneg a)
  have hSam := mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg b)
  nlinarith

/-- The determinant small-gain condition, written as a completed square.
It proves positive definiteness for every nonzero pair. -/
theorem small_gain_positive (A B C a b : ℝ) (hA : 0 < A)
    (hdet : C ^ 2 < 4 * A * B) (hab : a ≠ 0 ∨ b ≠ 0) :
    0 < A * a ^ 2 - C * a * b + B * b ^ 2 := by
  have hid : 4 * A * (A * a ^ 2 - C * a * b + B * b ^ 2) =
      (2 * A * a - C * b) ^ 2 + (4 * A * B - C ^ 2) * b ^ 2 := by ring
  by_cases hb : b = 0
  · have ha : a ≠ 0 := hab.resolve_right (by simpa only [hb, ne_eq, not_true_eq_false, not_false_eq_true])
    simp only [hb, mul_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero]
    exact mul_pos hA (sq_pos_of_ne_zero ha)
  · have hp := mul_pos (sub_pos.mpr hdet) (sq_pos_of_ne_zero hb)
    nlinarith [sq_nonneg (2 * A * a - C * b)]

/-- Combine projected strong monotonicity, auxiliary dissipation and an
explicit metric comparison. No conservative-potential assumption is used. -/
theorem projected_dissipation (workOpt workSam opt sam R auxOpt auxSam
    β rPhi AOpt ASam ρ energy : ℝ)
    (hβ : 0 ≤ β)
    (hPhi : rPhi * R ≤ workOpt + workSam)
    (hOpt : opt ≤ -β * workOpt - auxOpt + AOpt * R)
    (hSam : sam ≤ -β * workSam - auxSam + ASam * R)
    (hmetric : ρ * energy ≤ (β * rPhi - AOpt - ASam) * R + auxOpt + auxSam) :
    opt + sam ≤ -ρ * energy := by
  have hw := mul_le_mul_of_nonneg_left hPhi hβ
  linarith

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The appendix hypocoercive metric, with beta fixed to one. -/
def hypocoerciveEnergy (γ : ℝ) (q p : H) : ℝ :=
  γ * ‖q‖ ^ 2 + 2 * ⟪q, p⟫ + (2 / γ) * ‖p‖ ^ 2

/-- A sum-of-squares identity proves positivity of the actual metric. -/
theorem hypocoerciveEnergy_identity (γ : ℝ) (hγ : γ ≠ 0) (q p : H) :
    γ * hypocoerciveEnergy γ q p = ‖γ • q + p‖ ^ 2 + ‖p‖ ^ 2 := by
  simp only [hypocoerciveEnergy, ← real_inner_self_eq_norm_sq, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm p q]
  field_simp
  <;> ring

/-- Strict positivity holds precisely away from the zero phase vector. -/
theorem hypocoerciveEnergy_pos (γ : ℝ) (hγ : 0 < γ) (q p : H)
    (hqp : q ≠ 0 ∨ p ≠ 0) : 0 < hypocoerciveEnergy γ q p := by
  have hid := hypocoerciveEnergy_identity γ (ne_of_gt hγ) q p
  by_cases hp : p = 0
  · have hq : q ≠ 0 := hqp.resolve_right (by simpa only [hp, ne_eq, not_true_eq_false, not_false_eq_true])
    simp only [hypocoerciveEnergy, hp, norm_zero, inner_zero_right,
      zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
    exact mul_pos hγ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hq))
  · have hn := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hp)
    nlinarith [sq_nonneg ‖γ • q + p‖]

/-- Exact metric pairing along q'=p, p'=-f-gamma p. This identity does
not require f to be the gradient of a potential. -/
theorem hypocoercive_pairing (γ : ℝ) (hγ : γ ≠ 0) (q p f : H) :
    ⟪q, γ • p + (-f - γ • p)⟫ +
      ⟪p, p + (2 / γ) • (-f - γ • p)⟫ =
      -⟪q, f⟫ - ‖p‖ ^ 2 - (2 / γ) * ⟪p, f⟫ := by
  simp only [inner_add_right, inner_sub_right, inner_neg_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp
  <;> ring

/-- Young's inequality in the exact coefficient needed by the appendix. -/
theorem force_cross_young (δ η : ℝ) (hη : 0 < η) (p f : H) :
    -δ * ⟪p, f⟫ ≤ η * ‖p‖ ^ 2 + δ ^ 2 / (4 * η) * ‖f‖ ^ 2 := by
  have hs := sq_nonneg ‖(2 * η) • p + δ • f‖
  rw [← real_inner_self_eq_norm_sq] at hs
  simp only [inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm p f,
    real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hs
  have hy : -δ * ⟪p, f⟫ - η * ‖p‖ ^ 2 ≤ δ ^ 2 * ‖f‖ ^ 2 / (4 * η) := by
    apply (le_div_iff₀ (show 0 < 4 * η by positivity)).mpr
    nlinarith
  rw [div_mul_eq_mul_div]
  linarith

/-- An explicit upper norm comparison for the twisted metric. -/
theorem hypocoerciveEnergy_upper (γ : ℝ) (hγ : 0 < γ) (q p : H) :
    hypocoerciveEnergy γ q p ≤
      (γ + 1 + 2 / γ) * (‖q‖ ^ 2 + ‖p‖ ^ 2) := by
  have hcross := sq_nonneg ‖q - p‖
  rw [norm_sub_sq_real] at hcross
  have hdiv : 0 ≤ 2 / γ := by positivity
  have hq := mul_nonneg hdiv (sq_nonneg ‖q‖)
  have hp := mul_nonneg hγ.le (sq_nonneg ‖p‖)
  dsimp [hypocoerciveEnergy]
  nlinarith

/-- Quantitative hypocoercivity for a strongly monotone, possibly
nonconservative joint force. `f` is the force difference, not a Hessian.
The displayed coefficient inequalities give the rate directly. -/
theorem hypocoercive_dissipation (γ η r L ρ : ℝ) (hγ : 0 < γ)
    (hη : 0 < η) (hρ : 0 ≤ ρ) (q p f : H)
    (hmono : r * ‖q‖ ^ 2 ≤ ⟪q, f⟫)
    (hforce : ‖f‖ ^ 2 ≤ L ^ 2 * ‖q‖ ^ 2)
    (hrateQ : ρ * (γ + 1 + 2 / γ) ≤ r - (2 / γ) ^ 2 / (4 * η) * L ^ 2)
    (hrateP : ρ * (γ + 1 + 2 / γ) ≤ 1 - η) :
    -⟪q, f⟫ - ‖p‖ ^ 2 - (2 / γ) * ⟪p, f⟫ ≤
      -ρ * hypocoerciveEnergy γ q p := by
  have hy := force_cross_young (2 / γ) η hη p f
  have hcoef : 0 ≤ (2 / γ) ^ 2 / (4 * η) := by positivity
  have hf := mul_le_mul_of_nonneg_left hforce hcoef
  have hq := mul_le_mul_of_nonneg_right hrateQ (sq_nonneg ‖q‖)
  have hp := mul_le_mul_of_nonneg_right hrateP (sq_nonneg ‖p‖)
  have he := mul_le_mul_of_nonneg_left (hypocoerciveEnergy_upper γ hγ q p) hρ
  nlinarith

end Hilbert
end PBGSO
