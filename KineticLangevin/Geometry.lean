import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-! # The changing coordinates of Dalalyan and Riou-Durand

The phase coordinates are ordered `(velocity, position)`.  Their Euclidean
energy is deliberately written as a sum of squares: the default norm on a Lean
product is the maximum norm, and is not the Euclidean norm used in the paper.
All statements hold in any real inner product space, including an L² space.
-/

noncomputable section

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The paper's two transformed coordinates, with `a = λ₋` and `γ-a = λ₊`. -/
def transform (γ a : ℝ) (s : E × E) : E × E :=
  (s.1 + (γ - a) • s.2, -s.1 - a • s.2)

/-- Squared Euclidean energy of the transformed phase point. -/
def transformEnergy (γ a : ℝ) (s : E × E) : ℝ :=
  ‖(transform γ a s).1‖ ^ 2 + ‖(transform γ a s).2‖ ^ 2

theorem transformEnergy_nonneg (γ a : ℝ) (s : E × E) :
    0 ≤ transformEnergy γ a s := by
  unfold transformEnergy
  positivity

/-- Adding the transformed coordinates recovers `(γ-2a) position`. -/
theorem transform_add (γ a : ℝ) (s : E × E) :
    (transform γ a s).1 + (transform γ a s).2 = (γ - 2 * a) • s.2 := by
  simp only [transform, sub_smul, mul_smul]
  module

/-- The inverse change of coordinates is valid whenever `a ≠ γ/2`. -/
theorem transform_inverse_position (γ a : ℝ) (h : γ - 2 * a ≠ 0) (s : E × E) :
    (γ - 2 * a)⁻¹ • ((transform γ a s).1 + (transform γ a s).2) = s.2 := by
  rw [transform_add, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem transform_inverse_velocity (γ a : ℝ) (h : γ - 2 * a ≠ 0) (s : E × E) :
    -(γ - 2 * a)⁻¹ •
      (a • (transform γ a s).1 + (γ - a) • (transform γ a s).2) = s.1 := by
  have he : a • (transform γ a s).1 + (γ - a) • (transform γ a s).2 =
      -(γ - 2 * a) • s.1 := by
    simp only [transform, smul_add, smul_sub, smul_neg, smul_smul]
    module
  rw [he, smul_smul]
  have hc : -(γ - 2 * a)⁻¹ * -(γ - 2 * a) = 1 := by
    rw [neg_mul_neg]
    exact inv_mul_cancel₀ h
  rw [hc, one_smul]

/-- The position projection has norm at most `√2 / (γ-2a)`.  The squared
version avoids introducing square-root simplifications into later estimates. -/
theorem position_sq_le_energy (γ a : ℝ) (s : E × E) :
    (γ - 2 * a) ^ 2 * ‖s.2‖ ^ 2 ≤ 2 * transformEnergy γ a s := by
  have htriangle := norm_add_le (transform γ a s).1 (transform γ a s).2
  have hsum : ‖(transform γ a s).1 + (transform γ a s).2‖ ^ 2 ≤
      2 * (‖(transform γ a s).1‖ ^ 2 + ‖(transform γ a s).2‖ ^ 2) := by
    nlinarith [norm_nonneg ((transform γ a s).1 + (transform γ a s).2),
      sq_nonneg (‖(transform γ a s).1‖ - ‖(transform γ a s).2‖)]
  rw [transform_add, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hsum
  exact hsum

/-- When coupled velocities initially coincide, only the position difference
contributes to the initial transformed energy. -/
theorem transformEnergy_zero_velocity (γ a : ℝ) (x : E) :
    transformEnergy γ a (0, x) = ((γ - a) ^ 2 + a ^ 2) * ‖x‖ ^ 2 := by
  simp only [transformEnergy, transform, zero_add, neg_zero, zero_sub,
    norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- For the parameter `a=0`, velocity projection has operator norm one. -/
theorem velocity_sq_le_energy (γ : ℝ) (s : E × E) :
    ‖s.1‖ ^ 2 ≤ transformEnergy γ 0 s := by
  simp only [transformEnergy, transform, sub_zero, zero_smul, norm_neg]
  nlinarith [sq_nonneg ‖s.1 + γ • s.2‖]

/-- A genuine norm-like Euclidean phase energy, without relying on the
maximum norm of the product type. -/
def phaseEnergy (s : E × E) : ℝ := ‖s.1‖ ^ 2 + ‖s.2‖ ^ 2

/-- The Euclidean transformed norm, implemented using mathlib's `WithLp 2`
product so that its triangle inequality is the actual Hilbert-space one. -/
def transformNorm (γ a : ℝ) (s : E × E) : ℝ :=
  ‖WithLp.toLp 2 (transform γ a s)‖

theorem transformNorm_nonneg (γ a : ℝ) (s : E × E) : 0 ≤ transformNorm γ a s :=
  norm_nonneg _

theorem transformNorm_sq (γ a : ℝ) (s : E × E) :
    transformNorm γ a s ^ 2 = transformEnergy γ a s := by
  exact WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (transform γ a s))

theorem transform_add_states (γ a : ℝ) (s t : E × E) :
    transform γ a (s + t) = transform γ a s + transform γ a t := by
  ext <;> simp only [transform, Prod.fst_add, Prod.snd_add] <;> module

theorem transformNorm_add_le (γ a : ℝ) (s t : E × E) :
    transformNorm γ a (s + t) ≤ transformNorm γ a s + transformNorm γ a t := by
  unfold transformNorm
  rw [transform_add_states, WithLp.toLp_add]
  exact norm_add_le _ _

theorem transformNorm_sub_triangle (γ a : ℝ) (s r t : E × E) :
    transformNorm γ a (s - t) ≤ transformNorm γ a (s - r) + transformNorm γ a (r - t) := by
  have he : s - t = (s - r) + (r - t) := by abel
  rw [he]
  exact transformNorm_add_le γ a _ _

theorem transformNorm_le_of_energy_le (γ a B : ℝ) (s : E × E) (hB : 0 ≤ B)
    (he : transformEnergy γ a s ≤ B ^ 2) : transformNorm γ a s ≤ B := by
  apply (sq_le_sq₀ (transformNorm_nonneg γ a s) hB).mp
  rw [transformNorm_sq]
  exact he

theorem velocity_le_transformNorm (γ : ℝ) (s : E × E) : ‖s.1‖ ≤ transformNorm γ 0 s := by
  apply (sq_le_sq₀ (norm_nonneg _) (transformNorm_nonneg γ 0 s)).mp
  rw [transformNorm_sq]
  exact velocity_sq_le_energy γ s

/-- The position projection of transformed norm has exactly the factor
`√2/γ` used only once at the final law comparison. -/
theorem position_le_transformNorm (γ : ℝ) (hγ : 0 < γ) (s : E × E) :
    ‖s.2‖ ≤ Real.sqrt 2 / γ * transformNorm γ 0 s := by
  have hs := position_sq_le_energy γ 0 s
  simp only [mul_zero, sub_zero, ← transformNorm_sq] at hs
  have hnorm : γ * ‖s.2‖ ≤ Real.sqrt 2 * transformNorm γ 0 s := by
    apply (sq_le_sq₀ (mul_nonneg hγ.le (norm_nonneg _)) (by
      exact mul_nonneg (Real.sqrt_nonneg _) (transformNorm_nonneg _ _ _))).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact hs
  have hdiv := (le_div_iff₀ hγ).mpr (show ‖s.2‖ * γ ≤ Real.sqrt 2 * transformNorm γ 0 s by nlinarith)
  convert hdiv using 1 <;> ring

/-- Equal velocity differences identify the initial transformed norm. -/
theorem transformNorm_zero_velocity (γ : ℝ) (hγ : 0 ≤ γ) (x : E) :
    transformNorm γ 0 (0, x) = γ * ‖x‖ := by
  apply (sq_eq_sq₀ (transformNorm_nonneg _ _ _) (mul_nonneg hγ (norm_nonneg _))).mp
  rw [transformNorm_sq, transformEnergy_zero_velocity]
  simp [mul_pow]

end KineticLangevin
