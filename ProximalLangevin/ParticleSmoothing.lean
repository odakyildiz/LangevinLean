import ProximalLangevin.SplittingCoupling
import ProximalLangevin.MYIPLA

set_option linter.style.header false

/-!
# Uniform approximation and bounded gradients in the actual particle coordinates

The lifted sum has Lipschitz constant `N*K`, and its Moreau approximation has
the same constant. These estimates do not use the inverse smoothing scale.
They supply the quantitative inputs for the actual splitting coupling.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal BigOperators
namespace ProximalLangevin

/-- Lifting a globally Lipschitz pair potential to the scaled state multiplies
its Lipschitz constant by the number of particles. -/
theorem potential_lipschitz {N dθ dx : ℕ} (hN : 0 < N)
    {g : IPLA.Joint dθ dx → ℝ} {K : ℝ≥0} (hK : LipschitzWith K g) :
    LipschitzWith ((N : ℝ≥0) * K) (@IPLA.potential N dθ dx g) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hav := averagedPotential_lipschitz (N := N) hN hK
  apply LipschitzWith.of_dist_le_mul
  intro z w
  have hh := hav.dist_le_mul z w
  rw [Real.dist_eq] at hh ⊢
  have heq : IPLA.potential g z - IPLA.potential g w =
      (N : ℝ) * (averagedPotential g z - averagedPotential g w) := by
    dsimp [averagedPotential]
    field_simp
  rw [heq, abs_mul, abs_of_pos hn]
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, mul_assoc] using
    mul_le_mul_of_nonneg_left hh hn.le

/-- The lifted true Moreau approximation preserves the particle Lipschitz
constant, uniformly over positive smoothing scales. -/
theorem potential_moreau_lipschitz {N dθ dx : ℕ} (hN : 0 < N)
    {g : IPLA.Joint dθ dx → ℝ} (hg : ConvexOn ℝ univ g)
    (hb : ∃ b, ∀ x, b ≤ g x) {η : ℝ} (hη : 0 < η)
    {K : ℝ≥0} (hK : LipschitzWith K g) :
    LipschitzWith ((N : ℝ≥0) * K) (@IPLA.potential N dθ dx (moreau g η)) :=
  potential_lipschitz hN (moreau_lipschitz_of_lipschitz hg hb hη hK)

/-- The actual gradient of the lifted Moreau term is bounded by `N*K`,
independently of the smoothing scale. -/
theorem potential_moreau_gradient_norm_le {N dθ dx : ℕ} (hN : 0 < N)
    {g : IPLA.Joint dθ dx → ℝ} (hg : ConvexOn ℝ univ g)
    (hb : ∃ b, ∀ x, b ≤ g x) {η : ℝ} (hη : 0 < η)
    {K : ℝ≥0} (hK : LipschitzWith K g) (z : IPLA.State N dθ dx) :
    ‖gradient (IPLA.potential (moreau g η)) z‖ ≤ (N : ℝ) * (K : ℝ) := by
  simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
    gradient_norm_le_of_lipschitz (potential_moreau_lipschitz hN hg hb hη hK) z

/-- The finite one-sided Moreau gap for the actual sum over particles. -/
theorem potential_moreau_gap {N dθ dx : ℕ}
    {g : IPLA.Joint dθ dx → ℝ} (hg : ConvexOn ℝ univ g)
    (hb : ∃ b, ∀ x, b ≤ g x) {η : ℝ} (hη : 0 < η)
    {K : ℝ≥0} (hK : LipschitzWith K g) (z : IPLA.State N dθ dx) :
    0 ≤ IPLA.potential g z - IPLA.potential (moreau g η) z ∧
      IPLA.potential g z - IPLA.potential (moreau g η) z ≤
        (N : ℝ) * η * (K : ℝ) ^ 2 / 2 := by
  have heq : IPLA.potential g z - IPLA.potential (moreau g η) z =
      ∑ i : Fin N, (g (IPLA.joint i z) - moreau g η (IPLA.joint i z)) := by
    simp only [IPLA.potential, Finset.sum_sub_distrib]
  rw [heq]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (moreau_gap_of_lipschitz hg hb hη hK _).1)
  · calc
      _ ≤ ∑ _i : Fin N, η * (K : ℝ) ^ 2 / 2 :=
        Finset.sum_le_sum (fun i _ => (moreau_gap_of_lipschitz hg hb hη hK _).2)
      _ = _ := by simp; ring

/-- Lifting commutes with the smooth-plus-Moreau decomposition. -/
theorem potential_smoothed_decomposition {N dθ dx : ℕ}
    (g₁ g₂ : IPLA.Joint dθ dx → ℝ) (η : ℝ) :
    @IPLA.potential N dθ dx (smoothedPotential g₁ g₂ η) =
      fun z => IPLA.potential g₁ z + IPLA.potential (moreau g₂ η) z := by
  funext z
  simp only [IPLA.potential, smoothedPotential, Finset.sum_add_distrib]

end ProximalLangevin
