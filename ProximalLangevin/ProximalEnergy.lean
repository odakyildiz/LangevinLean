import ProximalLangevin.Proximal

set_option linter.style.header false

/-!
# The nonsmooth proximal energy inequality

This is the deterministic inequality used in Lemma A.8 of arXiv:2406.14292v3.
Any genuine subgradient at the input suffices. A bound on its squared norm
then gives the constant in assumption C1; no convergence or energy estimate
is supplied as an assumption.
-/

open Set
open scoped RealInnerProductSpace

namespace ProximalLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proximity decreases squared distance and nonsmooth energy, up to the
squared norm of any subgradient at the input point. -/
theorem isProxPoint_energy_le {f : E → ℝ} (hf : ConvexOn ℝ univ f)
    {η : ℝ} (hη : 0 < η) {x p s : E}
    (hp : IsProxPoint f η x p) (hs : IsSubgradient f x s) (a : E) :
    ‖p - a‖ ^ 2 ≤ ‖x - a‖ ^ 2 - 2 * η * (f x - f a) + η ^ 2 * ‖s‖ ^ 2 := by
  have hres := subgradient_of_isProxPoint hf hη hp a
  have hneg : a - p = -(p - a) := by abel
  simp only [real_inner_smul_left, hneg, inner_neg_right] at hres
  have hscaled := mul_le_mul_of_nonneg_left hres hη.le
  have hinv : η * η⁻¹ = 1 := mul_inv_cancel₀ hη.ne'
  simp only [mul_add, mul_neg, ← mul_assoc, hinv, one_mul] at hscaled
  have hsub := hs p
  rw [show p - x = -(x - p) by abel, inner_neg_right] at hsub
  have hdist : ‖x - a‖ ^ 2 = ‖x - p‖ ^ 2 + 2 * ⟪x - p, p - a⟫ +
      ‖p - a‖ ^ 2 := by
    rw [show x - a = (x - p) + (p - a) by abel, norm_add_sq_real]
  have hyoung := sq_nonneg ‖(x - p) - η • s‖
  rw [norm_sub_sq_real] at hyoung
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hη, real_inner_smul_right] at hyoung
  rw [real_inner_comm s (x - p)] at hyoung
  nlinarith [mul_le_mul_of_nonneg_left hsub hη.le]

/-- The deterministic nonsmooth energy estimate for the actual chosen
minimizer of the proximal objective. -/
theorem prox_energy_le [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hb : ∃ b : ℝ, ∀ z, b ≤ f z)
    {η : ℝ} (hη : 0 < η) {x s : E} (hs : IsSubgradient f x s) (a : E) :
    ‖prox f η x - a‖ ^ 2 ≤
      ‖x - a‖ ^ 2 - 2 * η * (f x - f a) + η ^ 2 * ‖s‖ ^ 2 :=
  isProxPoint_energy_le hf hη (prox_isProxPoint hf hb hη x) hs a

/-- A squared-subgradient bound supplies the forcing term in Lemma A.8. -/
theorem prox_energy_le_of_subgradient_bound [FiniteDimensional ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hb : ∃ b : ℝ, ∀ z, b ≤ f z)
    {η : ℝ} (hη : 0 < η) {x s : E} (hs : IsSubgradient f x s)
    {C : ℝ} (hC : ‖s‖ ^ 2 ≤ C) (a : E) :
    ‖prox f η x - a‖ ^ 2 ≤
      ‖x - a‖ ^ 2 - 2 * η * (f x - f a) + η ^ 2 * C := by
  exact (prox_energy_le hf hb hη hs a).trans (by gcongr)

end ProximalLangevin
