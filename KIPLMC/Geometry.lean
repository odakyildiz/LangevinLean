import IPLA.Geometry
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Kinetic particle geometry

The scaled position is `(θ,x¹/√N,…,xᴺ/√N)`. In physical time the
correspondingly scaled velocity uses the same transformation. The force is
`∇V_N/N`, and the velocity temperature is `1/N`. This representation avoids a
time change and permits direct reuse of kinetic Langevin integrators.
-/

noncomputable section
set_option linter.style.header false
open scoped NNReal
namespace KIPLMC

/-- The same scaled particle geometry already used by IPLA. -/
abbrev State := IPLA.State

/-- The averaged potential `bar U_N` in Appendix A. -/
def averagePotential {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ)
    (z : State N dθ dx) : ℝ := (N : ℝ)⁻¹ * IPLA.potential U z

/-- The physical-time force in scaled coordinates. -/
def force {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ)
    (z : State N dθ dx) : State N dθ dx :=
  (N : ℝ)⁻¹ • gradient (@IPLA.potential N dθ dx U) z

/-- The scaled force is the actual gradient of the averaged potential. -/
theorem gradient_averagePotential {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    (hdiff : Differentiable ℝ U) (z : State N dθ dx) :
    gradient (@averagePotential N dθ dx U) z = force U z := by
  apply ext_inner_right ℝ
  intro w
  rw [inner_gradient_left]
  have hd := (IPLA.potential_differentiable (N := N) hdiff z).hasFDerivAt.const_mul (N : ℝ)⁻¹
  change HasFDerivAt (@averagePotential N dθ dx U) _ z at hd
  rw [hd.fderiv]
  simp [force, inner_smul_left, inner_gradient_left]

/-- The original sum potential is `N` times its average. -/
theorem potential_eq_mul_average {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (z : State N dθ dx) :
    IPLA.potential U z = (N : ℝ) * averagePotential U z := by
  simp [averagePotential, ← mul_assoc, Nat.cast_ne_zero.mpr hN.ne']

/-- Averaging the lifted strong convexity cancels its factor `N`. -/
theorem averagePotential_strongConvex {N dθ dx : ℕ} (hN : 0 < N)
    {U : IPLA.Joint dθ dx → ℝ} {m : ℝ}
    (hU : StrongConvexOn Set.univ m U) :
    StrongConvexOn Set.univ m (@averagePotential N dθ dx U) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hs := (IPLA.potential_strongConvex (N := N) hU).2 hx hy ha hb hab
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
  convert hi using 1 <;> dsimp only [averagePotential] <;>
    simp only [smul_eq_mul] <;> field_simp <;> ring

/-- The parameter acceleration is the average of the pair gradients. -/
theorem force_parameter {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    (hdiff : Differentiable ℝ U) (z : State N dθ dx) (j : Fin dθ) :
    force U z (Sum.inl j) = (N : ℝ)⁻¹ *
      ∑ i : Fin N, gradient U (IPLA.joint i z) (Sum.inl j) := by
  simp [force, IPLA.gradient_potential_parameter hdiff]

/-- Unscaling the latent acceleration recovers the unaveraged pair gradient. -/
theorem force_particle {N dθ dx : ℕ} (hN : 0 < N)
    {U : IPLA.Joint dθ dx → ℝ} (hdiff : Differentiable ℝ U)
    (z : State N dθ dx) (i : Fin N) (j : Fin dx) :
    Real.sqrt N * force U z (Sum.inr (i,j)) =
      gradient U (IPLA.joint i z) (Sum.inr j) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [force, PiLp.smul_apply, smul_eq_mul, IPLA.gradient_potential_particle hdiff]
  calc
    _ = ((Real.sqrt N) ^ 2 * (N : ℝ)⁻¹) *
      gradient U (IPLA.joint i z) (Sum.inr j) := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N), mul_inv_cancel₀ hn, one_mul]

/-- Smoothness also cancels its factor `N`, so this physical-time force has
the original pair smoothness constant independently of particle count. -/
theorem force_lipschitz {N dθ dx : ℕ} (hN : 0 < N)
    {U : IPLA.Joint dθ dx → ℝ} {L : ℝ≥0}
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) :
    LipschitzWith L (@force N dθ dx U) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := (IPLA.potential_gradient_lipschitz (N := N) hdiff hLip).norm_sub_le x y
  rw [dist_eq_norm, dist_eq_norm]
  simp only [force, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ((((N : ℝ≥0) * L : ℝ≥0) : ℝ) * ‖x-y‖) :=
      mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hn.le)
    _ = _ := by
      simp only [NNReal.coe_mul, NNReal.coe_natCast]
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]

end KIPLMC
