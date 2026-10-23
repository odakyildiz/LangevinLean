import KIPLMC.Exponential
import KIPLMC.Splitting

/-! # Exact time and velocity conjugacies

The physical-time implementation can alternatively be expressed at unit
temperature by changing the velocity and the clock. These algebraic identities
are the deterministic part of Appendix B; Gaussian covariance and Brownian
scaling are distinct probability assertions.
-/

noncomputable section
set_option linter.style.header false
namespace KIPLMC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Change the velocity scale without changing position. -/
def rescaleVelocity (c : ℝ) (z : E × E) : E × E := (c • z.1, z.2)

theorem rescaleVelocity_inverse (c : ℝ) (hc : c ≠ 0) (z : E × E) :
    rescaleVelocity c⁻¹ (rescaleVelocity c z) = z := by
  simp [rescaleVelocity, smul_smul, inv_mul_cancel₀ hc]

/-- Changing the kinetic clock by `c` changes the force by `1/c²`.
Innovations are additive here, so the theorem records their exact rescaling. -/
theorem exponentialStep_conjugate (g : E → E) (c γ h : ℝ) (hc : c ≠ 0)
    (z noise : E × E) :
    KineticLangevin.exponentialStep g (c * γ) (h / c)
        (rescaleVelocity c z) (rescaleVelocity c noise) =
      rescaleVelocity c (KineticLangevin.exponentialStep
        (fun x ↦ (c ^ 2)⁻¹ • g x) γ h z noise) := by
  have h1 : KineticLangevin.psi γ 1 h / c * c = KineticLangevin.psi γ 1 h := by
    field_simp
  have h2 : c * (KineticLangevin.psi γ 1 h * (c ^ 2)⁻¹) =
      KineticLangevin.psi γ 1 h / c := by field_simp
  simp only [KineticLangevin.exponentialStep, rescaleVelocity]
  rw [KineticLangevin.psi_scale_div c γ h hc 0,
    KineticLangevin.psi_scale_div c γ h hc 1,
    KineticLangevin.psi_scale_div c γ h hc 2]
  ext <;> simp only [pow_zero, div_one, pow_one, smul_add, smul_sub,
    smul_smul, h1, h2, div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hc,
    mul_inv_cancel₀ hc, mul_one] <;> module

/-- The damping depends only on the product friction times step. -/
theorem obaboDamping_scaled (c γ h : ℝ) (hc : c ≠ 0) :
    KineticLangevin.obaboDamping (c * γ) (h / c) =
      KineticLangevin.obaboDamping γ h := by
  unfold KineticLangevin.obaboDamping
  congr 1
  field_simp

/-- The standard particle rescaling has `c²=N`, precisely the factor needed
to identify its physical-time force with the force of the sum potential. -/
theorem inverse_sqrt_sq (N : ℕ) : ((Real.sqrt N) ^ 2)⁻¹ = (N : ℝ)⁻¹ := by
  rw [Real.sq_sqrt (Nat.cast_nonneg N)]

end KIPLMC
