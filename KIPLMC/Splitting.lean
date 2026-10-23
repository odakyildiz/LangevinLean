import KIPLMC.Geometry
import KineticLangevin.OBABO

/-! # KIPLMC2 as OBABO

In scaled coordinates every velocity thermostat has variance `1/N`.
The parameter coordinates are unchanged; multiplying a latent coordinate by
`sqrt N` recovers the unit-temperature latent thermostat of Algorithm 2.
-/

noncomputable section
set_option linter.style.header false
namespace KIPLMC

/-- Half-step thermal amplitude in the scaled particle geometry. -/
def thermalAmplitude (N : ℕ) (γ h : ℝ) : ℝ :=
  Real.sqrt (KineticLangevin.obaboVariance γ h / N)

/-- Algorithm 2, using the already formalized O-B-A-B-O composition. -/
def kiplmc2Step {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx) (ξ ξ' : State N dθ dx) :=
  KineticLangevin.obaboStep (force U) h (KineticLangevin.obaboDamping γ h)
    (thermalAmplitude N γ h) z ξ ξ'

/-- The intermediate half velocity in Algorithm 2. -/
def halfVelocity {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx) (ξ : State N dθ dx) : State N dθ dx :=
  KineticLangevin.obaboDamping γ h • z.1 + thermalAmplitude N γ h • ξ -
    (h / 2) • force U z.2

/-- The A substep updates the position with the newly computed half velocity. -/
theorem kiplmc2Step_position {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx) (ξ ξ' : State N dθ dx) :
    (kiplmc2Step U γ h z ξ ξ').2 = z.2 + h • halfVelocity U γ h z ξ := rfl

/-- The second B substep uses the gradient at the new position. -/
theorem kiplmc2Step_velocity {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx) (ξ ξ' : State N dθ dx) :
    (kiplmc2Step U γ h z ξ ξ').1 = KineticLangevin.obaboDamping γ h •
      (halfVelocity U γ h z ξ - (h / 2) •
        force U (z.2 + h • halfVelocity U γ h z ξ)) + thermalAmplitude N γ h • ξ' := rfl

/-- The first parameter O+B update is the average-gradient update in the paper. -/
theorem halfVelocity_parameter {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    (hdiff : Differentiable ℝ U) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx) (ξ : State N dθ dx) (j : Fin dθ) :
    halfVelocity U γ h z ξ (Sum.inl j) =
      KineticLangevin.obaboDamping γ h * z.1 (Sum.inl j) +
      thermalAmplitude N γ h * ξ (Sum.inl j) -
      h / (2 * N) * ∑ i : Fin N, gradient U (IPLA.joint i z.2) (Sum.inl j) := by
  simp only [halfVelocity, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul, force_parameter hdiff]
  ring

/-- Unscaling the thermostat coefficient recovers the latent amplitude. -/
theorem unscale_thermalAmplitude {N : ℕ} (hN : 0 < N) (γ h : ℝ) :
    Real.sqrt N * thermalAmplitude N γ h =
      Real.sqrt (KineticLangevin.obaboVariance γ h) := by
  rw [thermalAmplitude, ← Real.sqrt_mul (Nat.cast_nonneg N)]
  congr 1
  field_simp

/-- The first latent O+B update is exactly the unaveraged latent force. -/
theorem halfVelocity_particle {N dθ dx : ℕ} (hN : 0 < N)
    {U : IPLA.Joint dθ dx → ℝ} (hdiff : Differentiable ℝ U) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx) (ξ : State N dθ dx)
    (i : Fin N) (j : Fin dx) :
    Real.sqrt N * halfVelocity U γ h z ξ (Sum.inr (i,j)) =
      KineticLangevin.obaboDamping γ h * (Real.sqrt N * z.1 (Sum.inr (i,j))) +
      Real.sqrt (KineticLangevin.obaboVariance γ h) * ξ (Sum.inr (i,j)) -
      (h / 2) * gradient U (IPLA.joint i z.2) (Sum.inr j) := by
  simp only [halfVelocity, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    mul_sub, mul_add]
  rw [← mul_assoc (Real.sqrt N) (thermalAmplitude N γ h), unscale_thermalAmplitude hN]
  rw [mul_left_comm (Real.sqrt N) (h / 2), force_particle hN hdiff]
  ring

/-- The A step in the common parameter coordinates. -/
theorem kiplmc2Step_parameter_position {N dθ dx : ℕ}
    (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx) (ξ ξ' : State N dθ dx) (j : Fin dθ) :
    (kiplmc2Step U γ h z ξ ξ').2 (Sum.inl j) =
      z.2 (Sum.inl j) + h * halfVelocity U γ h z ξ (Sum.inl j) := rfl

/-- Physical latent positions drift by their physical half velocities. -/
theorem kiplmc2Step_particle_position {N dθ dx : ℕ}
    (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx) (ξ ξ' : State N dθ dx)
    (i : Fin N) (j : Fin dx) :
    Real.sqrt N * (kiplmc2Step U γ h z ξ ξ').2 (Sum.inr (i,j)) =
      Real.sqrt N * z.2 (Sum.inr (i,j)) +
      h * (Real.sqrt N * halfVelocity U γ h z ξ (Sum.inr (i,j))) := by
  rw [kiplmc2Step_position]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end KIPLMC
