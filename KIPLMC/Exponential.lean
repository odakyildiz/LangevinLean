import KIPLMC.Geometry
import KineticLangevin.Integrator

/-! # KIPLMC1 reuses the exponential integrator

There is one implementation of exponential Euler: the shared kinetic map.
KIPLMC1 supplies its scaled particle force and its temperature `1/N`.
The coordinate theorems recover Algorithm 1 without postulating equivalence.
-/

noncomputable section
set_option linter.style.header false
namespace KIPLMC

/-- The physical-time kinetic particle noise amplitude in scaled coordinates. -/
def kineticAmplitude (N : ℕ) (γ : ℝ) : ℝ := Real.sqrt (2 * γ / N)

/-- KIPLMC1 is the shared exponential integrator, with the scaled force and
the physical-time, correlated Gaussian innovation supplied by the caller. -/
def kiplmc1Step {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z noise : State N dθ dx × State N dθ dx) :=
  KineticLangevin.exponentialStep (force U) γ h z (kineticAmplitude N γ • noise)

/-- Its parameter velocity update contains the mean parameter gradient. -/
theorem kiplmc1Step_parameter_velocity {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    (hdiff : Differentiable ℝ U) (γ h : ℝ)
    (z noise : State N dθ dx × State N dθ dx) (j : Fin dθ) :
    (kiplmc1Step U γ h z noise).1 (Sum.inl j) =
      KineticLangevin.psi γ 0 h * z.1 (Sum.inl j) -
      (KineticLangevin.psi γ 1 h / N) *
        ∑ i : Fin N, gradient U (IPLA.joint i z.2) (Sum.inl j) +
      kineticAmplitude N γ * noise.1 (Sum.inl j) := by
  simp [kiplmc1Step, KineticLangevin.exponentialStep, force_parameter hdiff,
    div_eq_mul_inv, mul_assoc]

/-- Its parameter position update uses the same mean force and the correlated
position innovation, which is distinct from the velocity innovation. -/
theorem kiplmc1Step_parameter_position {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    (hdiff : Differentiable ℝ U) (γ h : ℝ)
    (z noise : State N dθ dx × State N dθ dx) (j : Fin dθ) :
    (kiplmc1Step U γ h z noise).2 (Sum.inl j) =
      z.2 (Sum.inl j) + KineticLangevin.psi γ 1 h * z.1 (Sum.inl j) -
      (KineticLangevin.psi γ 2 h / N) *
        ∑ i : Fin N, gradient U (IPLA.joint i z.2) (Sum.inl j) +
      kineticAmplitude N γ * noise.2 (Sum.inl j) := by
  simp [kiplmc1Step, KineticLangevin.exponentialStep, force_parameter hdiff,
    div_eq_mul_inv, mul_assoc]

theorem unscale_kineticAmplitude {N : ℕ} (hN : 0 < N) (γ : ℝ) :
    Real.sqrt N * kineticAmplitude N γ = Real.sqrt (2 * γ) := by
  rw [kineticAmplitude, ← Real.sqrt_mul (Nat.cast_nonneg N)]
  congr 1
  field_simp

/-- The latent velocity update has the unaveraged force and unit-temperature
noise after undoing the scaled coordinates. -/
theorem kiplmc1Step_particle_velocity {N dθ dx : ℕ} (hN : 0 < N)
    {U : IPLA.Joint dθ dx → ℝ} (hdiff : Differentiable ℝ U) (γ h : ℝ)
    (z noise : State N dθ dx × State N dθ dx) (i : Fin N) (j : Fin dx) :
    Real.sqrt N * (kiplmc1Step U γ h z noise).1 (Sum.inr (i,j)) =
      KineticLangevin.psi γ 0 h * (Real.sqrt N * z.1 (Sum.inr (i,j))) -
      KineticLangevin.psi γ 1 h * gradient U (IPLA.joint i z.2) (Sum.inr j) +
      Real.sqrt (2 * γ) * noise.1 (Sum.inr (i,j)) := by
  simp only [kiplmc1Step, KineticLangevin.exponentialStep,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Prod.smul_fst, smul_eq_mul,
    mul_add, mul_sub]
  rw [mul_left_comm (Real.sqrt N) (KineticLangevin.psi γ 1 h), force_particle hN hdiff]
  rw [← mul_assoc (Real.sqrt N) (kineticAmplitude N γ), unscale_kineticAmplitude hN]
  ring

/-- The latent position update uses `ψ₂` for the same unaveraged force. -/
theorem kiplmc1Step_particle_position {N dθ dx : ℕ} (hN : 0 < N)
    {U : IPLA.Joint dθ dx → ℝ} (hdiff : Differentiable ℝ U) (γ h : ℝ)
    (z noise : State N dθ dx × State N dθ dx) (i : Fin N) (j : Fin dx) :
    Real.sqrt N * (kiplmc1Step U γ h z noise).2 (Sum.inr (i,j)) =
      Real.sqrt N * z.2 (Sum.inr (i,j)) +
      KineticLangevin.psi γ 1 h * (Real.sqrt N * z.1 (Sum.inr (i,j))) -
      KineticLangevin.psi γ 2 h * gradient U (IPLA.joint i z.2) (Sum.inr j) +
      Real.sqrt (2 * γ) * noise.2 (Sum.inr (i,j)) := by
  simp only [kiplmc1Step, KineticLangevin.exponentialStep,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, Prod.smul_snd, smul_eq_mul,
    mul_add, mul_sub]
  rw [mul_left_comm (Real.sqrt N) (KineticLangevin.psi γ 2 h), force_particle hN hdiff]
  rw [← mul_assoc (Real.sqrt N) (kineticAmplitude N γ), unscale_kineticAmplitude hN]
  ring

/-- The actual inhomogeneous KIPLMC1 trajectory driven by prescribed innovations. -/
def kiplmc1Chain {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx)
    (noise : ℕ → State N dθ dx × State N dθ dx) : ℕ → State N dθ dx × State N dθ dx
  | 0 => z
  | n + 1 => kiplmc1Step U γ h (kiplmc1Chain U γ h z noise n) (noise n)

end KIPLMC
