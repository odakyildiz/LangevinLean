import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-! # The OBABO integrator

The phase-space convention throughout this library is `(velocity, position)`.
The two independent Gaussian vectors enter the two O half-steps separately.
All identities in this file are pathwise identities; distributional assertions
about the inputs belong to the probability layer.
-/

noncomputable section
set_option linter.style.header false
namespace KineticLangevin
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Ornstein--Uhlenbeck velocity substep, with damping `δ` and supplied noise. -/
def ornsteinStep (δ σ : ℝ) (ξ : E) (z : E × E) : E × E :=
  (δ • z.1 + σ • ξ, z.2)

/-- Momentum kick over an interval of length `h`. -/
def kickStep (force : E → E) (h : ℝ) (z : E × E) : E × E :=
  (z.1 - h • force z.2, z.2)

/-- Position drift over an interval of length `h`. -/
def driftStep (h : ℝ) (z : E × E) : E × E :=
  (z.1, z.2 + h • z.1)

/-- O-B-A-B-O with independent noise arguments for its O half-steps.
`σ` is the half-step velocity noise coefficient; for inverse mass `u` it is
`sqrt (u * (1 - exp (-γ*h)))`. -/
def obaboStep (force : E → E) (h δ σ : ℝ) (z : E × E)
    (ξ ξ' : E) : E × E :=
  ornsteinStep δ σ ξ'
    (kickStep force (h / 2)
      (driftStep h (kickStep force (h / 2) (ornsteinStep δ σ ξ z))))

/-- The three intermediate stages are exactly the familiar velocity-Verlet
form, bracketed by the two thermostat updates. -/
theorem obaboStep_expanded (force : E → E) (h δ σ : ℝ) (z : E × E)
    (ξ ξ' : E) :
    obaboStep force h δ σ z ξ ξ' =
      let vhalf := δ • z.1 + σ • ξ - (h / 2) • force z.2
      let xnext := z.2 + h • vhalf
      (δ • (vhalf - (h / 2) • force xnext) + σ • ξ', xnext) := rfl

@[simp] theorem kickStep_neg (force : E → E) (h : ℝ) (z : E × E) :
    kickStep force (-h) (kickStep force h z) = z := by
  ext <;> simp [kickStep]

@[simp] theorem driftStep_neg (h : ℝ) (z : E × E) :
    driftStep (-h) (driftStep h z) = z := by
  ext <;> simp [driftStep]

/-- Reversing the velocity conjugates a Hamiltonian kick to its inverse. -/
def reverseVelocity (z : E × E) : E × E := (-z.1, z.2)

omit [Module ℝ E] in
@[simp] theorem reverseVelocity_twice (z : E × E) :
    reverseVelocity (reverseVelocity z) = z := by simp [reverseVelocity]

theorem reverseVelocity_kick (force : E → E) (h : ℝ) (z : E × E) :
    reverseVelocity (kickStep force h (reverseVelocity z)) =
      kickStep force (-h) z := by
  ext <;> simp [reverseVelocity, kickStep, add_comm]

theorem reverseVelocity_drift (h : ℝ) (z : E × E) :
    reverseVelocity (driftStep h (reverseVelocity z)) = driftStep (-h) z := by
  ext <;> simp [reverseVelocity, driftStep]

/-- The Hamiltonian part is reversible because its kick-drift-kick composition
is palindromic. This is an exact algebraic statement, not a convergence rate. -/
def verletStep (force : E → E) (h : ℝ) (z : E × E) : E × E :=
  kickStep force (h / 2) (driftStep h (kickStep force (h / 2) z))

theorem verletStep_neg (force : E → E) (h : ℝ) (z : E × E) :
    verletStep force (-h) (verletStep force h z) = z := by
  simp only [verletStep, neg_div]
  rw [kickStep_neg, driftStep_neg, kickStep_neg]

theorem obaboStep_zero (force : E → E) (z : E × E) (ξ ξ' : E) :
    obaboStep force 0 1 0 z ξ ξ' = z := by
  simp [obaboStep, ornsteinStep, kickStep, driftStep]

/-- A synchronous coupling cancels both additive thermostat noises exactly.
The new position must be used in the second kick, even in this difference
identity. -/
theorem obaboStep_synchronous (force : E → E) (h δ σ : ℝ)
    (z w : E × E) (ξ ξ' : E) :
    let a := δ • (z.1 - w.1) - (h / 2) • (force z.2 - force w.2)
    let x := z.2 + h • (δ • z.1 + σ • ξ - (h / 2) • force z.2)
    let y := w.2 + h • (δ • w.1 + σ • ξ - (h / 2) • force w.2)
    (obaboStep force h δ σ z ξ ξ').1 - (obaboStep force h δ σ w ξ ξ').1 =
      δ • (a - (h / 2) • (force x - force y)) ∧
    (obaboStep force h δ σ z ξ ξ').2 - (obaboStep force h δ σ w ξ ξ').2 =
      z.2 - w.2 + h • a := by
  dsimp [obaboStep, ornsteinStep, kickStep, driftStep]
  constructor <;> module

/-- The standard O half-step damping. -/
def obaboDamping (γ h : ℝ) : ℝ := Real.exp (-γ * h / 2)

/-- Half-step variance for a standard-mass velocity thermostat. -/
def obaboVariance (γ h : ℝ) : ℝ := 1 - obaboDamping γ h ^ 2

theorem obaboDamping_pos (γ h : ℝ) : 0 < obaboDamping γ h := Real.exp_pos _

theorem obaboDamping_sq (γ h : ℝ) : obaboDamping γ h ^ 2 = Real.exp (-γ * h) := by
  rw [obaboDamping, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem obaboVariance_nonneg {γ h : ℝ} (hγ : 0 ≤ γ) (hh : 0 ≤ h) :
    0 ≤ obaboVariance γ h := by
  rw [obaboVariance, obaboDamping_sq]
  exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hγ) hh))

/-- Damping and thermal noise preserve the scalar velocity variance exactly. -/
theorem obabo_thermostat_variance {γ h u : ℝ} (hγ : 0 ≤ γ) (hh : 0 ≤ h)
    (hu : 0 ≤ u) :
    obaboDamping γ h ^ 2 * u + Real.sqrt (u * obaboVariance γ h) ^ 2 = u := by
  rw [Real.sq_sqrt (mul_nonneg hu (obaboVariance_nonneg hγ hh))]
  dsimp [obaboVariance]
  ring

end KineticLangevin
