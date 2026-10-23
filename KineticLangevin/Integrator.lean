import KineticLangevin.Coefficients
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# First- and second-order kinetic Langevin updates

States are ordered `(velocity, position)`, as in the paper. The force argument
is a vector field; in the paper it is the gradient of the potential. Keeping
the force explicit permits reuse with a non-unit inverse mass. Innovations
are supplied explicitly, separating the deterministic map from the joint
Gaussian law with covariance defined in `Coefficients`.
-/

noncomputable section

namespace KineticLangevin

/-- A phase state, velocity first and position second. -/
abbrev PhaseSpace (E : Type*) := E × E

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact velocity response when the force is held constant. -/
def frozenVelocity (γ : ℝ) (v force : E) (t : ℝ) : E :=
  psi γ 0 t • v - psi γ 1 t • force

/-- Exact position response when the force is held constant. -/
def frozenPosition (γ : ℝ) (x v force : E) (t : ℝ) : E :=
  x + psi γ 1 t • v - psi γ 2 t • force

theorem hasDerivAt_frozenPosition (γ : ℝ) (x v force : E) (t : ℝ) :
    HasDerivAt (frozenPosition γ x v force) (frozenVelocity γ v force t) t := by
  change HasDerivAt (fun s => x + psi γ 1 s • v - psi γ 2 s • force)
    (psi γ 0 t • v - psi γ 1 t • force) t
  simpa only [zero_add, Pi.add_def, Pi.sub_def, Nat.reduceAdd] using ((hasDerivAt_const t x).add
    ((hasDerivAt_psi_succ γ t 0).smul_const v)).sub
      ((hasDerivAt_psi_succ γ t 1).smul_const force)

/-- The deterministic exponential update solves the damped velocity equation
exactly for the frozen force, including the zero-friction case. -/
theorem hasDerivAt_frozenVelocity (γ : ℝ) (v force : E) (t : ℝ) :
    HasDerivAt (frozenVelocity γ v force)
      (-γ • frozenVelocity γ v force t - force) t := by
  have hd := ((hasDerivAt_psi_zero γ t).smul_const v).sub
    ((hasDerivAt_psi_succ γ t 0).smul_const force)
  have he : -γ • frozenVelocity γ v force t - force =
      (-γ * psi γ 0 t) • v - psi γ 0 t • force := by
    dsimp only [frozenVelocity]
    simp only [smul_sub, smul_smul]
    rw [show -γ * psi γ 1 t = psi γ 0 t - 1 by
      linarith [friction_mul_psi_one γ t]]
    module
  rw [he]
  exact hd

/-- Exponential Euler with an explicitly supplied additive phase innovation. -/
def exponentialStep (force : E → E) (γ h : ℝ)
    (state noise : PhaseSpace E) : PhaseSpace E :=
  (psi γ 0 h • state.1 - psi γ 1 h • force state.2 + noise.1,
   state.2 + psi γ 1 h • state.1 - psi γ 2 h • force state.2 + noise.2)

theorem exponentialStep_eq_frozen (force : E → E) (γ h : ℝ)
    (state noise : PhaseSpace E) :
    exponentialStep force γ h state noise =
      (frozenVelocity γ state.1 (force state.2) h + noise.1,
       frozenPosition γ state.2 state.1 (force state.2) h + noise.2) := rfl

/-- The KLMC step of Dalalyan–Riou-Durand, equation (17).
The innovation has covariance `klmcCovariance γ h` in each spatial coordinate. -/
def klmcStep (force : E → E) (γ h : ℝ)
    (state noise : PhaseSpace E) : PhaseSpace E :=
  exponentialStep force γ h state (Real.sqrt (2 * γ) • noise)

@[simp] theorem exponentialStep_velocity (force : E → E) (γ h : ℝ)
    (state noise : PhaseSpace E) :
    (exponentialStep force γ h state noise).1 =
      psi γ 0 h • state.1 - psi γ 1 h • force state.2 + noise.1 := rfl

@[simp] theorem exponentialStep_position (force : E → E) (γ h : ℝ)
    (state noise : PhaseSpace E) :
    (exponentialStep force γ h state noise).2 =
      state.2 + psi γ 1 h • state.1 - psi γ 2 h • force state.2 + noise.2 := rfl

@[simp] theorem exponentialStep_zero (force : E → E) (γ : ℝ) (state : PhaseSpace E) :
    exponentialStep force γ 0 state 0 = state := by
  ext <;> simp [exponentialStep]

/-- The two synchronous copies use exactly the same innovation. Its contribution
therefore cancels before any norm or moment estimate is made. -/
theorem exponentialStep_sub (force : E → E) (γ h : ℝ)
    (state other noise : PhaseSpace E) :
    exponentialStep force γ h state noise - exponentialStep force γ h other noise =
      (psi γ 0 h • (state.1 - other.1) -
        psi γ 1 h • (force state.2 - force other.2),
       (state.2 - other.2) + psi γ 1 h • (state.1 - other.1) -
        psi γ 2 h • (force state.2 - force other.2)) := by
  ext <;> simp only [exponentialStep, Prod.fst_sub, Prod.snd_sub,
    smul_sub] <;> abel

theorem klmcStep_sub (force : E → E) (γ h : ℝ)
    (state other noise : PhaseSpace E) :
    klmcStep force γ h state noise - klmcStep force γ h other noise =
      (psi γ 0 h • (state.1 - other.1) -
        psi γ 1 h • (force state.2 - force other.2),
       (state.2 - other.2) + psi γ 1 h • (state.1 - other.1) -
        psi γ 2 h • (force state.2 - force other.2)) :=
  exponentialStep_sub force γ h state other _

/-- The local linear drift correction used by the second-order method. -/
def klmc2Step (force : E → E) (hessian : E → E →L[ℝ] E) (γ h : ℝ)
    (state : PhaseSpace E) (noise : Fin 4 → E) : PhaseSpace E :=
  (psi γ 0 h • state.1 - psi γ 1 h • force state.2 -
      phi γ 2 h • hessian state.2 state.1 +
      Real.sqrt (2 * γ) • (noise 0 - hessian state.2 (noise 2)),
   state.2 + psi γ 1 h • state.1 - psi γ 2 h • force state.2 -
      phi γ 3 h • hessian state.2 state.1 +
      Real.sqrt (2 * γ) • (noise 1 - hessian state.2 (noise 3)))

/-- With zero Hessian, the second-order update is exactly the first-order update.
The first two components of the four-dimensional innovation are retained. -/
theorem klmc2Step_zero_hessian (force : E → E) (γ h : ℝ)
    (state : PhaseSpace E) (noise : Fin 4 → E) :
    klmc2Step force (fun _ => 0) γ h state noise =
      klmcStep force γ h state (noise 0, noise 1) := by
  ext <;> simp [klmc2Step, klmcStep, exponentialStep]

/-- At zero friction, exponential Euler is the exact constant-acceleration
update, and the fluctuation-dissipation noise vanishes. -/
theorem klmcStep_zero_friction (force : E → E) (h : ℝ)
    (state noise : PhaseSpace E) :
    klmcStep force 0 h state noise =
      (state.1 - h • force state.2,
       state.2 + h • state.1 - (h ^ 2 / 2) • force state.2) := by
  ext <;> simp [klmcStep, exponentialStep]

/-- The inhomogeneous numerical trajectory driven by a prescribed noise stream. -/
def klmcChain (force : E → E) (γ h : ℝ) (initial : PhaseSpace E)
    (noise : ℕ → PhaseSpace E) : ℕ → PhaseSpace E
  | 0 => initial
  | k + 1 => klmcStep force γ h (klmcChain force γ h initial noise k) (noise k)

@[simp] theorem klmcChain_zero (force : E → E) (γ h : ℝ)
    (initial : PhaseSpace E) (noise : ℕ → PhaseSpace E) :
    klmcChain force γ h initial noise 0 = initial := rfl

@[simp] theorem klmcChain_succ (force : E → E) (γ h : ℝ)
    (initial : PhaseSpace E) (noise : ℕ → PhaseSpace E) (k : ℕ) :
    klmcChain force γ h initial noise (k + 1) =
      klmcStep force γ h (klmcChain force γ h initial noise k) (noise k) := rfl

/-- The second-order numerical trajectory, with all four coupled noises. -/
def klmc2Chain (force : E → E) (hessian : E → E →L[ℝ] E) (γ h : ℝ)
    (initial : PhaseSpace E) (noise : ℕ → Fin 4 → E) : ℕ → PhaseSpace E
  | 0 => initial
  | k + 1 => klmc2Step force hessian γ h
      (klmc2Chain force hessian γ h initial noise k) (noise k)

end KineticLangevin
