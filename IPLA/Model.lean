import IPLA.Geometry
import IPLA.Dalalyan
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.WithDensity

set_option linter.style.header false

/-! # Statistical objects in the final statement

The target is defined by its normalized Gibbs density, and the selected center
is required to maximize the latent-variable marginal density. These definitions identify
the objects; they do not prove normalization, invariance or concentration.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace IPLA

/-- The original parameter/latent pair `(θ,x)`, parameter first. For fixed
observations `y`, the standard IPLA potential is `U y (pair θ x) = -log p_θ(x,y)`.
The geometry and dynamics work with the fixed slice `U y`. -/
def pair {dθ dx : ℕ} (θ : EuclideanSpace ℝ (Fin dθ))
    (x : EuclideanSpace ℝ (Fin dx)) : Joint dθ dx :=
  WithLp.toLp 2 (Sum.elim θ x)

/-- Unnormalized marginal density of the parameter, integrating out the latent
variable. For `U_y(θ,x) = -log p_θ(x,y)`, this is the marginal likelihood
`p_θ(y)`. A parameter prior may instead be included in `U_y`. -/
def marginalDensity {dθ dx : ℕ} (U : Joint dθ dx → ℝ) (θ : EuclideanSpace ℝ (Fin dθ)) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-U (pair θ x))) ∂volume

/-- The parameter maximizes the integrated joint density. This is maximum
likelihood in standard IPLA notation, and MAP when the parameter prior is
included in `U`. Its existence is not asserted by this definition. -/
def IsMarginalMaximizer {dθ dx : ℕ} (U : Joint dθ dx → ℝ) (θ : EuclideanSpace ℝ (Fin dθ)) : Prop :=
  ∀ θ', marginalDensity U θ' ≤ marginalDensity U θ

/-- Compatibility name for the prior-inclusive formulation. -/
@[deprecated IsMarginalMaximizer (since := "2026-10-20")]
abbrev IsMarginalMAP {dθ dx : ℕ} (U : Joint dθ dx → ℝ) (θ : EuclideanSpace ℝ (Fin dθ)) : Prop :=
  IsMarginalMaximizer U θ

/-- The normalized density in (49), with `U_N` the actual lifted potential.
The integral and scalar are extended-valued. `gibbsTarget_isProbability` derives
positive finite normalization from the original joint strong convexity, before
any conversion to real numbers. -/
def gibbsTarget {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) : Measure (State N dθ dx) :=
  (∫⁻ z : State N dθ dx, ENNReal.ofReal (Real.exp (-potential U z)) ∂volume)⁻¹ •
    volume.withDensity (fun z ↦ ENNReal.ofReal (Real.exp (-potential U z)))

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- The actual update noise is independent standard Gaussian in every
coordinate and time, and independent of initialization. These are distributional
hypotheses, not a claim to have constructed a random sequence. -/
structure GaussianInnovations {N dθ dx : ℕ} (initial : Lp (State N dθ dx) 2 P)
    (noise : ℕ → Lp (State N dθ dx) 2 P) : Prop where
  coordinateLaw : ∀ k (a : Fin dθ ⊕ (Fin N × Fin dx)),
    HasLaw (fun ω ↦ noise k ω a) (gaussianReal 0 1) P
  independent : iIndepFun
    (fun j : ℕ × (Fin dθ ⊕ (Fin N × Fin dx)) ↦ fun ω ↦ noise j.1 ω j.2) P
  independentInitial : IndepFun (fun ω ↦ initial ω) (fun ω k ↦ noise k ω) P

/-- The laws of the actual noise-driven IPLA recursion, in scaled coordinates.
The coordinate identities in `Geometry.lean` show that this is precisely the
usual average-gradient parameter step and ordinary particle Langevin steps. -/
def laws {N dθ dx : ℕ} [IsProbabilityMeasure P] (U : Joint dθ dx → ℝ) (γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P) :
    ℕ → Measure (State N dθ dx) :=
  fun k ↦ P.map (lpChain P (potential U) (γ / N)
    (potential_gradient_lipschitz hdiff hLip) initial noise k)

end IPLA
