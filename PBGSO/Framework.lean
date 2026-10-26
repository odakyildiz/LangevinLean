import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The general particle-based gradient stochastic optimisation framework

`Model` has independent optimiser, parameter, sampler, observation and noise
coordinate types. In particular neither the optimiser nor the sampler is
restricted to a first-order gradient flow. Auxiliary momenta and adaptive
optimiser variables belong to `S`; augmented sampler variables belong to `Z`.

`IsWeakSolution` states the actual optimiser ODE and weak Fokker--Planck
equation. It is a law-level solution notion. No existence, equivalence to a
strong SDE, or stochastic Itô formula is asserted by this file.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PBGSO

variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [MeasurableSpace Z] [Fintype I]

/-- The `P₂` condition on a sampler law. Probability normalisation is
specified separately, so this predicate records exactly the moment input. -/
def HasFiniteSecondMoment (ν : Measure Z) : Prop :=
  Integrable (fun z => ‖z‖ ^ 2) ν

/-- The paper's independent optimiser and sampler design choices. A finite
noise index specifies the columns of the diffusion matrix. -/
structure Model (S Θ Z X I : Type*)
    [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] where
  parameter : S → Θ
  position : Z → X
  observation : Θ → X → Θ
  optimizer : ℝ → S → Θ → S
  drift : Θ → Z → Z
  diffusion : Θ → Z → I → Z

namespace Model

variable (M : Model S Θ Z X I)

/-- `G_ν(ϑ)`, with an actual Bochner integral over the full sampler state. -/
def meanGradient (ν : Measure Z) (s : S) : Θ :=
  ∫ z, M.observation (M.parameter s) (M.position z) ∂ν

/-- The full optimiser vector field driven by a sampler law. -/
def optimizerField (t : ℝ) (s : S) (ν : Measure Z) : S :=
  M.optimizer t s (M.meanGradient ν s)

/-- The interacting-particle gradient. All particles share the same complete
optimiser state. Bounds use `0 < N`, since no gradient estimate exists for an
empty particle population. -/
def particleGradient (N : ℕ) (s : S) (z : Fin N → Z) : Θ :=
  (N : ℝ)⁻¹ • ∑ i, M.observation (M.parameter s) (M.position (z i))

/-- The sampler empirical measure. At positive population size its total
mass is one; zero population is excluded by all sampling estimates. -/
def empiricalLaw (N : ℕ) (z : Fin N → Z) : Measure Z :=
  (N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (z i)

/-- The finite-sum gradient is exactly integration against the empirical
law, rather than an independent primitive estimator. -/
theorem meanGradient_empirical [MeasurableSingletonClass Z] [CompleteSpace Θ]
    (N : ℕ) (s : S) (z : Fin N → Z) :
    M.meanGradient (empiricalLaw N z) s = M.particleGradient N s z := by
  classical
  unfold meanGradient empiricalLaw particleGradient
  rw [integral_smul_measure]
  rw [integral_finsetSum_measure
    (fun i _ => integrable_dirac (by simp))]
  simp

/-- The augmented invariant law has the intended gradient expectation as
soon as its observation projection has the target marginal. -/
theorem meanGradient_of_marginal [MeasurableSpace X]
    (s : S) (ν : Measure Z) (π : Measure X)
    (hposition : AEMeasurable M.position ν)
    (hmarginal : ν.map M.position = π)
    (hobs : AEStronglyMeasurable (M.observation (M.parameter s)) π) :
    M.meanGradient ν s = ∫ x, M.observation (M.parameter s) x ∂π := by
  rw [meanGradient, ← hmarginal]
  exact (integral_map hposition (hmarginal ▸ hobs)).symm

/-- The empirical law is a probability law for positive particle count. -/
theorem empiricalLaw_probability (N : ℕ) (hN : 0 < N) (z : Fin N → Z) :
    IsProbabilityMeasure (empiricalLaw N z) := by
  constructor
  simp [empiricalLaw]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp)

/-- The continuous-time particle vector field, before time discretisation. -/
def particleField (N : ℕ) (t : ℝ) (s : S) (z : Fin N → Z) : S :=
  M.optimizer t s (M.particleGradient N s z)

/-- An Euler step for an arbitrary optimiser response and sampler. `noise`
contains Brownian increments, with their scaling already included. -/
def particleEulerStep (N : ℕ) (t h : ℝ) (s : S) (z : Fin N → Z)
    (noise : Fin N → I → ℝ) : S × (Fin N → Z) :=
  (s + h • M.particleField N t s z,
   fun i => z i + h • M.drift (M.parameter s) (z i) +
     ∑ j, noise i j • M.diffusion (M.parameter s) (z i) j)

/-- The frozen sampler generator, including state- and parameter-dependent
diffusion. The two Fréchet derivatives are evaluated in sampler coordinates. -/
def generator (θ : Θ) (φ : Z → ℝ) (z : Z) : ℝ :=
  fderiv ℝ φ z (M.drift θ z) +
    (1 / 2 : ℝ) * ∑ i,
      (fderiv ℝ (fderiv ℝ φ) z (M.diffusion θ z i)) (M.diffusion θ z i)

/-- A weak law solution for a specified separating test family. This makes
the analytic solution notion explicit instead of assuming an error bound.
Integrability is required rather than relying on totalised integrals. -/
structure IsWeakSolution (tests : Set (Z → ℝ)) (s : ℝ → S)
    (ν : ℝ → Measure Z) : Prop where
  probability : ∀ t, 0 ≤ t → IsProbabilityMeasure (ν t)
  second_moment : ∀ t, 0 ≤ t → HasFiniteSecondMoment (ν t)
  gradient_integrable : ∀ t, 0 ≤ t →
    Integrable (fun z => M.observation (M.parameter (s t)) (M.position z)) (ν t)
  optimizer_ode : ∀ t, 0 ≤ t →
    HasDerivWithinAt s (M.optimizerField t (s t) (ν t)) (Ici 0) t
  test_integrable : ∀ φ ∈ tests, ∀ t, 0 ≤ t → Integrable φ (ν t)
  generator_integrable : ∀ φ ∈ tests, ∀ t, 0 ≤ t →
    Integrable (M.generator (M.parameter (s t)) φ) (ν t)
  forward_equation : ∀ φ ∈ tests, ∀ t, 0 ≤ t →
    HasDerivWithinAt (fun r => ∫ z, φ z ∂ν r)
      (∫ z, M.generator (M.parameter (s t)) φ z ∂ν t) (Ici 0) t

/-- Frozen stationarity stated at the infinitesimal generator level. This
is an analytic input: boundary conditions and generator-domain arguments
must establish it for a proposed Gibbs diffusion. -/
structure FrozenStationary (tests : Set (Z → ℝ)) (θ : Θ) (ν : Measure Z) : Prop where
  probability : IsProbabilityMeasure ν
  second_moment : HasFiniteSecondMoment ν
  test_integrable : ∀ φ ∈ tests, Integrable φ ν
  generator_integrable : ∀ φ ∈ tests, Integrable (M.generator θ φ) ν
  generator_zero : ∀ φ ∈ tests, (∫ z, M.generator θ φ z ∂ν) = 0

/-- Uniqueness is quantified over the explicit ODE/forward equation above.
It is a well-posedness assumption, not a stationarity conclusion. -/
def WeakUniqueness (tests : Set (Z → ℝ)) : Prop :=
  ∀ s ν s' ν', M.IsWeakSolution tests s ν → M.IsWeakSolution tests s' ν' →
    s 0 = s' 0 → ν 0 = ν' 0 → ∀ t, 0 ≤ t → s t = s' t ∧ ν t = ν' t

/-- Paper Theorem 1, candidate part: a vanishing exact gradient, a fixed
optimiser state, and a frozen invariant sampler make a constant weak
solution. Time-dependent optimiser responses are allowed. -/
theorem constant_isWeakSolution (tests : Set (Z → ℝ)) (sStar : S) (νStar : Measure Z)
    (hν : M.FrozenStationary tests (M.parameter sStar) νStar)
    (hint : Integrable
      (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t, 0 ≤ t → M.optimizer t sStar 0 = 0) :
    M.IsWeakSolution tests (fun _ => sStar) (fun _ => νStar) where
  probability := fun _ _ => hν.probability
  second_moment := fun _ _ => hν.second_moment
  gradient_integrable := fun _ _ => hint
  optimizer_ode := by
    intro t ht
    simpa [optimizerField, hg, hfix t ht] using
      (hasDerivWithinAt_const t (Ici (0 : ℝ)) sStar)
  test_integrable := fun φ hφ _ _ => hν.test_integrable φ hφ
  generator_integrable := fun φ hφ _ _ => hν.generator_integrable φ hφ
  forward_equation := by
    intro φ hφ t ht
    simpa [hν.generator_zero φ hφ] using
      (hasDerivWithinAt_const t (Ici (0 : ℝ)) (∫ z, φ z ∂νStar))

/-- Paper Theorem 1 at the explicit weak-solution level. The only analytic
inputs are frozen generator stationarity, integrability and uniqueness. -/
theorem stationary_of_frozen (tests : Set (Z → ℝ))
    (hunique : M.WeakUniqueness tests) (sStar : S) (νStar : Measure Z)
    (hν : M.FrozenStationary tests (M.parameter sStar) νStar)
    (hint : Integrable
      (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t, 0 ≤ t → M.optimizer t sStar 0 = 0)
    (s : ℝ → S) (ν : ℝ → Measure Z) (hsol : M.IsWeakSolution tests s ν)
    (hs : s 0 = sStar) (hn : ν 0 = νStar) (t : ℝ) (ht : 0 ≤ t) :
    s t = sStar ∧ ν t = νStar :=
  hunique s ν (fun _ => sStar) (fun _ => νStar) hsol
    (M.constant_isWeakSolution tests sStar νStar hν hint hg hfix) hs hn t ht

/-- The gradient identity makes every stationary point suitable for the
previous stationarity theorem. It does not assert global minimality. -/
theorem meanGradient_zero_of_gradient_identity
    (loss : Θ → ℝ) [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (sStar : S) (νStar : Measure Z)
    (hid : M.meanGradient νStar sStar = gradient loss (M.parameter sStar))
    (hcritical : gradient loss (M.parameter sStar) = 0) :
    M.meanGradient νStar sStar = 0 := hid.trans hcritical

/-- Relabelling particles does not change their common gradient estimate. -/
theorem particleGradient_perm (N : ℕ) (s : S) (z : Fin N → Z)
    (e : Equiv.Perm (Fin N)) :
    M.particleGradient N s (z ∘ e) = M.particleGradient N s z := by
  unfold particleGradient
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end Model
end PBGSO
