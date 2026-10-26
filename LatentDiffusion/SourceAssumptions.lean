import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Literal source regularity contracts

These are assumption translations, not existence theorems. In particular the
paper's universal solution premise includes strictly positive classical densities
at time zero even for arbitrary finite-second-moment initial laws. It is recorded
literally so that this strength is visible; it is not inferred from the other
source assumptions or used to hide an analytic bridge.
-/

noncomputable section

namespace LatentDiffusion.SourceAssumptions

open MeasureTheory Set
open scoped NNReal

variable {P Z : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The source's normalized tilted posterior, with the normalizing constant
provided as model data. Normalization and existence of this constant are part of
the model interpretation, not proved by the regularity contract. -/
def normalizedPosterior (ρ : P → Z → ℝ) (A : P → ℝ) (p : P) (z : Z) : ℝ :=
  ρ p z / A p

/-- The manuscript's model-regularity assumption. Parameter differentiability is
pointwise in the latent state; spatial regularity is pointwise in the parameter. -/
structure ModelRegularity (ρ : P → Z → ℝ) (A : P → ℝ) : Prop where
  posterior_parameter_differentiable :
    ∀ z, Differentiable ℝ (fun p ↦ normalizedPosterior ρ A p z)
  evidence_differentiable : Differentiable ℝ A
  posterior_spatial_C2 : ∀ p, ContDiff ℝ 2 (normalizedPosterior ρ A p)
  tilted_positive : ∀ p z, 0 < ρ p z

/-- The time-space domain in the source's C^{1,2} density assumption. -/
def timeSpaceDomain : Set (ℝ × Z) := Ici 0 ×ˢ univ

/-- Explicit partial derivatives and their joint continuity on the closed positive
time half-space. Time derivatives at zero are right derivatives, not derivatives
of an extension to negative time. This is the C^{1,2} meaning used here. -/
def ClassicalDensityRegularity {M : ℕ} (q : Fin M → ℝ → Z → ℝ) : Prop :=
  ∃ (dt : Fin M → ℝ → Z → ℝ)
    (dz : Fin M → ℝ → Z → (Z →L[ℝ] ℝ))
    (dzz : Fin M → ℝ → Z → (Z →L[ℝ] (Z →L[ℝ] ℝ))),
    ∀ m,
      ContinuousOn (fun tz : ℝ × Z ↦ q m tz.1 tz.2) timeSpaceDomain ∧
      ContinuousOn (fun tz : ℝ × Z ↦ dt m tz.1 tz.2) timeSpaceDomain ∧
      ContinuousOn (fun tz : ℝ × Z ↦ dz m tz.1 tz.2) timeSpaceDomain ∧
      ContinuousOn (fun tz : ℝ × Z ↦ dzz m tz.1 tz.2) timeSpaceDomain ∧
      (∀ t, 0 ≤ t → ∀ z, HasDerivWithinAt (fun s ↦ q m s z) (dt m t z) (Ici 0) t) ∧
      (∀ t, 0 ≤ t → ∀ z, HasFDerivAt (q m t) (dz m t z) z) ∧
      (∀ t, 0 ≤ t → ∀ z, HasFDerivAt (dz m t) (dzz m t z) z)

variable [MeasurableSpace Z]

/-- All data in a source classical solution. `flowEquation` is the actual gradient
flow equation chosen by the application, rather than a scalar energy estimate.
The density is required to realize the initial law as well as later laws. -/
structure ClassicalSolution {M : ℕ} (ν : Measure Z)
    (flowEquation : (ℝ → P) → (Fin M → ℝ → ProbabilityMeasure Z) → Prop)
    (p₀ : P) (μ₀ : Fin M → ProbabilityMeasure Z) where
  parameter : ℝ → P
  law : Fin M → ℝ → ProbabilityMeasure Z
  density : Fin M → ℝ → Z → ℝ
  initial_parameter : parameter 0 = p₀
  initial_law : ∀ m, law m 0 = μ₀ m
  parameter_C1 : ContDiffOn ℝ 1 parameter (Ici 0)
  density_C12 : ClassicalDensityRegularity density
  density_positive : ∀ m t, 0 ≤ t → ∀ z, 0 < density m t z
  density_realizes : ∀ m t, 0 ≤ t →
    (law m t : Measure Z) = ν.withDensity (fun z ↦ ENNReal.ofReal (density m t z))
  finite_second_moment : ∀ m t, 0 ≤ t → MemLp (fun z : Z ↦ z) 2 (law m t : Measure Z)
  solves : flowEquation parameter law

/-- Literal universal solution-regularity premise: every parameter and every
finite-second-moment initial probability law admits the classical solution above.
This includes the source's density regularity and positivity at t=0. -/
def SolutionRegularity {M : ℕ} (ν : Measure Z)
    (flowEquation : (ℝ → P) → (Fin M → ℝ → ProbabilityMeasure Z) → Prop) : Prop :=
  ∀ (p₀ : P) (μ₀ : Fin M → ProbabilityMeasure Z),
    (∀ m, MemLp (fun z : Z ↦ z) 2 (μ₀ m : Measure Z)) →
      Nonempty (ClassicalSolution ν flowEquation p₀ μ₀)

section Potential

variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The source's joint strong-log-concavity premise, expressed for each negative
log tilted density `U i` in the full parameter-latent pair space. -/
structure JointStrongLogConcavity (U : I → H → ℝ) (m : ℝ) : Prop where
  positive : 0 < m
  strong : ∀ i, StrongConvexOn univ m (U i)

/-- The source's differentiable joint log-likelihood and positive global
gradient-Lipschitz constant. Negating a log density preserves this bound. -/
structure LipschitzGradient (U : I → H → ℝ) (L : ℝ≥0) : Prop where
  positive : 0 < L
  differentiable : ∀ i, Differentiable ℝ (U i)
  lipschitz : ∀ i, LipschitzWith L (gradient (U i))

end Potential

end LatentDiffusion.SourceAssumptions
