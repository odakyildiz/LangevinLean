import PBGSO.WeakContraction
import PBGSO.EmpiricalMonotonicity

/-! # The actual particle/copy synchronous generator

The complete optimiser is a coordinate of the random interacting state.
The reference optimiser uses a population observation and its sampler copies
use the same coordinate Brownian drivers as the interacting particles.
The quadratic generator is computed from both derivatives of the actual
finite-dimensional test. Its expected-energy identity follows from a weak
forward equation, rather than being assumed as an error estimate.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace PBGSO

variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z] [Fintype I]

/-- A full interacting state paired with a full independent-copy state.
The law of the latter is separately required to be an independent-copy law
when the Monte Carlo variance theorem is used. -/
abbrev ParticlePair (N : ℕ) (S Z : Type*) :=
  (S × (Fin N → Z)) × (S × (Fin N → Z))

/-- Difference of the complete optimiser coordinates. -/
def particleOptimizerDifference (N : ℕ) : ParticlePair N S Z →L[ℝ] S :=
  (ContinuousLinearMap.fst ℝ S (Fin N → Z)).comp
      (ContinuousLinearMap.fst ℝ (S × (Fin N → Z)) (S × (Fin N → Z))) -
  (ContinuousLinearMap.fst ℝ S (Fin N → Z)).comp
      (ContinuousLinearMap.snd ℝ (S × (Fin N → Z)) (S × (Fin N → Z)))

/-- Difference of the paired i-th sampler coordinates. -/
def particleSamplerDifference (N : ℕ) (i : Fin N) : ParticlePair N S Z →L[ℝ] Z :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.snd ℝ S (Fin N → Z)).comp
        (ContinuousLinearMap.fst ℝ (S × (Fin N → Z)) (S × (Fin N → Z))) -
     (ContinuousLinearMap.snd ℝ S (Fin N → Z)).comp
        (ContinuousLinearMap.snd ℝ (S × (Fin N → Z)) (S × (Fin N → Z))))

/-- The actual bilinear form of the normalised particle coupling metric. -/
def particleQuadraticBilinear (D : TwistedGeometry S Z) (N : ℕ) :
    ParticlePair N S Z →L[ℝ] ParticlePair N S Z →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (particleOptimizerDifference N)
      (D.optimizerWeight.comp (particleOptimizerDifference N)) +
    (N : ℝ)⁻¹ • ∑ i : Fin N,
      (innerSL ℝ).bilinearComp (particleSamplerDifference N i)
        (D.samplerWeight.comp (particleSamplerDifference N i))

theorem particleQuadraticBilinear_apply (D : TwistedGeometry S Z) (N : ℕ)
    (p q : ParticlePair N S Z) :
    particleQuadraticBilinear D N p q =
      ⟪p.1.1 - p.2.1, D.optimizerWeight (q.1.1 - q.2.1)⟫ +
        (N : ℝ)⁻¹ * ∑ i, ⟪p.1.2 i - p.2.2 i,
          D.samplerWeight (q.1.2 i - q.2.2 i)⟫ := by
  simp [particleQuadraticBilinear, particleOptimizerDifference,
    particleSamplerDifference, ContinuousLinearMap.bilinearComp_apply,
    inner_sub_left, Finset.sum_sub_distrib]

theorem particleQuadraticBilinear_symmetric (D : TwistedGeometry S Z) (N : ℕ)
    (p q : ParticlePair N S Z) :
    particleQuadraticBilinear D N p q = particleQuadraticBilinear D N q p := by
  simp only [particleQuadraticBilinear_apply]
  congr 1
  · exact (D.optimizer_symmetric _ _).trans (real_inner_comm _ _)
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (D.sampler_symmetric _ _).trans (real_inner_comm _ _)

theorem particleQuadraticBilinear_diag (D : TwistedGeometry S Z) (N : ℕ)
    (p : ParticlePair N S Z) :
    particleQuadraticBilinear D N p p =
      particleCouplingEnergy D N p.1.1 p.2.1 p.1.2 p.2.2 :=
  particleQuadraticBilinear_apply D N p p

/-- The actual paired drift: empirical observation for the interacting
optimiser, population observation for the reference optimiser. -/
def particleCopyDrift (M : Model S Θ Z X I) (N : ℕ) (ν : Measure Z)
    (t : ℝ) (p : ParticlePair N S Z) : ParticlePair N S Z :=
  ((M.particleField N t p.1.1 p.1.2,
      fun i => M.drift (M.parameter p.1.1) (p.1.2 i)),
   (M.optimizerField t p.2.1 ν,
      fun i => M.drift (M.parameter p.2.1) (p.2.2 i)))

/-- One Brownian driver for particle i acts on the same reference copy i.
Both optimiser noise coordinates are identically zero. -/
def particleCopyDiffusion (M : Model S Θ Z X I) (N : ℕ)
    (p : ParticlePair N S Z) (ij : Fin N × I) : ParticlePair N S Z :=
  ((0, fun k => if k = ij.1 then M.diffusion (M.parameter p.1.1) (p.1.2 k) ij.2 else 0),
   (0, fun k => if k = ij.1 then M.diffusion (M.parameter p.2.1) (p.2.2 k) ij.2 else 0))

/-- Full paired particle generator with the true empirical optimiser map. -/
def particleCopyGenerator (M : Model S Θ Z X I) (N : ℕ) (ν : Measure Z)
    (t : ℝ) (φ : ParticlePair N S Z → ℝ) (p : ParticlePair N S Z) : ℝ :=
  fderiv ℝ φ p (particleCopyDrift M N ν t p) +
    (1 / 2 : ℝ) * ∑ ij : Fin N × I,
      fderiv ℝ (fderiv ℝ φ) p
        (particleCopyDiffusion M N p ij) (particleCopyDiffusion M N p ij)

/-- A diffusion column has exactly its corresponding normalised sampler
quadratic cost, with no optimiser contribution. -/
theorem particleCopyDiffusion_quadratic (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (N : ℕ) (p : ParticlePair N S Z) (ij : Fin N × I) :
    particleQuadraticBilinear D N (particleCopyDiffusion M N p ij)
      (particleCopyDiffusion M N p ij) =
      (N : ℝ)⁻¹ * D.samplerSq
        (M.diffusion (M.parameter p.1.1) (p.1.2 ij.1) ij.2 -
         M.diffusion (M.parameter p.2.1) (p.2.2 ij.1) ij.2) := by
  classical
  rw [particleQuadraticBilinear_apply]
  dsimp only [particleCopyDiffusion]
  simp only [sub_self, inner_zero_left, zero_add]
  congr 1
  rw [Finset.sum_eq_single ij.1]
  · simp [TwistedGeometry.samplerSq]
  · intro k _ hk
    simp [hk]
  · simp

/-- The quadratic generator contains joint empirical work and precisely
the additional empirical-versus-population optimiser fluctuation. -/
theorem particleCopyGenerator_quadratic (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (N : ℕ) (ν : Measure Z) (t : ℝ)
    (p : ParticlePair N S Z) :
    particleCopyGenerator M N ν t (fun q => particleQuadraticBilinear D N q q) p =
      2 * (particleCouplingWork M D N t p.1.1 p.2.1 p.1.2 p.2.2 +
        ⟪p.1.1 - p.2.1, D.optimizerWeight
          (M.particleField N t p.2.1 p.2.2 - M.optimizerField t p.2.1 ν)⟫) := by
  classical
  rw [particleCopyGenerator, (quadratic_hasFDerivAt _ p).fderiv]
  simp only [add_apply, ContinuousLinearMap.flip_apply,
    quadratic_second_fderiv, particleQuadraticBilinear_symmetric]
  rw [← particle_population_work_decomposition M D N t p.1.1 p.2.1 p.1.2 p.2.2 ν]
  simp_rw [← two_mul, ← Finset.mul_sum]
  simp_rw [particleCopyDiffusion_quadratic]
  simp only [particleQuadraticBilinear_apply, particleCopyDrift]
  simp only [Fintype.sum_prod_type, samplerCouplingWork, Finset.sum_add_distrib,
    Finset.mul_sum]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

section ForwardEquation
variable [MeasurableSpace S]

/-- The law-level forward equation for the displayed actual particle/copy
drift and synchronous diffusion. Reference iid marginals and deterministic
reference optimiser states are separate premises of sampling estimates. -/
structure IsParticleCopyWeakSolution (M : Model S Θ Z X I) (N : ℕ)
    (ν : ℝ → Measure Z) (tests : Set (ParticlePair N S Z → ℝ))
    (Γ : ℝ → Measure (ParticlePair N S Z)) : Prop where
  probability : ∀ t, 0 ≤ t → IsProbabilityMeasure (Γ t)
  test_integrable : ∀ φ ∈ tests, ∀ t, 0 ≤ t → Integrable φ (Γ t)
  generator_integrable : ∀ φ ∈ tests, ∀ t, 0 ≤ t →
    Integrable (particleCopyGenerator M N (ν t) t φ) (Γ t)
  forward_equation : ∀ φ ∈ tests, ∀ t, 0 ≤ t →
    HasDerivWithinAt (fun r => ∫ p, φ p ∂Γ r)
      (∫ p, particleCopyGenerator M N (ν t) t φ p ∂Γ t) (Set.Ici 0) t

/-- Expected actual optimiser-plus-averaged-particle quadratic separation. -/
def expectedParticleEnergy (D : TwistedGeometry S Z) (N : ℕ)
    (Γ : ℝ → Measure (ParticlePair N S Z)) (t : ℝ) : ℝ :=
  ∫ p, particleQuadraticBilinear D N p p ∂Γ t

namespace IsParticleCopyWeakSolution
variable {M : Model S Θ Z X I} {N : ℕ} {ν : ℝ → Measure Z}
  {tests : Set (ParticlePair N S Z → ℝ)} {Γ : ℝ → Measure (ParticlePair N S Z)}

/-- The expected energy derivative is computed from the actual full-state
generator, retaining precisely the population-gradient fluctuation term. -/
theorem energy_hasDerivWithinAt (hsol : IsParticleCopyWeakSolution M N ν tests Γ)
    (D : TwistedGeometry S Z)
    (hquad : (fun p => particleQuadraticBilinear D N p p) ∈ tests)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (expectedParticleEnergy D N Γ)
      (2 * ∫ p, particleCouplingWork M D N t p.1.1 p.2.1 p.1.2 p.2.2 +
        ⟪p.1.1 - p.2.1, D.optimizerWeight
          (M.particleField N t p.2.1 p.2.2 - M.optimizerField t p.2.1 (ν t))⟫ ∂Γ t)
      (Set.Ici 0) t := by
  have hd := hsol.forward_equation _ hquad t ht
  simp_rw [particleCopyGenerator_quadratic] at hd
  change HasDerivWithinAt (fun r => ∫ p, particleQuadraticBilinear D N p p ∂Γ r)
    _ _ _
  simpa only [integral_const_mul] using hd

end IsParticleCopyWeakSolution
end ForwardEquation

end PBGSO
