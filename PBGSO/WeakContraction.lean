import PBGSO.PaperTheorems
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.MeasureTheory.Function.L2Space

/-! # General multiplicative-noise contraction at the coupled weak-law level

The synchronous generator below retains the full state- and parameter-dependent
diffusion. Its action on a quadratic test is computed from both Fréchet
derivatives. The energy identity is then derived from the weak forward equation
and the optimiser ODE; it is not a hypothesis of the contraction theorem.

The solution notion explicitly requires the quadratic test to belong to its
generator domain. Establishing this domain property, existence of synchronous
couplings, and equivalence with a strong SDE remain analytic obligations for a
particular stochastic implementation.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
namespace PBGSO

section Quadratic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivative of a general continuous bilinear quadratic form. -/
theorem quadratic_hasFDerivAt (B : E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (fun y => B y y) (B x + B.flip x) x := by
  simpa using B.hasFDerivAt.clm_apply (hasFDerivAt_id x)

/-- Its second derivative is the symmetrisation of the bilinear form. -/
theorem quadratic_second_fderiv (B : E →L[ℝ] E →L[ℝ] ℝ) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => B y y)) x u v = B u v + B v u := by
  have heq : fderiv ℝ (fun y => B y y) = fun y => (B + B.flip) y := by
    funext y
    exact (quadratic_hasFDerivAt B y).fderiv
  rw [heq, (B + B.flip).hasFDerivAt.fderiv]
  rfl
end Quadratic

variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [Fintype I]

/-- Weighted squared sampler separation, as an actual function on a pair. -/
def couplingQuadratic (D : TwistedGeometry S Z) (zz : Z × Z) : ℝ :=
  D.samplerSq (zz.1 - zz.2)

/-- The synchronous two-sampler generator. Both samplers use the same
noise coordinate, which produces the diffusion *difference* in the energy. -/
def synchronousGenerator (M : Model S Θ Z X I) (s s' : S)
    (φ : Z × Z → ℝ) (zz : Z × Z) : ℝ :=
  fderiv ℝ φ zz (M.drift (M.parameter s) zz.1, M.drift (M.parameter s') zz.2) +
    (1 / 2 : ℝ) * ∑ i,
      fderiv ℝ (fderiv ℝ φ) zz
        (M.diffusion (M.parameter s) zz.1 i, M.diffusion (M.parameter s') zz.2 i)
        (M.diffusion (M.parameter s) zz.1 i, M.diffusion (M.parameter s') zz.2 i)

/-- Direct quadratic-generator computation, with arbitrary diffusion
columns. Neither additive noise nor conservative forces are required. -/
theorem synchronousGenerator_quadratic (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (s s' : S) (zz : Z × Z) :
    synchronousGenerator M s s' (couplingQuadratic D) zz =
      2 * samplerCouplingWork M D s s' zz := by
  let R : (Z × Z) →L[ℝ] Z :=
    ContinuousLinearMap.fst ℝ Z Z - ContinuousLinearMap.snd ℝ Z Z
  let B : (Z × Z) →L[ℝ] (Z × Z) →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp R (D.samplerWeight.comp R)
  have hq : couplingQuadratic D = fun y => B y y := rfl
  rw [synchronousGenerator, hq, (quadratic_hasFDerivAt B zz).fderiv]
  simp only [add_apply, ContinuousLinearMap.flip_apply]
  simp_rw [quadratic_second_fderiv]
  change (⟪zz.1 - zz.2, D.samplerWeight
      (M.drift (M.parameter s) zz.1 - M.drift (M.parameter s') zz.2)⟫ +
      ⟪M.drift (M.parameter s) zz.1 - M.drift (M.parameter s') zz.2,
        D.samplerWeight (zz.1 - zz.2)⟫) +
    (1 / 2 : ℝ) * ∑ i,
      (D.samplerSq (M.diffusion (M.parameter s) zz.1 i -
        M.diffusion (M.parameter s') zz.2 i) +
       D.samplerSq (M.diffusion (M.parameter s) zz.1 i -
        M.diffusion (M.parameter s') zz.2 i)) = _
  have hsym : ⟪M.drift (M.parameter s) zz.1 - M.drift (M.parameter s') zz.2,
      D.samplerWeight (zz.1 - zz.2)⟫ =
      ⟪zz.1 - zz.2, D.samplerWeight
        (M.drift (M.parameter s) zz.1 - M.drift (M.parameter s') zz.2)⟫ :=
    (real_inner_comm _ _).trans (D.sampler_symmetric _ _).symm
  rw [hsym]
  simp only [← two_mul, ← Finset.mul_sum, samplerCouplingWork]
  ring

/-- A pair weak forward solution with actual marginal laws. The test
families and their integrability requirements are part of the contract. -/
structure IsCoupledWeakSolution (M : Model S Θ Z X I)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    (s s' : ℝ → S) (ν ν' : ℝ → Measure Z) (Λ : ℝ → Measure (Z × Z)) : Prop where
  left : M.IsWeakSolution tests s ν
  right : M.IsWeakSolution tests s' ν'
  coupling : ∀ t, 0 ≤ t → IsCoupling (Λ t) (ν t) (ν' t)
  test_integrable : ∀ φ ∈ pairTests, ∀ t, 0 ≤ t → Integrable φ (Λ t)
  generator_integrable : ∀ φ ∈ pairTests, ∀ t, 0 ≤ t →
    Integrable (synchronousGenerator M (s t) (s' t) φ) (Λ t)
  forward_equation : ∀ φ ∈ pairTests, ∀ t, 0 ≤ t →
    HasDerivWithinAt (fun r => ∫ zz, φ zz ∂Λ r)
      (∫ zz, synchronousGenerator M (s t) (s' t) φ zz ∂Λ t) (Ici 0) t

/-- Total twisted coupling energy, including the deterministic optimiser. -/
def weakCouplingEnergy (D : TwistedGeometry S Z)
    (s s' : ℝ → S) (Λ : ℝ → Measure (Z × Z)) (t : ℝ) : ℝ :=
  D.optimizerSq (s t - s' t) + ∫ zz, couplingQuadratic D zz ∂Λ t

/-- The ordinary quadratic transport cost of a specific synchronous
sampler coupling and the two deterministic optimiser coordinates. -/
def euclideanCouplingEnergy (s s' : ℝ → S)
    (Λ : ℝ → Measure (Z × Z)) (t : ℝ) : ℝ :=
  ‖s t - s' t‖ ^ 2 + ∫ zz, ‖zz.1 - zz.2‖ ^ 2 ∂Λ t

namespace IsCoupledWeakSolution
variable {M : Model S Θ Z X I} {tests : Set (Z → ℝ)}
  {pairTests : Set (Z × Z → ℝ)} {s s' : ℝ → S}
  {ν ν' : ℝ → Measure Z} {Λ : ℝ → Measure (Z × Z)}
  (hsol : IsCoupledWeakSolution M tests pairTests s s' ν ν' Λ)
  (D : TwistedGeometry S Z) (hquad : couplingQuadratic D ∈ pairTests)

include hsol hquad

/-- Generator-domain integrability supplies the exact work integrability
needed by joint monotonicity. -/
theorem work_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (samplerCouplingWork M D (s t) (s' t)) (Λ t) := by
  have hi := (hsol.generator_integrable _ hquad t ht).const_mul (1 / 2 : ℝ)
  convert hi using 1
  ext zz
  rw [synchronousGenerator_quadratic]
  ring

/-- The actual energy derivative is derived from the weak generator
equation and the optimiser ODE, including its diffusion correction. -/
theorem energy_hasDerivWithinAt (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (weakCouplingEnergy D s s' Λ)
      (2 * (⟪s t - s' t, D.optimizerWeight
        (M.optimizerField t (s t) (ν t) - M.optimizerField t (s' t) (ν' t))⟫ +
        ∫ zz, samplerCouplingWork M D (s t) (s' t) zz ∂Λ t)) (Ici 0) t := by
  have hs := (hsol.left.optimizer_ode t ht).sub (hsol.right.optimizer_ode t ht)
  have hw := D.optimizerWeight.hasFDerivAt.comp_hasDerivWithinAt t hs
  have ho := hs.inner ℝ hw
  have hg := hsol.forward_equation _ hquad t ht
  simp_rw [synchronousGenerator_quadratic] at hg
  rw [integral_const_mul] at hg
  have hsym : ⟪M.optimizerField t (s t) (ν t) - M.optimizerField t (s' t) (ν' t),
      D.optimizerWeight (s t - s' t)⟫ =
      ⟪s t - s' t, D.optimizerWeight
        (M.optimizerField t (s t) (ν t) - M.optimizerField t (s' t) (ν' t))⟫ :=
    (real_inner_comm _ _).trans (D.optimizer_symmetric _ _).symm
  convert ho.add hg using 1
  · rfl
  · dsimp only [Pi.sub_apply, Function.comp_apply]
    rw [hsym]
    ring

/-- Full general twisted-energy contraction for synchronously coupled weak
laws whose generator domain contains the quadratic separation test. -/
theorem energy_decay (ρ T : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    weakCouplingEnergy D s s' Λ t ≤
      weakCouplingEnergy D s s' Λ 0 * Real.exp (-2 * ρ * t) := by
  let E' : ℝ → ℝ := fun r => 2 *
    (⟪s r - s' r, D.optimizerWeight
      (M.optimizerField r (s r) (ν r) - M.optimizerField r (s' r) (ν' r))⟫ +
      ∫ zz, samplerCouplingWork M D (s r) (s' r) zz ∂Λ r)
  have hd (r : ℝ) (hr : 0 ≤ r) :
      HasDerivWithinAt (weakCouplingEnergy D s s' Λ) (E' r) (Ici 0) r :=
    hsol.energy_hasDerivWithinAt D hquad r hr
  apply PBGSO.energy_decay (E' := E') (T := T)
  · intro r hr
    exact ((hd r hr.1).continuousWithinAt).mono Icc_subset_Ici_self
  · intro r hr
    exact (hd r hr.1).mono (Ici_subset_Ici.mpr hr.1)
  · intro r hr
    have h := hmono r hr.1 (s r) (s' r) (ν r) (ν' r) (Λ r)
      (hsol.coupling r hr.1) (hsol.left.probability r hr.1)
      (hsol.right.probability r hr.1) (hsol.left.second_moment r hr.1)
      (hsol.right.second_moment r hr.1)
      (hsol.left.gradient_integrable r hr.1) (hsol.right.gradient_integrable r hr.1)
      (hsol.work_integrable D hquad r hr.1) (hsol.test_integrable _ hquad r hr.1)
    dsimp [E', weakCouplingEnergy, couplingQuadratic]
    linarith
  · exact ht

/-- The twisted energy is nonnegative because both weights are positive. -/
theorem energy_nonneg (t : ℝ) : 0 ≤ weakCouplingEnergy D s s' Λ t := by
  exact add_nonneg (D.optimizerSq_nonneg _)
    (integral_nonneg fun _ => D.samplerSq_nonneg _)

section TransportCost
variable [BorelSpace Z] [SecondCountableTopology Z]

/-- The finite second moments of the actual marginals imply integrability
of the actual joint quadratic transport cost. -/
theorem cost_integrable (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun zz : Z × Z => ‖zz.1 - zz.2‖ ^ 2) (Λ t) := by
  have hν : MemLp (fun z : Z => z) 2 (ν t) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).2
      (hsol.left.second_moment t ht)
  have hν' : MemLp (fun z : Z => z) 2 (ν' t) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).2
      (hsol.right.second_moment t ht)
  have hf : MemLp (fun zz : Z × Z => zz.1) 2 (Λ t) := by
    have he : MemLp (fun z : Z => z) 2 ((Λ t).map Prod.fst) := by
      rw [(hsol.coupling t ht).1]
      exact hν
    exact he.comp_of_map measurable_fst.aemeasurable
  have hg : MemLp (fun zz : Z × Z => zz.2) 2 (Λ t) := by
    have he : MemLp (fun z : Z => z) 2 ((Λ t).map Prod.snd) := by
      rw [(hsol.coupling t ht).2]
      exact hν'
    exact he.comp_of_map measurable_snd.aemeasurable
  exact (memLp_two_iff_integrable_sq_norm (hf.sub hg).aestronglyMeasurable).1
    (hf.sub hg)

/-- The lower metric comparison is integrated over the genuine coupling. -/
theorem energy_lower (t : ℝ) (ht : 0 ≤ t) :
    D.lower * euclideanCouplingEnergy s s' Λ t ≤ weakCouplingEnergy D s s' Λ t := by
  have hc := hsol.cost_integrable D hquad t ht
  have hq := hsol.test_integrable _ hquad t ht
  have hi := integral_mono (hc.const_mul D.lower) hq
    (fun zz : Z × Z => D.sampler_lower (zz.1 - zz.2))
  rw [integral_const_mul] at hi
  simpa [weakCouplingEnergy, euclideanCouplingEnergy, TwistedGeometry.optimizerSq,
    mul_add] using add_le_add (D.optimizer_lower (s t - s' t)) hi

/-- The upper metric comparison is integrated over the genuine coupling. -/
theorem energy_upper (t : ℝ) (ht : 0 ≤ t) :
    weakCouplingEnergy D s s' Λ t ≤ D.upper * euclideanCouplingEnergy s s' Λ t := by
  have hc := hsol.cost_integrable D hquad t ht
  have hq := hsol.test_integrable _ hquad t ht
  have hi := integral_mono hq (hc.const_mul D.upper)
    (fun zz : Z × Z => D.sampler_upper (zz.1 - zz.2))
  rw [integral_const_mul] at hi
  simpa [weakCouplingEnergy, euclideanCouplingEnergy, TwistedGeometry.optimizerSq,
    mul_add] using add_le_add (D.optimizer_upper (s t - s' t)) hi

/-- The root cost contraction with precisely the source condition-number
factor. This concerns a specific actual joint law; taking the initial
coupling infimum is a separate transport theorem. -/
theorem rms_decay (ρ T : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Real.sqrt (euclideanCouplingEnergy s s' Λ t) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
        Real.sqrt (euclideanCouplingEnergy s s' Λ 0) := by
  have hT := ht.1.trans ht.2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hd := hsol.energy_decay D hquad ρ T hmono t ht
  have hlo := hsol.energy_lower D hquad t ht.1
  have hup := hsol.energy_upper D hquad 0 le_rfl
  have hcn : 0 ≤ D.conditionNumber :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) D.conditionNumber_ge_one
  have hn (r : ℝ) : 0 ≤ euclideanCouplingEnergy s s' Λ r :=
    add_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (hn t), mul_pow, mul_pow, Real.sq_sqrt hcn,
    Real.sq_sqrt (hn 0)]
  have he : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  have hi := mul_le_mul_of_nonneg_right hup (Real.exp_pos (-2 * ρ * t)).le
  apply (mul_le_mul_iff_of_pos_left D.lower_pos).mp
  have hκ : D.lower * D.conditionNumber = D.upper := by
    dsimp [TwistedGeometry.conditionNumber]
    field_simp [D.lower_pos.ne']
  calc
    D.lower * euclideanCouplingEnergy s s' Λ t ≤
        (D.upper * euclideanCouplingEnergy s s' Λ 0) *
          Real.exp (-2 * ρ * t) := hlo.trans (hd.trans hi)
    _ = D.lower * (D.conditionNumber * Real.exp (-2 * ρ * t) *
        euclideanCouplingEnergy s s' Λ 0) := by rw [← hκ]; ring

end TransportCost

end IsCoupledWeakSolution
end PBGSO
