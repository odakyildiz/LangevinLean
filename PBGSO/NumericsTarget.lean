import PBGSO.ParameterBound
import PBGSO.ParticleMethodLp
import PBGSO.TargetBias

/-! # Numerical parameter errors to actual stationary targets

The numerical and integral-reference variables live on the same probability
space. A compatibility equality explicitly identifies the reference parameter
law with the interacting optimiser parameter law used by the weak-generator
bound. This file does not assert that an arbitrary integral solution has that
weak law: such identification is an explicit premise. All triangles are
proved for the actual L² random variables. HOL may add a separately certified
original/surrogate target coupling bias.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace Topology
namespace PBGSO
open Methods

section LpTriangle
variable {Ω A B C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [MeasurableSpace B]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The L² triangle is applied to actual random variables on one common
probability space. -/
theorem numerical_target_triangle (X Y : Lp A 2 Q) (a : A) :
    ‖X - Lp.const 2 Q a‖ ≤ ‖X - Y‖ + ‖Y - Lp.const 2 Q a‖ :=
  norm_sub_le_norm_sub_add_norm_sub X Y _

/-- Changing a deterministic target incurs exactly its actual coordinate
distance on a probability space. -/
theorem numerical_target_shift (X : Lp A 2 Q) (a b : A) :
    ‖X - Lp.const 2 Q b‖ ≤ ‖X - Lp.const 2 Q a‖ + ‖a - b‖ := by
  have h := numerical_target_triangle Q X (Lp.const 2 Q a) b
  rw [← map_sub, Lp.norm_const 2 Q (a - b) (by norm_num)] at h
  simpa using h

/-- An explicit equality of parameter-coordinate laws transfers the genuine
reference L² target norm to the weak particle/reference joint law. -/
theorem lp_target_norm_eq_law_rms (X : Lp A 2 Q) (a : A)
    (Γ : Measure B) (f : B → A) (hf : AEMeasurable f Γ)
    (hLaw : Q.map X = Γ.map f) :
    ‖X - Lp.const 2 Q a‖ = Real.sqrt (∫ p, ‖f p - a‖ ^ 2 ∂Γ) := by
  have hn := ProximalLangevin.lp_norm_sq_eq_integral Q (X - Lp.const 2 Q a)
  have he : (∫ ω, ‖(X - Lp.const 2 Q a) ω‖ ^ 2 ∂Q) =
      ∫ ω, ‖X ω - a‖ ^ 2 ∂Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub X (Lp.const 2 Q a),
      Lp.coeFn_const 2 Q a] with ω hs hc
    simp only [Pi.sub_apply, Function.const_apply] at hs hc
    rw [hs, hc]
  rw [he] at hn
  have hX : AEMeasurable X Q := (Lp.aestronglyMeasurable X).aemeasurable
  have hg : Continuous (fun v : A ↦ ‖v - a‖ ^ 2) := by fun_prop
  have hmap : (∫ ω, ‖X ω - a‖ ^ 2 ∂Q) = ∫ p, ‖f p - a‖ ^ 2 ∂Γ := by
    rw [← integral_map hX hg.aestronglyMeasurable, hLaw,
      integral_map hf hg.aestronglyMeasurable]
  rw [hmap] at hn
  rw [← hn, Real.sqrt_sq (norm_nonneg _)]

/-- The actual momentum scheme's optimiser-position error is one of the
terms controlled by the proved phase error. -/
theorem momentum_parameter_triangle
    (z r : ((Lp A 2 Q) × C) × ((Lp A 2 Q) × C)) (a : A) :
    ‖z.2.1 - Lp.const 2 Q a‖ ≤ phaseError z r + ‖r.2.1 - Lp.const 2 Q a‖ := by
  have hc : ‖z.2.1 - r.2.1‖ ≤ phaseError z r := by
    have h := norm_fst_le (z.2 - r.2)
    dsimp only [Prod.fst_sub] at h
    exact h.trans (le_add_of_nonneg_left (norm_nonneg _))
  exact (numerical_target_triangle Q _ _ a).trans (add_le_add hc (le_refl _))

/-- The HOL optimiser coordinate is the first actual L² coordinate. -/
theorem higherOrder_parameter_triangle
    (z r : HOLState (Lp A 2 Q) C) (a : A) :
    ‖z.1 - Lp.const 2 Q a‖ ≤ holError z r + ‖r.1 - Lp.const 2 Q a‖ := by
  have hc : ‖z.1 - r.1‖ ≤ holError z r := by
    dsimp [holError]
    linarith [norm_nonneg (z.2.1 - r.2.1), norm_nonneg (z.2.2.1 - r.2.2.1),
      norm_nonneg (z.2.2.2 - r.2.2.2)]
  exact (numerical_target_triangle Q _ _ a).trans (add_le_add hc (le_refl _))

end LpTriangle

section TargetData
variable {S A Z Y J : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype J]

/-- Primitive mean-field/target process data for the source parameter bound.
No relaxation, interaction or parameter-error estimate is a field. -/
structure StationaryParameterData (M : Model S A Z Y J) (D : TwistedGeometry S Z)
    (sbar : ℝ → S) (ν : ℝ → Measure Z) (ρ : ℝ) where
  projection : LipschitzWith 1 M.parameter
  tests : Set (Z → ℝ)
  pairTests : Set (Z × Z → ℝ)
  mean_solution : M.IsWeakSolution tests sbar ν
  sStar : S
  νStar : Measure Z
  frozen_stationary : M.FrozenStationary tests (M.parameter sStar) νStar
  gradient_integrable : Integrable
    (fun z ↦ M.observation (M.parameter sStar) (M.position z)) νStar
  gradient_zero : M.meanGradient νStar sStar = 0
  optimizer_fixed : ∀ r, 0 ≤ r → M.optimizer r sStar 0 = 0
  quadratic_test : couplingQuadratic D ∈ pairTests
  rate_positive : 0 < ρ
  joint_monotonicity : TwistedJointMonotonicity M D ρ
  realize : ∀ c : ULA.Coupling (ν 0) νStar,
    ∃ Λ : ℝ → Measure (Z × Z),
      SynchronousCouplingData M pairTests sbar (fun _ ↦ sStar) ν (fun _ ↦ νStar) Λ ∧
        Λ 0 = c.joint

/-- The continuous interaction-plus-relaxation budget has the exact source
constants. It contains no numerical or smoothing error. -/
def StationaryParameterData.continuousBudget
    {M : Model S A Z Y J} {D : TwistedGeometry S Z} {sbar : ℝ → S}
    {ν : ℝ → Measure Z} {ρ : ℝ} (T : StationaryParameterData M D sbar ν ρ)
    (LΨ : ℝ≥0) (V : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
    optimizerLawDistance (sbar 0) T.sStar (ν 0) T.νStar +
  ((LΨ : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
    (1 - Real.exp (-ρ * t))

/-- The compatible reference law transfers the actual source parameter
bound to the actual L² reference variable used by a numerical theorem. -/
theorem StationaryParameterData.reference_norm_bound
    {M : Model S A Z Y J} {D : TwistedGeometry S Z} {sbar : ℝ → S}
    {ν : ℝ → Measure Z} {ρ : ℝ} (T : StationaryParameterData M D sbar ν ρ)
    {N : ℕ} (hN : 0 < N) {LΨ : ℝ≥0} {V : ℝ} (hV : 0 ≤ V)
    (P : ParticleParameterApproximation M D N ν sbar LΨ V)
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (X : Lp A 2 Q) (t : ℝ) (ht : 0 ≤ t)
    (compatible : Q.map X = (P.jointLaw t).map (fun p ↦ M.parameter p.1.1)) :
    ‖X - Lp.const 2 Q (M.parameter T.sStar)‖ ≤ T.continuousBudget LΨ V N t := by
  have hf : AEMeasurable (fun p : ParticlePair N S Z ↦ M.parameter p.1.1) (P.jointLaw t) :=
    (T.projection.continuous.comp (continuous_fst.comp continuous_fst)).measurable.aemeasurable
  rw [lp_target_norm_eq_law_rms Q X (M.parameter T.sStar) (P.jointLaw t) _ hf compatible]
  exact P.parameter_bound T.projection T.tests T.pairTests T.mean_solution T.sStar T.νStar
    T.frozen_stationary T.gradient_integrable T.gradient_zero T.optimizer_fixed
    T.quadratic_test T.rate_positive T.joint_monotonicity T.realize hN hV t ht

end TargetData

section MomentumMethod
variable {Ω A X I : Type*} {N : ℕ} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q)
  (D : ParticleForceData A X (EuclideanSpace ℝ I) N)

/-- Actual raw finite-particle OBABO iterate with the proved Gaussian
thermostat innovations and a shared random optimiser. -/
def momentumParticleIterate (γ h : ℝ)
    (z : ((Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q) ×
      ((Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q)) (n : ℕ) :=
  trajectory (fun s r ↦ KineticLangevin.obaboStep
    (coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)) h
    (Real.exp (-γ * h / 2)) (Real.sqrt (1 - Real.exp (-γ * h))) s r.1 r.2)
    (momentumGaussianNoise (Θ := Lp A 2 Q) Q W hW h) z n

/-- The explicit proved finite-horizon M-MFPO discretisation budget. -/
def momentumDiscretizationBudget (γ h R P F : ℝ) (e0 : ℝ) (n : ℕ) : ℝ :=
  let L := coupledLipschitzConstant (D.meanLip : ℝ) (D.samplerForceLip : ℝ)
  Real.exp (momentumStabilityConstant L * h * n) *
    (e0 + (momentumLocalConsistencyConstant L γ P F (Real.sqrt (Fintype.card I : ℝ)) +
      Real.sqrt γ * Real.sqrt (Fintype.card I : ℝ) +
      (3 / 2 : ℝ) * γ * Real.sqrt γ * Real.sqrt (Fintype.card I : ℝ) +
      (2 / 3 : ℝ) * (L + γ + 1) * R) * (n * h) * Real.sqrt h)

/-- A compatible integral reference carries its original kinetic equations,
finite-grid moments and temporal modulus. No discretisation bound is a field. -/
structure MomentumIntegralReference (γ h R P F : ℝ) (n : ℕ) where
  friction_nonneg : 0 ≤ γ
  step_pos : 0 < h
  step_le_one : h ≤ 1
  modulus_nonneg : 0 ≤ R
  momentum_nonneg : 0 ≤ P
  force_nonneg : 0 ≤ F
  independent_paths : iIndepFun
    (fun i ω (j : ℕ) ↦ W i ((j : ℝ≥0) * (h / 2).toNNReal) ω) Q
  p : ℕ → ℝ → (Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q
  q : ℕ → ℝ → (Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q
  momentum_integrable : ∀ k, k < n → IntervalIntegrable (p k) volume 0 h
  force_integrable : ∀ k, k < n → IntervalIntegrable
    (fun t ↦ coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) (q k t) + γ • p k t) volume 0 h
  momentum_equation : ∀ k, k < n → p k h = p k 0 -
    (∫ t in 0..h, coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) (q k t) + γ • p k t) +
    momentumGaussianIncrement (Θ := Lp A 2 Q) Q W hW γ h k
  position_equation : ∀ k, k < n → q k h = q k 0 + (∫ t in 0..h, p k t)
  grid_compatible : ∀ k, k < n → p (k + 1) 0 = p k h ∧ q (k + 1) 0 = q k h
  modulus : ∀ k, k < n → ∀ t, t ∈ Icc 0 h →
    ‖p k t - p k 0‖ ≤ R * Real.sqrt t ∧ ‖q k t - q k 0‖ ≤ R * Real.sqrt t
  momentum_bound : ∀ k, k < n → ‖p k 0‖ ≤ P
  force_bound : ∀ k, k < n →
    ‖coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) (q k 0)‖ ≤ F

theorem MomentumIntegralReference.finite_bound
    {γ h R P F : ℝ} {n : ℕ} (Ref : MomentumIntegralReference Q W hW D γ h R P F n)
    (z : ((Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q) ×
      ((Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q)) :
    phaseError (momentumParticleIterate Q W hW D γ h z n) (Ref.p n 0, Ref.q n 0) ≤
      momentumDiscretizationBudget D γ h R P F (phaseError z (Ref.p 0 0, Ref.q 0 0)) n := by
  exact m_mfpo_particle_lp_gaussian_finite_bound Q W hW D γ h R P F
    Ref.friction_nonneg Ref.step_pos Ref.step_le_one Ref.modulus_nonneg
    Ref.momentum_nonneg Ref.force_nonneg Ref.independent_paths Ref.p Ref.q n
    Ref.momentum_integrable Ref.force_integrable Ref.momentum_equation Ref.position_equation
    Ref.grid_compatible Ref.modulus Ref.momentum_bound Ref.force_bound z

end MomentumMethod

section HigherOrderMethod
variable {A X : Type*} {N : ℕ}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  (I : Type*) [Fintype I] [DecidableEq I]
  (D : ParticleForceData A X (EuclideanSpace ℝ I) N)

/-- Actual finite-particle HOL-MYPGD Gaussian iterate. -/
def higherOrderParticleIterate (α γ : ℝ) (h : ℝ≥0)
    (z : HOLState (Lp A 2 (ULA.CanonicalBrownian.vectorProbability I)) (HOLGaussianSpace I))
    (n : ℕ) :=
  trajectory (higherOrderStep (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I))
    (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ h)
    (higherOrderGaussianNoise I α γ h) z n

/-- The explicit proved HOL finite-horizon discretisation budget. -/
def higherOrderDiscretizationBudget (α γ Fθ FG U V C : ℝ) (h : ℝ≥0) (e0 : ℝ) (n : ℕ) : ℝ :=
  Real.exp (holStabilityConstant α γ (D.meanLip : ℝ) (D.samplerForceLip : ℝ) * (h : ℝ) * n) *
    (e0 + (holLocalConsistencyConstant (holRemainderConstants α γ) (D.samplerForceLip : ℝ)
      Fθ FG U V + Real.sqrt (Fintype.card I : ℝ) * holScalarNoiseConstant α γ +
      (8 / 3 : ℝ) * C) * (n * (h : ℝ)) * Real.sqrt (h : ℝ))

/-- The compatible HOL integral reference and its finite-horizon regularity
assumptions. Its Brownian input is exactly the auxiliary-coordinate input. -/
structure HigherOrderIntegralReference (α γ Fθ FG U V C : ℝ) (h : ℝ≥0) (n : ℕ) where
  auxiliary_friction_pos : 0 < α
  momentum_coupling_nonneg : 0 ≤ γ
  step_pos : 0 < (h : ℝ)
  step_le_one : (h : ℝ) ≤ 1
  optimizer_force_nonneg : 0 ≤ Fθ
  sampler_force_nonneg : 0 ≤ FG
  first_auxiliary_nonneg : 0 ≤ U
  second_auxiliary_nonneg : 0 ≤ V
  modulus_nonneg : 0 ≤ C
  r : ℕ → ℝ → HOLState (Lp A 2 (ULA.CanonicalBrownian.vectorProbability I)) (HOLGaussianSpace I)
  drift_integrable : ∀ k, k < n → IntervalIntegrable
    (fun t ↦ holDrift (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I))
      (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ (r k t)) volume 0 h
  equation : ∀ k, k < n → r k h = r k 0 +
    (∫ t in 0..h, holDrift (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I))
      (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ (r k t)) +
    holBrownianIncrement (higherOrderGaussianIncrement I α γ h k)
  grid_compatible : ∀ k, k < n → r (k + 1) 0 = r k h
  drift_modulus : ∀ k, k < n → ∀ t, t ∈ Icc 0 (h : ℝ) →
    ‖holDrift (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I))
      (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ (r k t) -
      holDrift (D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I))
      (D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)) α γ (r k 0)‖ ≤ C * Real.sqrt t
  optimizer_force_bound : ∀ k, k < n →
    ‖D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I) (r k 0).1 (r k 0).2.1‖ ≤ Fθ
  sampler_force_bound : ∀ k, k < n →
    ‖D.samplerForceLp (ULA.CanonicalBrownian.vectorProbability I)
      ((r k 0).1 - (h : ℝ) • D.meanForceLp (ULA.CanonicalBrownian.vectorProbability I)
        (r k 0).1 (r k 0).2.1) (r k 0).2.1‖ ≤ FG
  first_auxiliary_bound : ∀ k, k < n → ‖(r k 0).2.2.1‖ ≤ U
  second_auxiliary_bound : ∀ k, k < n → ‖(r k 0).2.2.2‖ ≤ V

theorem HigherOrderIntegralReference.finite_bound
    {α γ Fθ FG U V C : ℝ} {h : ℝ≥0} {n : ℕ}
    (Ref : HigherOrderIntegralReference I D α γ Fθ FG U V C h n)
    (z : HOLState (Lp A 2 (ULA.CanonicalBrownian.vectorProbability I)) (HOLGaussianSpace I)) :
    holError (higherOrderParticleIterate I D α γ h z n) (Ref.r n 0) ≤
      higherOrderDiscretizationBudget I D α γ Fθ FG U V C h (holError z (Ref.r 0 0)) n := by
  exact hol_mypgd_particle_lp_gaussian_finite_bound I D α γ Fθ FG U V C h
    Ref.auxiliary_friction_pos Ref.momentum_coupling_nonneg Ref.step_pos Ref.step_le_one
    Ref.optimizer_force_nonneg Ref.sampler_force_nonneg Ref.first_auxiliary_nonneg
    Ref.second_auxiliary_nonneg Ref.modulus_nonneg Ref.r n Ref.drift_integrable Ref.equation
    Ref.grid_compatible Ref.drift_modulus Ref.optimizer_force_bound Ref.sampler_force_bound
    Ref.first_auxiliary_bound Ref.second_auxiliary_bound z

end HigherOrderMethod

section MomentumTarget
variable {Ω A X I S Z Y J : Type*} {N : ℕ} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype J]

/-- M-MFPO numerical parameter error to the actual stationary target:
proved discretisation + mean-field relaxation + finite-particle interaction.
The explicit compatible-law premise connects the integral reference used by
the numerical proof to the interacting-coordinate law used by the weak proof.
No strong-SDE/weak-law equivalence is silently asserted. -/
theorem m_mfpo_numerical_parameter_bound
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (D : ParticleForceData A X (EuclideanSpace ℝ I) N)
    {γ h R P F : ℝ} {n : ℕ} (Ref : MomentumIntegralReference Q W hW D γ h R P F n)
    (z : ((Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q) ×
      ((Lp A 2 Q) × Lp (EuclideanSpace ℝ I) 2 Q))
    {M : Model S A Z Y J} {G : TwistedGeometry S Z} {sbar : ℝ → S}
    {ν : ℝ → Measure Z} {ρ : ℝ} (Target : StationaryParameterData M G sbar ν ρ)
    (hN : 0 < N) {LΨ : ℝ≥0} {V : ℝ} (hV : 0 ≤ V)
    (Particle : ParticleParameterApproximation M G N ν sbar LΨ V)
    (compatible : Q.map (Ref.q n 0).1 =
      (Particle.jointLaw (n * h)).map (fun p ↦ M.parameter p.1.1)) :
    ‖(momentumParticleIterate Q W hW D γ h z n).2.1 -
        Lp.const 2 Q (M.parameter Target.sStar)‖ ≤
      momentumDiscretizationBudget D γ h R P F (phaseError z (Ref.p 0 0, Ref.q 0 0)) n +
      Target.continuousBudget LΨ V N (n * h) := by
  have hn := MomentumIntegralReference.finite_bound Q W hW D Ref z
  have hr := Target.reference_norm_bound hN hV Particle Q (Ref.q n 0).1 (n * h)
    (mul_nonneg (Nat.cast_nonneg n) Ref.step_pos.le) compatible
  exact (momentum_parameter_triangle Q _ (Ref.p n 0, Ref.q n 0)
    (M.parameter Target.sStar)).trans (add_le_add hn hr)

end MomentumTarget

section HigherOrderTarget
variable {A X I S Z Y J : Type*} {N : ℕ} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype J]

/-- HOL-MYPGD numerical parameter error to its actual surrogate stationary
target. The compatible-law equality is explicit; the original target may
require the separate bias term proved in the following theorem. -/
theorem hol_mypgd_numerical_parameter_bound
    (D : ParticleForceData A X (EuclideanSpace ℝ I) N)
    {α γ Fθ FG U V C : ℝ} {h : ℝ≥0} {n : ℕ}
    (Ref : HigherOrderIntegralReference I D α γ Fθ FG U V C h n)
    (z : HOLState (Lp A 2 (ULA.CanonicalBrownian.vectorProbability I)) (HOLGaussianSpace I))
    {M : Model S A Z Y J} {G : TwistedGeometry S Z} {sbar : ℝ → S}
    {ν : ℝ → Measure Z} {ρ : ℝ} (Target : StationaryParameterData M G sbar ν ρ)
    (hN : 0 < N) {LΨ : ℝ≥0} {Variance : ℝ} (hVariance : 0 ≤ Variance)
    (Particle : ParticleParameterApproximation M G N ν sbar LΨ Variance)
    (compatible : (ULA.CanonicalBrownian.vectorProbability I).map (Ref.r n 0).1 =
      (Particle.jointLaw (n * (h : ℝ))).map (fun p ↦ M.parameter p.1.1)) :
    ‖(higherOrderParticleIterate I D α γ h z n).1 -
        Lp.const 2 (ULA.CanonicalBrownian.vectorProbability I) (M.parameter Target.sStar)‖ ≤
      higherOrderDiscretizationBudget I D α γ Fθ FG U V C h (holError z (Ref.r 0 0)) n +
      Target.continuousBudget LΨ Variance N (n * (h : ℝ)) := by
  have hn := HigherOrderIntegralReference.finite_bound I D Ref z
  have hr := Target.reference_norm_bound hN hVariance Particle
    (ULA.CanonicalBrownian.vectorProbability I) (Ref.r n 0).1 (n * (h : ℝ))
    (by positivity) compatible
  exact (higherOrder_parameter_triangle (ULA.CanonicalBrownian.vectorProbability I)
    _ (Ref.r n 0) (M.parameter Target.sStar)).trans (add_le_add hn hr)

/-- HOL numerical error to the original target includes the actual
surrogate-target bias L ε/m. This term is derived from a genuine coupled
pair of target sampler variables, the original gradient identity and strong
monotonicity; neither equality of the two targets nor a smoothing radius is
assumed without its explicit coupling premise. -/
theorem hol_mypgd_original_parameter_bound
    (D : ParticleForceData A X (EuclideanSpace ℝ I) N)
    {α γ Fθ FG U V C : ℝ} {h : ℝ≥0} {n : ℕ}
    (Ref : HigherOrderIntegralReference I D α γ Fθ FG U V C h n)
    (z : HOLState (Lp A 2 (ULA.CanonicalBrownian.vectorProbability I)) (HOLGaussianSpace I))
    {M : Model S A Z Y J} {G : TwistedGeometry S Z} {sbar : ℝ → S}
    {ν : ℝ → Measure Z} {ρ : ℝ} (Target : StationaryParameterData M G sbar ν ρ)
    (hN : 0 < N) {LΨ : ℝ≥0} {Variance : ℝ} (hVariance : 0 ≤ Variance)
    (Particle : ParticleParameterApproximation M G N ν sbar LΨ Variance)
    (compatible : (ULA.CanonicalBrownian.vectorProbability I).map (Ref.r n 0).1 =
      (Particle.jointLaw (n * (h : ℝ))).map (fun p ↦ M.parameter p.1.1))
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (g : A → A) (f : B → A) (L : ℝ≥0) (hf : LipschitzWith L f)
    (m ε : ℝ) (hm : 0 < m) (star : A) (hstar : g star = 0)
    (hmono : m * ‖M.parameter Target.sStar - star‖ ^ 2 ≤
      ⟪M.parameter Target.sStar - star, g (M.parameter Target.sStar) - g star⟫_ℝ)
    (Xoriginal Xsurrogate : Lp B 2 (ULA.CanonicalBrownian.vectorProbability I))
    (hgradient : g (M.parameter Target.sStar) =
      ∫ ω, f (Xoriginal ω) ∂(ULA.CanonicalBrownian.vectorProbability I))
    (hsurrogate : (∫ ω, f (Xsurrogate ω) ∂(ULA.CanonicalBrownian.vectorProbability I)) = 0)
    (hcoupling : ‖Xoriginal - Xsurrogate‖ ≤ ε) :
    ‖(higherOrderParticleIterate I D α γ h z n).1 -
        Lp.const 2 (ULA.CanonicalBrownian.vectorProbability I) star‖ ≤
      higherOrderDiscretizationBudget I D α γ Fθ FG U V C h (holError z (Ref.r 0 0)) n +
      Target.continuousBudget LΨ Variance N (n * (h : ℝ)) + (L : ℝ) * ε / m := by
  have hn := hol_mypgd_numerical_parameter_bound D Ref z Target hN hVariance Particle compatible
  have hb := hybrid_target_bias (ULA.CanonicalBrownian.vectorProbability I) g f L hf m ε hm
    (M.parameter Target.sStar) star hstar hmono Xoriginal Xsurrogate hgradient hsurrogate hcoupling
  exact (numerical_target_shift (ULA.CanonicalBrownian.vectorProbability I) _
    (M.parameter Target.sStar) star).trans (add_le_add hn hb)

end HigherOrderTarget
end PBGSO
