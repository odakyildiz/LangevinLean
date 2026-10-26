import PBGSO.ParticleAdditiveWeakRealization
import PBGSO.AdditiveStationaryTarget
import PBGSO.ParameterLawTransfer

/-! # Parameter bounds for actually constructed additive particle processes

The full interacting trajectory and independent reference cloud are built
from primitive globally Lipschitz maps. Their quadratic generator, iid law,
zero initial separation and parameter-law transfer are conclusions. The
stationary-target specialization uses an actual frozen invariant trajectory;
it assumes neither an all-couplings realizer nor output-law compatibility.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace PBGSO

section Realization
variable {Ω S A Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (L : LipschitzDynamics S Z A) (M : Model S A Z X I)
  (D : TwistedGeometry S Z) (N : ℕ) (hN : 0 < N)
  (Ybar : ℝ → S × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q) (V : ℝ)

/-- Actual additive particle trajectory together with the process data
proved from that trajectory. Its paired law is a field identity proved by
the constructor, not a law-compatibility premise of the error theorem. -/
structure AdditiveParticleRealization where
  state : ℝ → Lp (S × (Fin N → Z)) 2 (IndependentCopies.seeds (J := Fin N) Q)
  continuous : Continuous state
  initial : state 0 = independentReferenceCLM (A := S) (Z := Z) Q N (Ybar 0)
  equation : ∀ t, 0 ≤ t → state t - state 0 =
    (∫ r in 0..t, ULA.lpDrift (IndependentCopies.seeds Q) (L.particleField N)
      (L.particleField_lipschitz N hN) (state r)) +
    independentReferenceCLM (A := S) (Z := Z) Q N (0, B t)
  approximation : ParticleParameterApproximation M D N (fun t ↦ Q.map (Ybar t).2)
    (fun t ↦ (Ybar t).1) L.responseLip V
  paired_law : approximation.jointLaw = fun t ↦ particlePairLaw (IndependentCopies.seeds Q) N
    (state t) (independentReferenceCLM (A := S) (Z := Z) Q N (Ybar t))

/-- All fields of the particle realization follow from the actual integral
construction and the primitive uniform observation-variance assumption. -/
def additiveParticleRealization (H : AdditiveModelCompatibility L M)
    (HY : IsGlobalAdditiveIntegralSolution Q L Ybar B)
    (hB : Continuous B) (hB0 : B 0 = 0)
    (hVariance : ∀ r, 0 ≤ r →
      (∫ z, ‖M.observation (M.parameter (Ybar r).1) (M.position z) -
        M.meanGradient (Q.map (Ybar r).2) (Ybar r).1‖ ^ 2 ∂Q.map (Ybar r).2) ≤ V) :
    AdditiveParticleRealization Q L M D N hN Ybar B V :=
  Classical.choice (by
    obtain ⟨Y, hc, hi, he, P, hp⟩ := exists_additive_particle_approximation
      Q N L M H hN D Ybar B HY hB hB0 V hVariance
    exact ⟨⟨Y, hc, hi, he, P, hp⟩⟩)

namespace AdditiveParticleRealization
variable {Q L M D N hN Ybar B V}
  (R : AdditiveParticleRealization Q L M D N hN Ybar B V)

/-- The actual model parameter coordinate of the shared random optimiser. -/
def parameter (hparam : LipschitzWith 1 M.parameter) (t : ℝ) :
    Lp A 2 (IndependentCopies.seeds (J := Fin N) Q) :=
  liftMap (IndependentCopies.seeds Q) M.parameter hparam
    (particleOptimizerLp (A := S) (Z := Z) (IndependentCopies.seeds Q) N (R.state t))

/-- The law identity required by the numerical/source interface is derived
from the actual L² projection and the actual constructed paired law. -/
theorem parameter_law (hparam : LipschitzWith 1 M.parameter) (t : ℝ) :
    (IndependentCopies.seeds (J := Fin N) Q).map (R.parameter hparam t) =
      (R.approximation.jointLaw t).map (fun p ↦ M.parameter p.1.1) := by
  rw [R.paired_law]
  have hp : particleOptimizerLp (A := S) (Z := Z) (IndependentCopies.seeds Q) N (R.state t) =
      (ContinuousLinearMap.fst ℝ S (Fin N → Z)).compLp (R.state t) := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.fst ℝ S (Fin N → Z)).coeFn_compLpL (R.state t),
      (ContinuousLinearMap.fst ℝ S (Fin N → Z)).coeFn_compLp (R.state t)] with ω h1 h2
    exact h1.trans h2.symm
  unfold parameter
  rw [hp]
  exact ParameterLawTransfer.optimizer_parameter_law (IndependentCopies.seeds (J := Fin N) Q)
    M hparam (R.state t) (independentReferenceCLM (A := S) (Z := Z) Q N (Ybar t))

/-- The source parameter bound applies to the actual random parameter
coordinate. No output-law identity, particle weak equation, iid reference
law, residual-measurability or initial-energy premise remains here. -/
theorem parameter_bound {ρ : ℝ}
    (Target : StationaryParameterData M D (fun t ↦ (Ybar t).1)
      (fun t ↦ Q.map (Ybar t).2) ρ)
    (hV : 0 ≤ V) (t : ℝ) (ht : 0 ≤ t) :
    ‖R.parameter Target.projection t -
      Lp.const 2 (IndependentCopies.seeds (J := Fin N) Q) (M.parameter Target.sStar)‖ ≤
        Target.continuousBudget L.responseLip V N t := by
  exact Target.reference_norm_bound hN hV R.approximation
    (IndependentCopies.seeds Q) (R.parameter Target.projection t) t ht
    (R.parameter_law Target.projection t)

end AdditiveParticleRealization
end Realization
namespace AdditiveConstructed
variable {Ξ S A Z X I : Type*} [MeasurableSpace Ξ]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (R : Measure Ξ) [IsProbabilityMeasure R]
  (L : LipschitzDynamics S Z A) (M : Model S A Z X I)
  (H : AdditiveModelCompatibility L M) (D : TwistedGeometry S Z)
  (μ : Measure Z) [IsProbabilityMeasure μ] (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : S)
  (B : ℝ → Lp Z 2 R) (hB : Continuous B) (hB0 : B 0 = 0)
  (N : ℕ) (hN : 0 < N) (V : ℝ)
  (hVariance : ∀ r, 0 ≤ r →
    (∫ z, ‖M.observation
      (M.parameter (AdditiveCanonical.optimizer R L μ hμ a B hB hB0 r)) (M.position z) -
      M.meanGradient (AdditiveCanonical.law R L μ hμ a B hB hB0 r)
        (AdditiveCanonical.optimizer R L μ hμ a B hB hB0 r)‖ ^ 2
      ∂AdditiveCanonical.law R L μ hμ a B hB hB0 r) ≤ V)

/-- Actual finite-particle realization of the canonical mean-field process
on independent complete initial/noise seeds. Existence is fully constructed. -/
def particleRealization : AdditiveParticleRealization (μ.prod R) L M D N hN
    (AdditiveCanonical.flow R L μ hμ a B hB hB0) (AdditiveCanonical.input R μ B) V :=
  additiveParticleRealization (μ.prod R) L M D N hN
    (AdditiveCanonical.flow R L μ hμ a B hB hB0) (AdditiveCanonical.input R μ B) V H
    (AdditiveCanonical.flow_spec R L μ hμ a B hB hB0).1
    ((lpPullbackCLM (measurePreserving_snd (μ := μ) (ν := R))).continuous.comp hB)
    (by simp [AdditiveCanonical.input, hB0]) hVariance

/-- Source Theorem 4 for actual constructed additive dynamics, with every
process/law compatibility premise discharged. Frozen invariance is supplied
as the source's actual stationary sampler trajectory, and the variance and
joint-monotonicity assumptions remain explicit primitive hypotheses. -/
theorem parameter_bound
    (νStar : Measure Z) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : Z ↦ z) 2 νStar) (aStar : S)
    (Frozen : AdditiveStationary.FrozenTrajectory R L νStar hνStar aStar B)
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity M D ρ)
    (hparam : LipschitzWith 1 M.parameter)
    (hg : M.meanGradient νStar aStar = 0)
    (hfix : ∀ t, 0 ≤ t → M.optimizer t aStar 0 = 0)
    (hV : 0 ≤ V) (t : ℝ) (ht : 0 ≤ t) :
    ‖(particleRealization R L M H D μ hμ a B hB hB0 N hN V hVariance).parameter hparam t -
      Lp.const 2 (IndependentCopies.seeds (J := Fin N) (μ.prod R)) (M.parameter aStar)‖ ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) * optimizerLawDistance a aStar μ νStar +
      ((L.responseLip : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * t)) := by
  let T := AdditiveStationary.stationaryParameterData R L M H νStar hνStar aStar B hB hB0
    Frozen D ρ hρ hmono hparam hg hfix μ hμ a
  let P := particleRealization R L M H D μ hμ a B hB hB0 N hN V hVariance
  have h := P.parameter_bound T hV t ht
  have hs : T.sStar = aStar := rfl
  have hν : T.νStar = νStar := rfl
  have hopt : AdditiveCanonical.optimizer R L μ hμ a B hB hB0 0 = a :=
    congrArg Prod.fst (AdditiveCanonical.flow_spec R L μ hμ a B hB hB0).2
  have hb : T.continuousBudget L.responseLip V N t =
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) * optimizerLawDistance a aStar μ νStar +
      ((L.responseLip : ℝ) / ρ) * Real.sqrt (D.conditionNumber * V / (N : ℝ)) *
        (1 - Real.exp (-ρ * t)) := by
    simp only [StationaryParameterData.continuousBudget, hs, hν, hopt,
      AdditiveCanonical.law_zero]
  have hfinal := h.trans_eq hb
  simpa only [hs] using hfinal

end AdditiveConstructed
end PBGSO
