import PBGSO.RawConstructedParticleCopy
import PBGSO.RawParticleInteraction

/-! Sharp source particle bound for the actual original empirical equation.
The reference cloud, common driver, physical coefficients, and iid law are
constructed from one original mean-field trajectory. Only an actual original
interacting strong solution is supplied, as in the source theorem. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawConstructedParticleBounds
open FilteredBrownian ConstructedItoParticle RawConstructedParticleCopy
variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (M : Model S Θ Z X I) (N : ℕ) {T : ℝ≥0}
  (U : RawLocalStationarity.Data Q D M T)
  (Y : RawEmpiricalDynamics.Solution M N
    (IndependentCopies.seeds (J := Fin N) Q) (RawIndependentCopies.driver Q D N) T)

/-- Literal original interacting state and independently seeded references. -/
def originalPair (r : ℝ) (ω : Fin N → Ω) : ParticlePair N S Z :=
  (oneEquiv N (Y.state r ω),(U.optimizer r,RawIndependentCopies.cloud Q D N U r ω))

variable (A : Construction Q D M N U Y)

theorem pair_state : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
    ∀ r ∈ Icc 0 (T : ℝ), pairEquiv N (A.data.state r ω) = originalPair Q D M N U Y r ω := by
  filter_upwards [A.interacting_state,A.reference_state] with ω hI hR r hr
  exact Prod.ext (hI r hr) (hR r hr)

theorem reference_cloud_law (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    (IndependentCopies.seeds (J := Fin N) Q).map
      (fun ω => (pairEquiv N (A.data.state r ω)).2.2) =
      Measure.pi (fun _ : Fin N => referenceLaw Q D M U r) := by
  rw [Measure.map_congr (A.reference_state.mono (fun ω h => congrArg Prod.snd (h r hr))),
    RawIndependentCopies.cloud_law Q D N U r hr,referenceLaw_eq Q D M U r hr]

theorem reference_optimizer (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      (pairEquiv N (A.data.state r ω)).2.1 = U.optimizer r :=
  A.reference_state.mono (fun _ h => congrArg Prod.fst (h r hr))

theorem initial_coupling
    (hinit : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      oneEquiv N (Y.state 0 ω) = (U.optimizer 0,RawIndependentCopies.cloud Q D N U 0 ω)) :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      (pairEquiv N (A.data.state 0 ω)).1 = (pairEquiv N (A.data.state 0 ω)).2 := by
  filter_upwards [A.interacting_state,A.reference_state,hinit] with ω hI hR h0
  rw [hI 0 ⟨le_rfl,T.coe_nonneg⟩,hR 0 ⟨le_rfl,T.coe_nonneg⟩,h0]

include A in
/-- Exact source3 bound for the original empirical SDE. The final distance
uses the original native trajectory and constructed iid reference copies;
no raw paired equation or reference-law compatibility is an input. -/
theorem finite_particle_interaction_bound
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g-M.optimizer t s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (hF : ∀ t ∈ Icc 0 (T : ℝ), MemLp
      (fun z => M.observation (M.parameter (U.optimizer t)) (M.position z)) 2
      (Q.map (U.sampler.state t)))
    (hVar : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer t)) (M.position z)-
        M.meanGradient (Q.map (U.sampler.state t)) (U.optimizer t)‖^2
          ∂Q.map (U.sampler.state t)) ≤ V)
    (hinit : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      oneEquiv N (Y.state 0 ω) = (U.optimizer 0,RawIndependentCopies.cloud Q D N U 0 ω)) :
    Real.sqrt (∫ ω, particleEmpiricalDistanceSq N (originalPair Q D M N U Y T ω)
      ∂IndependentCopies.seeds (J := Fin N) Q) ≤
      ((LΨ : ℝ)/ρ)*Real.sqrt (G.conditionNumber*V/(N : ℝ))*(1-Real.exp (-ρ*T)) := by
  have hF' : ∀ t ∈ Icc 0 (T : ℝ), MemLp
      (fun z => M.observation (M.parameter (U.optimizer t)) (M.position z)) 2
      (referenceLaw Q D M U t) := by
    intro t ht
    rw [referenceLaw_eq Q D M U t ht]
    exact hF t ht
  have hVar' : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer t)) (M.position z)-
        M.meanGradient (referenceLaw Q D M U t) (U.optimizer t)‖^2
          ∂referenceLaw Q D M U t) ≤ V := by
    intro t ht
    rw [referenceLaw_eq Q D M U t ht]
    exact hVar t ht
  have h := A.data.finite_particle_interaction_bound G ρ hρ hmono hN LΨ V hV U.optimizer
    hΨ hF' (reference_cloud_law Q D M N U Y A) (reference_optimizer Q D M N U Y A)
    hVar' (initial_coupling Q D M N U Y A hinit)
  have he : (fun ω => particleEmpiricalDistanceSq N (pairEquiv N (A.data.state T ω))) =ᵐ[
      IndependentCopies.seeds (J := Fin N) Q]
      (fun ω => particleEmpiricalDistanceSq N (originalPair Q D M N U Y T ω)) :=
    (pair_state Q D M N U Y A).mono (fun _ h => congrArg (particleEmpiricalDistanceSq N)
      (h T ⟨T.coe_nonneg,le_rfl⟩))
  rwa [integral_congr_ae he] at h

omit A in
/-- Source3 with the paired construction instantiated internally from the
original interacting equation and primitive Borel model fields. -/
theorem original_finite_particle_interaction_bound
    (hBorelF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hBorelb : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hBorelΨ : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2))
    (G : TwistedGeometry S Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M G ρ) (hN : 0 < N)
    (LΨ : ℝ≥0) (V : ℝ) (hV : 0 ≤ V)
    (hΨ : ∀ t ∈ Icc 0 (T : ℝ), ∀ s g g',
      ‖M.optimizer t s g-M.optimizer t s g'‖ ≤ (LΨ : ℝ)*‖g-g'‖)
    (hF : ∀ t ∈ Icc 0 (T : ℝ), MemLp
      (fun z => M.observation (M.parameter (U.optimizer t)) (M.position z)) 2
      (Q.map (U.sampler.state t)))
    (hVar : ∀ t ∈ Icc 0 (T : ℝ),
      (∫ z, ‖M.observation (M.parameter (U.optimizer t)) (M.position z)-
        M.meanGradient (Q.map (U.sampler.state t)) (U.optimizer t)‖^2
          ∂Q.map (U.sampler.state t)) ≤ V)
    (hinit : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      oneEquiv N (Y.state 0 ω) = (U.optimizer 0,RawIndependentCopies.cloud Q D N U 0 ω)) :
    Real.sqrt (∫ ω, particleEmpiricalDistanceSq N (originalPair Q D M N U Y T ω)
      ∂IndependentCopies.seeds (J := Fin N) Q) ≤
      ((LΨ : ℝ)/ρ)*Real.sqrt (G.conditionNumber*V/(N : ℝ))*(1-Real.exp (-ρ*T)) :=
  finite_particle_interaction_bound Q D M N U Y
    (RawConstructedParticleCopy.build Q D M N U Y hBorelF hBorelb hBorelΨ)
    G ρ hρ hmono hN LΨ V hV hΨ hF hVar hinit

end PBGSO.RawConstructedParticleBounds
