import PBGSO.EmpiricalMetric
import PBGSO.MethodLpEquivalences
import PBGSO.ParticleAdditiveWeakRealization

/-! # Source metrics constructed on actual numerical L² coordinates
The empirical A3 coupling is transported by proved inverse implementation
maps. All norm comparisons and random-state drift dissipation are conclusions.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory Set
open scoped NNReal BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.ImplementationMetric
open Methods ImplementationDynamics ConstructedItoParticle

section PhysicalField
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X] [Fintype I] [DecidableEq I]

/-- Complete physical drift identity from primitive model compatibility. -/
theorem physical_drift_of_compatibility (N : ℕ) (L : LipschitzDynamics S Z Θ)
    (M : Model S Θ Z X I) (H : AdditiveModelCompatibility L M)
    (t : ℝ) (ht : 0≤t) (p : S × (Fin N → Z)) :
    (oneEquiv N).symm (L.particleField N p)=
      RawEmpiricalDynamics.drift M N t ((oneEquiv N).symm p) := by
  apply (oneEquiv N).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,RawEmpiricalDynamics.drift_coordinates,
    ContinuousLinearEquiv.apply_symm_apply]
  exact (additive_particle_field N L M H t ht p).symm
end PhysicalField

section ActualCoordinates
variable {Ω A C X I : Type*} {N : ℕ} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : ParticleForceData A X C N)

/-- Actual kinetic drift packing on the shared probability space. -/
theorem momentum_drift_ae (γ : ℝ) (σ : I → HypocoercivePhase X)
    (z : (Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) :
    momentumPhysicalLpEquiv Q D
      (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2-γ • z.1,z.1) =ᵐ[Q]
      fun ω => RawEmpiricalDynamics.drift (heavyBallModel γ D.F D.G σ) N 0
        (momentumPhysicalLpEquiv Q D z ω) := by
  let E := oneEquiv (S := HypocoercivePhase A) (Z := HypocoercivePhase X) N
  let L := momentumForceDynamics D γ
  have hcompat : AdditiveModelCompatibility L (heavyBallModel γ D.F D.G σ) :=
    momentum_compatibility D.F D.G D.parameterLip D.samplerLip D.parameter_bound D.sampler_bound γ σ
  change E.symm.toContinuousLinearMap.compLpL 2 Q
      (momentumPackLp Q D (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) z.2-γ • z.1,z.1)) =ᵐ[Q]
      fun ω => RawEmpiricalDynamics.drift (heavyBallModel γ D.F D.G σ) N 0
        (E.symm.toContinuousLinearMap.compLpL 2 Q (momentumPackLp Q D z) ω)
  rw [momentumPackLp_drift]
  filter_upwards [E.symm.toContinuousLinearMap.coeFn_compLpL
      (ULA.lpDrift Q (L.particleField N) (L.particleField_lipschitz N D.nonempty) (momentumPackLp Q D z)),
    ULA.lpDrift_coe Q (L.particleField N) (L.particleField_lipschitz N D.nonempty) (momentumPackLp Q D z),
    E.symm.toContinuousLinearMap.coeFn_compLpL (momentumPackLp Q D z)] with ω he hf hx
  rw [he,hf,hx]
  exact physical_drift_of_compatibility N L (heavyBallModel γ D.F D.G σ) hcompat 0 le_rfl _

/-- Actual complete HOL drift packing, including both auxiliaries. -/
theorem higherOrder_drift_ae (α γ : ℝ) (σ : I → X)
    (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    higherOrderPhysicalLpEquiv Q D (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ z) =ᵐ[Q]
      fun ω => RawEmpiricalDynamics.drift (higherOrderModel D.F D.G α γ σ) N 0
        (higherOrderPhysicalLpEquiv Q D z ω) := by
  let E := oneEquiv (S := A) (Z := HigherOrderSampler X) N
  let L := higherOrderForceDynamics D α γ
  have hcompat : AdditiveModelCompatibility L (higherOrderModel D.F D.G α γ σ) :=
    higherOrder_compatibility D.F D.G D.parameterLip D.samplerLip D.parameter_bound D.sampler_bound α γ σ
  change E.symm.toContinuousLinearMap.compLpL 2 Q
      (higherOrderPackLp Q D (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ z)) =ᵐ[Q]
      fun ω => RawEmpiricalDynamics.drift (higherOrderModel D.F D.G α γ σ) N 0
        (E.symm.toContinuousLinearMap.compLpL 2 Q (higherOrderPackLp Q D z) ω)
  rw [higherOrderPackLp_drift]
  filter_upwards [E.symm.toContinuousLinearMap.coeFn_compLpL
      (ULA.lpDrift Q (L.particleField N) (L.particleField_lipschitz N D.nonempty) (higherOrderPackLp Q D z)),
    ULA.lpDrift_coe Q (L.particleField N) (L.particleField_lipschitz N D.nonempty) (higherOrderPackLp Q D z),
    E.symm.toContinuousLinearMap.coeFn_compLpL (higherOrderPackLp Q D z)] with ω he hf hx
  rw [he,hf,hx]
  exact physical_drift_of_compatibility N L (higherOrderModel D.F D.G α γ σ) hcompat 0 le_rfl _

/-- Source A3 constructs the actual M-MFPO metric and proves dissipativity
of its random-state drift. No additional L² monotonicity is required. -/
theorem momentum_metric [FiniteDimensional ℝ A] [FiniteDimensional ℝ X]
    (γ : ℝ) (σ : I → HypocoercivePhase X)
    (G : TwistedGeometry (HypocoercivePhase A) (HypocoercivePhase X)) (ρ : ℝ)
    (hmono : TwistedJointMonotonicity (heavyBallModel γ D.F D.G σ) G ρ) :
    ∃ n : ℕ, ∃ T : ((Lp A 2 Q × Lp C 2 Q) × (Lp A 2 Q × Lp C 2 Q)) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin n)) 2 Q,
      (∀ x, (Real.sqrt (EmpiricalMetric.lower N G)/
        (‖(momentumPhysicalLpEquiv Q D).symm.toContinuousLinearMap‖+1))*‖x‖≤‖T x‖) ∧
      (∀ x, ‖T x‖≤(Real.sqrt (EmpiricalMetric.upper N G)*
        ‖(momentumPhysicalLpEquiv Q D).toContinuousLinearMap‖)*‖x‖) ∧
      (∀ x y, ⟪T (x-y),T ((-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) x.2-γ • x.1,x.1)-
        (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) y.2-γ • y.1,y.1))⟫_ℝ ≤ -ρ*‖T (x-y)‖^2) :=
  EmpiricalMetric.exists_transported_metric Q (momentumPhysicalLpEquiv Q D)
    (heavyBallModel γ D.F D.G σ) G ρ hmono D.nonempty 0 le_rfl
    (fun x => (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) x.2-γ • x.1,x.1))
    (momentum_drift_ae Q D γ σ)

/-- Source A3 constructs the analogous metric for actual HOL coordinates. -/
theorem higherOrder_metric [FiniteDimensional ℝ A] [FiniteDimensional ℝ X]
    (α γ : ℝ) (σ : I → X)
    (G : TwistedGeometry A (HigherOrderSampler X)) (ρ : ℝ)
    (hmono : TwistedJointMonotonicity (higherOrderModel D.F D.G α γ σ) G ρ) :
    ∃ n : ℕ, ∃ T : HOLState (Lp A 2 Q) (Lp C 2 Q) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin n)) 2 Q,
      (∀ x, (Real.sqrt (EmpiricalMetric.lower N G)/
        (‖(higherOrderPhysicalLpEquiv Q D).symm.toContinuousLinearMap‖+1))*‖x‖≤‖T x‖) ∧
      (∀ x, ‖T x‖≤(Real.sqrt (EmpiricalMetric.upper N G)*
        ‖(higherOrderPhysicalLpEquiv Q D).toContinuousLinearMap‖)*‖x‖) ∧
      (∀ x y, ⟪T (x-y),T (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ x-
        holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ y)⟫_ℝ ≤ -ρ*‖T (x-y)‖^2) :=
  EmpiricalMetric.exists_transported_metric Q (higherOrderPhysicalLpEquiv Q D)
    (higherOrderModel D.F D.G α γ σ) G ρ hmono D.nonempty 0 le_rfl
    (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ)
    (higherOrder_drift_ae Q D α γ σ)
end ActualCoordinates
end PBGSO.ImplementationMetric
