import PBGSO.FullyConstructedMomentum
import PBGSO.MomentumUniformParticle
import PBGSO.MethodMetricComparisons
import PBGSO.UniformStepSize

/-! # Fully constructed time-uniform M-MFPO target guarantee
The source joint monotonicity builds the contracting empirical metric.
Primitive force regularity, actual Gaussian coupling and Picard integral
solutions derive uniform moments, local defects and numerical stability.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace
namespace PBGSO.FullyUniformMomentum
open Methods ImplementationDynamics FullyConstructedMomentum

variable {A J : Type*} {N : ℕ} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)
  (γ : ℝ)

variable
  (Geometry : TwistedGeometry (HypocoercivePhase A) (HypocoercivePhase (EuclideanSpace ℝ J)))
  (μ : Measure (HypocoercivePhase (EuclideanSpace ℝ J))) [IsProbabilityMeasure μ]
  (hμ : MemLp (fun z : HypocoercivePhase (EuclideanSpace ℝ J) ↦ z) 2 μ)
  (a : HypocoercivePhase A) (Variance : ℝ)
  (hVariance : ∀ r, 0 ≤ r →
    (∫ z, ‖(model D γ).observation
      ((model D γ).parameter (AdditiveCanonical.optimizer (ULA.CanonicalBrownian.vectorProbability J)
        (momentumForceDynamics D γ) μ hμ a (input γ) (input_continuous γ) (input_zero γ) r))
      ((model D γ).position z) -
      (model D γ).meanGradient (AdditiveCanonical.law (ULA.CanonicalBrownian.vectorProbability J)
        (momentumForceDynamics D γ) μ hμ a (input γ) (input_continuous γ) (input_zero γ) r)
        (AdditiveCanonical.optimizer (ULA.CanonicalBrownian.vectorProbability J) (momentumForceDynamics D γ)
          μ hμ a (input γ) (input_continuous γ) (input_zero γ) r)‖ ^ 2
      ∂AdditiveCanonical.law (ULA.CanonicalBrownian.vectorProbability J) (momentumForceDynamics D γ)
        μ hμ a (input γ) (input_continuous γ) (input_zero γ) r) ≤ Variance)

/-- Coercivity of the constructed source metric in raw kinetic coordinates. -/
def metricCoercivity : ℝ := Real.sqrt (EmpiricalMetric.lower N Geometry) / 2

/-- Data-only upper norm bound for the constructed metric factor. -/
def metricUpper : ℝ := 2 * Real.sqrt (EmpiricalMetric.upper N Geometry)

/-- Actual Brownian increment radius, with the given nonnegative friction. -/
def noiseRadius (hγ : 0 ≤ γ) : ℝ :=
  momentumUniformBrownianRadius (I := Fin N × J) ⟨γ, hγ⟩

/-- State-independent part of the proved OBABO local Gaussian error. -/
def localConstant0 (hγ : 0 ≤ γ) : ℝ :=
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  (momentumUniformDefect (momentumUniformForceLip D) ⟨γ, hγ⟩
    ‖coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) 0‖
    (Real.sqrt (Fintype.card (Fin N × J) : ℝ)) (noiseRadius (N := N) (J := J) γ hγ)).1

/-- Linear initial-state part of the proved OBABO local Gaussian error. -/
def localConstant1 (hγ : 0 ≤ γ) : ℝ :=
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  (momentumUniformDefect (momentumUniformForceLip D) ⟨γ, hγ⟩
    ‖coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) 0‖
    (Real.sqrt (Fintype.card (Fin N × J) : ℝ)) (noiseRadius (N := N) (J := J) γ hγ)).2

/-- Explicit one-unit exact kinetic radius when started at zero. -/
def zeroStartRadius (hγ : 0 ≤ γ) : ℝ :=
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  let γnn : ℝ≥0 := ⟨γ, hγ⟩
  UniformIntegral.radius (momentumUniformForceLip D + γnn + 1)
    ‖coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) 0‖
    (noiseRadius (N := N) (J := J) γ hγ) 0

/-- Data-only transformed zero-start radius `S`. -/
def zeroStartMoment (hγ : 0 ≤ γ) : ℝ :=
  metricUpper (N := N) Geometry * zeroStartRadius D γ μ hγ

/-- Uniform exact-reference radius, derived by contraction and unit restarts. -/
def referenceRadius (hγ : 0 ≤ γ) (ρ : ℝ) : ℝ :=
  let S := zeroStartMoment D γ Geometry μ hγ
  metricUpper (N := N) Geometry * ‖initial D γ Geometry μ hμ a Variance hVariance‖ +
    S / (1 - Real.exp (-ρ)) + S

/-- Linear-radius coefficient absorbed by exact-flow dissipation. -/
def radiusGrowth (hγ : 0 ≤ γ) : ℝ :=
  metricUpper (N := N) Geometry * localConstant1 D γ μ hγ / metricCoercivity (N := N) Geometry

/-- Explicit time-uniform numerical coefficient, independent of `h,n`. -/
def discretizationConstant (hγ : 0 ≤ γ) (ρ : ℝ) : ℝ :=
  4 * (metricUpper (N := N) Geometry * localConstant0 D γ μ hγ +
    radiusGrowth D γ Geometry μ hγ * referenceRadius D γ Geometry μ hμ a Variance hVariance hγ ρ) /
      (ρ * metricCoercivity (N := N) Geometry)

/-- Explicit positive upper step size; `hγ` only forms the physical friction. -/
def maximumStep (hγ : 0 ≤ γ) (ρ : ℝ) : ℝ :=
  UniformStep.maximumStep ρ (radiusGrowth D γ Geometry μ hγ)

/-- Positivity and both uniform bounds for the explicit data-defined constants. -/
theorem explicit_guarantee
    (hcloud : D.cloud = euclideanParticleEncoding N J) (hγ : 0 ≤ γ)
    (star : A) (νStar : Measure (HypocoercivePhase (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HypocoercivePhase (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (momentumForceDynamics D γ) νStar hνStar (targetState star) (input γ))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (model D γ) Geometry ρ)
    (hg : (model D γ).meanGradient νStar (targetState star) = 0)
    (hV : 0 ≤ Variance) :
    0 < maximumStep D γ Geometry μ hγ ρ ∧
      0 ≤ discretizationConstant D γ Geometry μ hμ a Variance hVariance hγ ρ ∧
      ∀ h : ℝ, 0 < h → h ≤ maximumStep D γ Geometry μ hγ ρ → ∀ n : ℕ,
        (‖momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          D γ h (initial D γ Geometry μ hμ a Variance hVariance) n -
          momentumUnpackLp (ParticleNoiseSpace.probability (J := J) μ N) D
            ((particles D γ Geometry μ hμ a Variance hVariance).state (n*h))‖ ≤ discretizationConstant D γ Geometry μ hμ a Variance hVariance hγ ρ * Real.sqrt h) ∧
        ‖(momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          D γ h (initial D γ Geometry μ hμ a Variance hVariance) n).2.1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) star‖ ≤
        discretizationConstant D γ Geometry μ hμ a Variance hVariance hγ ρ * Real.sqrt h +
        (Real.sqrt Geometry.conditionNumber * Real.exp (-ρ * (n*h)) *
          optimizerLawDistance a (targetState star) μ νStar +
          ((2+γ)/ρ) * Real.sqrt (Geometry.conditionNumber * Variance/(N : ℝ)) *
            (1-Real.exp (-ρ * (n*h)))) := by
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  let W := particleBrownian (J := J) μ N
  let hW := particleBrownian_isPreBrownian (J := J) μ N
  let L := momentumForceDynamics D γ
  let M := model D γ
  let H := compatibility D γ
  let Ptc := particles D γ Geometry μ hμ a Variance hVariance
  let Y := Ptc.state
  let z := fun t ↦ momentumUnpackLp Q D (Y t)
  have hY : Continuous Y := Ptc.continuous
  have hz : Continuous z := (momentumUnpackLp Q D).continuous.comp hY
  have heq (t : ℝ) (ht : 0 ≤ t) : Y t-Y 0 =
      (∫ r in 0..t, ULA.lpDrift Q (L.particleField N)
        (L.particleField_lipschitz N D.nonempty) (Y r))+
      samplerBrownianInput Q (ParticleBrownianInput.diffusion (A := HypocoercivePhase A) N
        (momentumPhysicalDiffusion (J := J) γ)) W hW 0 t := by
    exact (Ptc.equation t ht).trans (congrArg (fun b ↦
      (∫ r in 0..t, ULA.lpDrift Q (L.particleField N)
        (L.particleField_lipschitz N D.nonempty) (Y r))+b)
      (ParticleBrownianInput.packed_input_eq μ N (momentumPhysicalDiffusion (J := J) γ) 0 t))
  have hze (t : ℝ) (ht : 0 ≤ t) : z t-z 0 =
      (∫ r in 0..t, MethodSegments.momentumDrift Q D γ (z r))+
        MethodSegments.momentumInput Q W hW γ t := by
    have he := momentumUnpackLp_integral Q D γ Y
      (samplerBrownianInput Q (ParticleBrownianInput.diffusion (A := HypocoercivePhase A) N
        (momentumPhysicalDiffusion (J := J) γ)) W hW 0) hY heq t ht
    rw [momentumUnpackLp_brownian Q D hcloud W hW γ 0 t] at he
    exact he
  obtain ⟨d,C,hcoerc,hupper,hdrift⟩ := MethodMetricComparisons.momentum_metric_explicit Q D hcloud γ
    (diffusionColumns (J := J) γ) Geometry ρ hmono
  let m := Real.sqrt (EmpiricalMetric.lower N Geometry) / 2
  have hm : 0 < m := by
    exact div_pos (Real.sqrt_pos.mpr (EmpiricalMetric.lower_pos N D.nonempty Geometry)) (by positivity)
  let Mbound := 2 * Real.sqrt (EmpiricalMetric.upper N Geometry)
  have hMbound : 0 ≤ Mbound := by dsimp [Mbound]; positivity
  have hCnorm : ‖C‖ ≤ Mbound := C.opNorm_le_bound hMbound hupper
  let γnn : ℝ≥0 := ⟨γ,hγ⟩
  let Force := coupledForce (D.meanForceLp Q) (D.samplerForceLp Q)
  let LF := momentumUniformForceLip D
  let Ξ := Real.sqrt (Fintype.card (Fin N × J) : ℝ)
  let β := momentumUniformBrownianRadius (I := Fin N × J) γnn
  let rawAB := momentumUniformDefect LF γnn ‖Force 0‖ Ξ β
  let actualAB := momentumMetricDefect LF γnn ‖Force 0‖ Ξ β C m
  let AB := (Mbound*rawAB.1,Mbound*rawAB.2/m)
  let baseR := UniformIntegral.radius (LF+γnn+1) ‖Force 0‖ β 0
  let R := Mbound*‖z 0‖+(Mbound*baseR)/(1-Real.exp (-ρ))+Mbound*baseR
  let U := 4*(AB.1+AB.2*R)/(ρ*m)
  have hβ : 0 ≤ β := by dsimp [β,momentumUniformBrownianRadius]; positivity
  have hab := momentumUniformDefect_nonneg LF γnn ‖Force 0‖ Ξ β
    (norm_nonneg _) (Real.sqrt_nonneg _) hβ
  have ha₀ := hab.1
  have hb₀ := hab.2
  have hABa : 0 ≤ AB.1 := by dsimp [AB,rawAB]; positivity
  have hABb : 0 ≤ AB.2 := by dsimp [AB,rawAB]; positivity
  have hgap : 0 < 1-Real.exp (-ρ) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hrad := UniformIntegral.radius_nonneg (LF+γnn+1) (norm_nonneg (Force 0)) hβ (le_refl 0)
  have hR : 0 ≤ R := by dsimp [R,baseR]; positivity
  have hAcomp : actualAB.1 ≤ AB.1 :=
    mul_le_mul_of_nonneg_right hCnorm ha₀
  have hBcomp : actualAB.2 ≤ AB.2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCnorm hb₀) hm.le
  have hScomp : ‖C‖*baseR ≤ Mbound*baseR := mul_le_mul_of_nonneg_right hCnorm hrad
  have hRcomp : momentumUniformReferenceRadius LF γnn ‖Force 0‖ β ρ C (z 0) ≤ R :=
    add_le_add (add_le_add (hupper (z 0))
      (div_le_div_of_nonneg_right hScomp hgap.le)) hScomp
  have hactualR : 0 ≤ momentumUniformReferenceRadius LF γnn ‖Force 0‖ β ρ C (z 0) := by
    dsimp [momentumUniformReferenceRadius]
    positivity
  have hUcomp : momentumUniformErrorConstant LF γnn ‖Force 0‖ Ξ β ρ C m (z 0) ≤ U := by
    apply div_le_div_of_nonneg_right _ (mul_nonneg hρ.le hm.le)
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤4)
    exact add_le_add hAcomp (mul_le_mul hBcomp hRcomp hactualR hABb)
  have hU : 0 ≤ U := by
    change 0 ≤ 4*(AB.1+AB.2*R)/(ρ*m)
    positivity
  change 0 < UniformStep.maximumStep ρ AB.2 ∧ 0 ≤ U ∧ _
  refine ⟨UniformStep.maximumStep_pos ρ AB.2 hρ hABb,hU,?_⟩
  intro h hh hhmax n
  obtain ⟨hh1,hρh,hsmall⟩ := UniformStep.admissible ρ AB.2 h hρ hABb hh hhmax
  have hsmallActual : actualAB.2*Real.sqrt h ≤ ρ/4 :=
    (mul_le_mul_of_nonneg_right hBcomp (Real.sqrt_nonneg h)).trans hsmall
  have hnum := momentumParticle_time_uniform Q W hW D γnn C m ρ hm hρ hcoerc hdrift
    z hz hze h hh hh1 hρh hsmallActual n
  let num := momentumParticleIterate Q W hW D γ h
    (initial D γ Geometry μ hμ a Variance hVariance) n
  have herror : ‖num-z (n*h)‖ ≤ U*Real.sqrt h :=
    hnum.trans (mul_le_mul_of_nonneg_right hUcomp (Real.sqrt_nonneg h))
  refine ⟨herror,?_⟩
  have hparam : LipschitzWith 1 M.parameter := momentum_parameter_lipschitz D.F D.G γ (diffusionColumns γ)
  have hcoord : (z (n*h)).2.1=Ptc.parameter hparam (n*h) :=
    momentumUnpackLp_parameter Q D γ (diffusionColumns γ) (Y (n*h))
  have hsource := AdditiveConstructed.parameter_bound (ULA.CanonicalBrownian.vectorProbability J)
    L M H Geometry μ hμ a (input γ) (input_continuous γ) (input_zero γ) N D.nonempty
    Variance hVariance νStar hνStar (targetState star) Frozen ρ hρ hmono hparam hg
    (fun t _ ↦ target_fixed D γ star t) hV (n*h) (mul_nonneg (Nat.cast_nonneg n) hh.le)
  have hresponse : (L.responseLip : ℝ)=2+γ := by
    change 2+‖γ‖=2+γ
    rw [Real.norm_eq_abs,abs_of_nonneg hγ]
  have hstar : M.parameter (targetState star)=star := rfl
  have hreference : ‖(z (n*h)).2.1-Lp.const 2 Q star‖ ≤
      Real.sqrt Geometry.conditionNumber * Real.exp (-ρ*(n*h))*
        optimizerLawDistance a (targetState star) μ νStar+
      ((2+γ)/ρ)*Real.sqrt (Geometry.conditionNumber*Variance/(N : ℝ))*(1-Real.exp (-ρ*(n*h))) := by
    rw [hcoord]
    simpa [Ptc,FullyConstructedMomentum.particles,Q,ParticleNoiseSpace.probability,L,M,H,hresponse,hstar] using hsource
  have hp : ‖num.2.1-(z (n*h)).2.1‖ ≤ ‖num-z (n*h)‖ :=
    (norm_fst_le (num.2-(z (n*h)).2)).trans (norm_snd_le (num-z (n*h)))
  exact (numerical_target_triangle Q num.2.1 (z (n*h)).2.1 star).trans
    (add_le_add (hp.trans herror) hreference)
/-- The actual raw-state discretisation bound with an explicit coefficient. -/
theorem explicit_discretization_bound
    (hcloud : D.cloud = euclideanParticleEncoding N J) (hγ : 0 ≤ γ)
    (star : A) (νStar : Measure (HypocoercivePhase (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HypocoercivePhase (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (momentumForceDynamics D γ) νStar hνStar (targetState star) (input γ))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (model D γ) Geometry ρ)
    (hg : (model D γ).meanGradient νStar (targetState star) = 0)
    (hV : 0 ≤ Variance)
    (h : ℝ) (hh : 0 < h) (hhmax : h ≤ maximumStep D γ Geometry μ hγ ρ) (n : ℕ) :
‖momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          D γ h (initial D γ Geometry μ hμ a Variance hVariance) n -
          momentumUnpackLp (ParticleNoiseSpace.probability (J := J) μ N) D
            ((particles D γ Geometry μ hμ a Variance hVariance).state (n*h))‖ ≤ discretizationConstant D γ Geometry μ hμ a Variance hVariance hγ ρ * Real.sqrt h := by
  exact ((explicit_guarantee D γ Geometry μ hμ a Variance hVariance hcloud hγ
    star νStar hνStar Frozen ρ hρ hmono hg hV).2.2 h hh hhmax n).1

/-- Final parameter theorem with data-defined coefficient and step size. -/
theorem explicit_parameter_bound
    (hcloud : D.cloud = euclideanParticleEncoding N J) (hγ : 0 ≤ γ)
    (star : A) (νStar : Measure (HypocoercivePhase (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HypocoercivePhase (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (momentumForceDynamics D γ) νStar hνStar (targetState star) (input γ))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (model D γ) Geometry ρ)
    (hg : (model D γ).meanGradient νStar (targetState star) = 0)
    (hV : 0 ≤ Variance)
    (h : ℝ) (hh : 0 < h) (hhmax : h ≤ maximumStep D γ Geometry μ hγ ρ) (n : ℕ) :
        ‖(momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          D γ h (initial D γ Geometry μ hμ a Variance hVariance) n).2.1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) star‖ ≤
        discretizationConstant D γ Geometry μ hμ a Variance hVariance hγ ρ * Real.sqrt h +
        (Real.sqrt Geometry.conditionNumber * Real.exp (-ρ * (n*h)) *
          optimizerLawDistance a (targetState star) μ νStar +
          ((2+γ)/ρ) * Real.sqrt (Geometry.conditionNumber * Variance/(N : ℝ)) *
            (1-Real.exp (-ρ * (n*h)))) := by
  exact ((explicit_guarantee D γ Geometry μ hμ a Variance hVariance hcloud hγ
    star νStar hνStar Frozen ρ hρ hmono hg hV).2.2 h hh hhmax n).2

/-- Backwards-compatible existential form of the explicit guarantee. -/
theorem numerical_parameter_bound
    (hcloud : D.cloud = euclideanParticleEncoding N J) (hγ : 0 ≤ γ)
    (star : A) (νStar : Measure (HypocoercivePhase (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HypocoercivePhase (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (momentumForceDynamics D γ) νStar hνStar (targetState star) (input γ))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (model D γ) Geometry ρ)
    (hg : (model D γ).meanGradient νStar (targetState star) = 0)
    (hV : 0 ≤ Variance) :
    ∃ hmax U : ℝ, 0 < hmax ∧ 0 ≤ U ∧
      ∀ h : ℝ, 0 < h → h ≤ hmax → ∀ n : ℕ,
        (‖momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          D γ h (initial D γ Geometry μ hμ a Variance hVariance) n -
          momentumUnpackLp (ParticleNoiseSpace.probability (J := J) μ N) D
            ((particles D γ Geometry μ hμ a Variance hVariance).state (n*h))‖ ≤ U*Real.sqrt h) ∧
        ‖(momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          D γ h (initial D γ Geometry μ hμ a Variance hVariance) n).2.1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) star‖ ≤
        U * Real.sqrt h +
        (Real.sqrt Geometry.conditionNumber * Real.exp (-ρ * (n*h)) *
          optimizerLawDistance a (targetState star) μ νStar +
          ((2+γ)/ρ) * Real.sqrt (Geometry.conditionNumber * Variance/(N : ℝ)) *
            (1-Real.exp (-ρ * (n*h)))) := by
  exact ⟨maximumStep D γ Geometry μ hγ ρ, discretizationConstant D γ Geometry μ hμ a Variance hVariance hγ ρ,
    explicit_guarantee D γ Geometry μ hμ a Variance hVariance hcloud hγ
      star νStar hνStar Frozen ρ hρ hmono hg hV⟩

end PBGSO.FullyUniformMomentum
