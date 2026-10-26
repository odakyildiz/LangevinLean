import PBGSO.FullyConstructedHigherOrder
import PBGSO.HOLUniform
import PBGSO.ImplementationMetric
import PBGSO.UniformStepSize

/-! # Time-uniform HOL-MYPGD parameter error from primitive source data

The original source A3 constructs the complete empirical metric. Actual
particle integral dynamics, exact restarts, printed Gaussian innovations,
local defects, reference moments and numerical stability are all derived.
The numerical error is uniform over every iteration on a strictly positive
explicit small-step interval. No common force potential is required.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace InnerProductSpace
namespace PBGSO.FullyUniformHigherOrder
open Methods ImplementationDynamics FullyConstructedHigherOrder

variable {A J : Type*} {N : ℕ}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [Fintype J] [DecidableEq J]
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)

private theorem input_continuous (α : ℝ) : Continuous (input (J := J) α) :=
  samplerBrownianInput_continuous _ _ _ _ _

private theorem input_zero (α : ℝ) : input (J := J) α 0 = 0 :=
  samplerBrownianInput_zero _ _ _ _ _

variable (α γ : ℝ) (Geo : TwistedGeometry A (HigherOrderSampler (EuclideanSpace ℝ J)))
  (μ : Measure (HigherOrderSampler (EuclideanSpace ℝ J))) [IsProbabilityMeasure μ]
  (hμ : MemLp (fun z : HigherOrderSampler (EuclideanSpace ℝ J) ↦ z) 2 μ) (a : A)
  (Variance : ℝ)
  (hVariance : ∀ r, 0 ≤ r →
    (∫ z, ‖(sourceModel D α γ).observation
      ((sourceModel D α γ).parameter (AdditiveCanonical.optimizer
        (ULA.CanonicalBrownian.vectorProbability J) (higherOrderForceDynamics D α γ)
        μ hμ a (input α) (input_continuous α) (input_zero α) r))
      ((sourceModel D α γ).position z) -
      (sourceModel D α γ).meanGradient (AdditiveCanonical.law
        (ULA.CanonicalBrownian.vectorProbability J) (higherOrderForceDynamics D α γ)
        μ hμ a (input α) (input_continuous α) (input_zero α) r)
        (AdditiveCanonical.optimizer (ULA.CanonicalBrownian.vectorProbability J)
          (higherOrderForceDynamics D α γ) μ hμ a
          (input α) (input_continuous α) (input_zero α) r)‖ ^ 2
      ∂AdditiveCanonical.law (ULA.CanonicalBrownian.vectorProbability J)
        (higherOrderForceDynamics D α γ) μ hμ a
        (input α) (input_continuous α) (input_zero α) r) ≤ Variance)


/-- Uniform strong discretisation error in the original raw product norm:
the maximum of the four component L² discrepancies. All constants are derived
from primitive forces, A3, physical coordinates and the actual initial state. -/
theorem discretization_bound [FiniteDimensional ℝ A]
    (hcloud : D.cloud = euclideanParticleEncoding N J)
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (sourceModel D α γ) Geo ρ) :
    ∃ hmax K : ℝ, 0 < hmax ∧ 0 ≤ K ∧
      ∀ (h : ℝ≥0) (n : ℕ), 0 < (h : ℝ) → (h : ℝ) ≤ hmax →
        ‖higherOrderPullbackParticleIterate (Fin N × J)
          (ParticleNoiseSpace.probability (J := J) μ N)
          (ParticleNoiseSpace.noise_preserving (J := J) μ N) D α γ h
          (initial D α γ Geo μ hμ a Variance hVariance) n -
          higherOrderUnpackLp (ParticleNoiseSpace.probability (J := J) μ N) D
            ((particle D α γ Geo μ hμ a Variance hVariance).state (n * (h : ℝ)))‖ ≤
          K * Real.sqrt (h : ℝ) := by
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  let hf := ParticleNoiseSpace.noise_preserving (J := J) μ N
  let L := higherOrderForceDynamics D α γ
  let M := sourceModel D α γ
  let H := higherOrder_compatibility D.F D.G D.parameterLip D.samplerLip
    D.parameter_bound D.sampler_bound α γ (physicalColumns (J := J) α)
  let Part := particle D α γ Geo μ hμ a Variance hVariance
  let U := higherOrderUnpackLp Q D
  let Y := fun t : ℝ ↦ U (Part.state t)
  have hY : Continuous Y := U.continuous.comp Part.continuous
  have hYeq : ∀ t, 0 ≤ t → Part.state t - Part.state 0 =
      (∫ r in 0..t, ULA.lpDrift Q (L.particleField N)
        (L.particleField_lipschitz N D.nonempty) (Part.state r)) +
      samplerBrownianInput Q (ParticleBrownianInput.diffusion (A := A) N
        (higherOrderPhysicalDiffusion (J := J) α))
        (canonicalPullbackCoordinate (Fin N × J) hf)
        (canonicalPullbackCoordinate_isPreBrownian (Fin N × J) hf) 0 t := by
    intro t ht
    have he := Part.equation t ht
    dsimp only [input] at he
    rw [ParticleBrownianInput.packed_input_eq] at he
    exact he
  have hraw : ∀ t, 0 ≤ t → Y t - Y 0 =
      (∫ r in 0..t, holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (Y r)) +
        higherOrderRestartInput Q hf α 0 t := by
    intro t ht
    have he := higherOrderUnpackLp_integral Q D α γ Part.state
      (samplerBrownianInput Q (ParticleBrownianInput.diffusion (A := A) N
        (higherOrderPhysicalDiffusion (J := J) α))
        (canonicalPullbackCoordinate (Fin N × J) hf)
        (canonicalPullbackCoordinate_isPreBrownian (Fin N × J) hf) 0)
      Part.continuous hYeq t ht
    rw [higherOrderUnpackLp_brownian Q D hcloud] at he
    exact he
  obtain ⟨dim, C, hcoerc, hupper, hCmono⟩ := ImplementationMetric.higherOrder_metric Q D α γ
    (physicalColumns (J := J) α) Geo ρ hmono
  let m := Real.sqrt (EmpiricalMetric.lower N Geo) /
    (‖(higherOrderPhysicalLpEquiv Q D).symm.toContinuousLinearMap‖ + 1)
  let Upper := Real.sqrt (EmpiricalMetric.upper N Geo) *
    ‖(higherOrderPhysicalLpEquiv Q D).toContinuousLinearMap‖
  have hm : 0 < m := by
    dsimp [m]
    exact div_pos (Real.sqrt_pos.mpr (EmpiricalMetric.lower_pos N D.nonempty Geo)) (by positivity)
  have hUpper : 0 ≤ Upper := by dsimp [Upper]; positivity
  have hCnorm : ‖C‖ ≤ Upper := C.opNorm_le_bound hUpper hupper
  let f₀ := ‖D.meanForceLp Q 0 0‖
  let g₀ := ‖D.samplerForceLp Q 0 0‖
  let b₀ := ‖holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ 0‖
  let c₀ := holUniformLocalConstant0 (Fin N × J) α γ D.meanLip D.samplerForceLip f₀ g₀ b₀
  let c₁ := holUniformLocalConstant1 α γ D.meanLip D.samplerForceLip f₀ g₀
  let Lip := holDriftGlobalLip D.meanLip D.samplerForceLip α γ
  let Ξ := holUniformNoiseRadius (Fin N × J) α
  let P₀ := UniformIntegral.radius Lip b₀ Ξ 0
  let S := Upper * P₀
  let R := Upper * ‖Y 0‖ + S / (1 - Real.exp (-ρ)) + S
  let b := Upper * c₁ / m
  let K := (4 * (Upper * c₀ + b * R) / ρ) / m
  have hc := holUniformLocalConstants_nonneg (Fin N × J) α γ D.meanLip D.samplerForceLip
    f₀ g₀ b₀ hα hγ D.meanLip.coe_nonneg D.samplerForceLip.coe_nonneg
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have hc₀ : 0 ≤ c₀ := hc.1
  have hc₁ : 0 ≤ c₁ := hc.2
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hP₀ : 0 ≤ P₀ := by
    exact UniformIntegral.radius_nonneg Lip (norm_nonneg _)
      (by dsimp [Ξ, holUniformNoiseRadius]; positivity) (le_refl 0)
  have hS : 0 ≤ S := mul_nonneg hUpper hP₀
  have hgap : 0 < 1 - Real.exp (-ρ) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hactualR : holUniformReferenceRadius
      (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ) Lip C ρ Ξ (Y 0) ≤ R := by
    have hs : ‖C‖ * P₀ ≤ S := mul_le_mul_of_nonneg_right hCnorm hP₀
    exact add_le_add (add_le_add (hupper (Y 0))
      (div_le_div_of_nonneg_right hs hgap.le)) hs
  have hab : ‖C‖ * c₁ / m ≤ b :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCnorm hc₁) hm.le
  refine ⟨UniformStep.maximumStep ρ b, K, UniformStep.maximumStep_pos ρ b hρ hb, hK, ?_⟩
  intro h n hh hhmax
  obtain ⟨hh1, hρh, hsmall⟩ := UniformStep.admissible ρ b h hρ hb hh hhmax
  have hsmallC : (‖C‖ * c₁ / m) * Real.sqrt (h : ℝ) ≤ ρ / 4 :=
    (mul_le_mul_of_nonneg_right hab (Real.sqrt_nonneg _)).trans hsmall
  have hnum := higherOrder_time_uniform_of_integral Q hf
    (D.meanForceLp Q) (D.samplerForceLp Q) D.meanLip D.samplerForceLip α γ
    D.meanLip.coe_nonneg D.samplerForceLip.coe_nonneg
    (D.meanForceLp_bound Q) (D.samplerForceLp_bound Q) hα hγ C m ρ hm hρ hcoerc hCmono
    Y hY hraw h hh hh1 hρh hsmallC n
  have hdisc : ‖higherOrderPullbackParticleIterate (Fin N × J) Q hf D α γ h
      (initial D α γ Geo μ hμ a Variance hVariance) n - Y ((n : ℝ) * (h : ℝ))‖ ≤
      K * Real.sqrt (h : ℝ) := by
    apply hnum.trans
    have hRactual0 : 0 ≤ holUniformReferenceRadius
        (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ) Lip C ρ Ξ (Y 0) := by
      dsimp [holUniformReferenceRadius]
      positivity
    have hbudget : ‖C‖ * c₀ + (‖C‖ * c₁ / m) *
        holUniformReferenceRadius (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ)
          Lip C ρ Ξ (Y 0) ≤ Upper * c₀ + b * R := by
      exact add_le_add (mul_le_mul_of_nonneg_right hCnorm hc₀)
        (mul_le_mul hab hactualR hRactual0 hb)
    calc
      _ ≤ ((4 * (Upper * c₀ + b * R) / ρ) * Real.sqrt (h : ℝ)) / m := by gcongr
      _ = K * Real.sqrt (h : ℝ) := by dsimp [K]; ring
  exact hdisc

/-- The final time-uniform parameter error combines the derived numerical
floor with source continuous relaxation and particle interaction. No numerical
metric, compatible process, moment estimate or error recurrence is a premise. -/
theorem parameter_bound [FiniteDimensional ℝ A]
    (hcloud : D.cloud = euclideanParticleEncoding N J)
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (νStar : Measure (HigherOrderSampler (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HigherOrderSampler (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (aStar : A)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (higherOrderForceDynamics D α γ) νStar hνStar aStar (input α))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (sourceModel D α γ) Geo ρ)
    (hg : (sourceModel D α γ).meanGradient νStar aStar = 0)
    (hV : 0 ≤ Variance) :
    ∃ hmax K : ℝ, 0 < hmax ∧ 0 ≤ K ∧
      ∀ (h : ℝ≥0) (n : ℕ), 0 < (h : ℝ) → (h : ℝ) ≤ hmax →
        ‖(higherOrderPullbackParticleIterate (Fin N × J)
          (ParticleNoiseSpace.probability (J := J) μ N)
          (ParticleNoiseSpace.noise_preserving (J := J) μ N) D α γ h
          (initial D α γ Geo μ hμ a Variance hVariance) n).1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) aStar‖ ≤
        K * Real.sqrt (h : ℝ) +
        (Real.sqrt Geo.conditionNumber * Real.exp (-ρ * (n * (h : ℝ))) *
          optimizerLawDistance a aStar μ νStar +
          (1 / ρ) * Real.sqrt (Geo.conditionNumber * Variance / (N : ℝ)) *
            (1 - Real.exp (-ρ * (n * (h : ℝ))))) := by
  obtain ⟨hmax, K, hhmax, hK, hdiscretization⟩ := discretization_bound D α γ Geo μ hμ a
    Variance hVariance hcloud hα hγ ρ hρ hmono
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  let hf := ParticleNoiseSpace.noise_preserving (J := J) μ N
  let L := higherOrderForceDynamics D α γ
  let M := sourceModel D α γ
  let H := higherOrder_compatibility D.F D.G D.parameterLip D.samplerLip
    D.parameter_bound D.sampler_bound α γ (physicalColumns (J := J) α)
  let Part := particle D α γ Geo μ hμ a Variance hVariance
  let Y := fun t : ℝ ↦ higherOrderUnpackLp Q D (Part.state t)
  refine ⟨hmax, K, hhmax, hK, ?_⟩
  intro h n hh hhstep
  have hdisc := hdiscretization h n hh hhstep
  have hparam := higherOrder_parameter_lipschitz D.F D.G α γ (physicalColumns (J := J) α)
  have hcparam := AdditiveConstructed.parameter_bound (ULA.CanonicalBrownian.vectorProbability J)
    L M H Geo μ hμ a (input α) (input_continuous α) (input_zero α) N D.nonempty
    Variance hVariance νStar hνStar aStar Frozen ρ hρ hmono hparam hg
    (by intros; exact neg_zero) hV (n * (h : ℝ)) (by positivity)
  have hcoordinate : (Y (n * (h : ℝ))).1 = Part.parameter hparam (n * (h : ℝ)) :=
    higherOrderUnpackLp_parameter Q D α γ (physicalColumns (J := J) α) _
  change ‖Part.parameter hparam (n * (h : ℝ)) - Lp.const 2 (IndependentCopies.seeds (μ.prod (ULA.CanonicalBrownian.vectorProbability J)))
      (M.parameter aStar)‖ ≤ _ at hcparam
  rw [← hcoordinate] at hcparam
  have hidentity : M.parameter aStar = aStar := rfl
  have hresponse : (L.responseLip : ℝ) = 1 := rfl
  rw [hidentity, hresponse] at hcparam
  have hdiscθ : ‖(higherOrderPullbackParticleIterate (Fin N × J) Q hf D α γ h
      (initial D α γ Geo μ hμ a Variance hVariance) n).1 - (Y (n * (h : ℝ))).1‖ ≤
      K * Real.sqrt (h : ℝ) := (norm_fst_le _).trans hdisc
  exact (numerical_target_triangle Q _ (Y (n * (h : ℝ))).1 aStar).trans
    (add_le_add hdiscθ hcparam)

end PBGSO.FullyUniformHigherOrder
