import PBGSO.HigherOrderIntegralReference

/-! # HOL-MYPGD target bound from primitive data

The complete interacting integral process, its original HOL coordinates,
all Brownian innovations and the finite-horizon reference constants are
constructed. The stationary input is an actual frozen invariant sampler
trajectory, as in source A2; the model's joint monotonicity and uniform
observation variance remain explicit assumptions. No error estimate,
reference equation, law equality or moment/modulus estimate is supplied.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace InnerProductSpace
namespace PBGSO.FullyConstructedHigherOrder
open Methods ImplementationDynamics

variable {A J : Type*} {N : ℕ}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [Fintype J] [DecidableEq J]
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)

/-- Actual final-auxiliary diffusion columns of the original HOL process. -/
def physicalColumns (α : ℝ) (i : J) : EuclideanSpace ℝ J :=
  Real.sqrt 2 • (Real.sqrt α • EuclideanSpace.basisFun J ℝ i)

/-- The original independent-force HOL model with its physical diffusion. -/
def sourceModel (α γ : ℝ) := higherOrderModel D.F D.G α γ (physicalColumns (J := J) α)

/-- The complete sampler Brownian input on its canonical source. -/
def input (α : ℝ) : ℝ → Lp (HigherOrderSampler (EuclideanSpace ℝ J)) 2
    (ULA.CanonicalBrownian.vectorProbability J) :=
  samplerBrownianInput (ULA.CanonicalBrownian.vectorProbability J)
    (higherOrderPhysicalDiffusion (J := J) α) ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian 0

/-- The input's physical coefficient is exactly the source model diffusion. -/
theorem physical_column_eq (α γ : ℝ) (a : A)
    (z : HigherOrderSampler (EuclideanSpace ℝ J)) (i : J) :
    (sourceModel D α γ).diffusion a z i = Real.sqrt 2 •
      higherOrderPhysicalDiffusion α (EuclideanSpace.basisFun J ℝ i) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [sourceModel, higherOrderModel, higherOrderPhysicalDiffusion_apply]
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [sourceModel, higherOrderModel, higherOrderPhysicalDiffusion_apply]
    · rfl

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

/-- The actual shared random optimiser and interacting particle trajectory. -/
def particle := AdditiveConstructed.particleRealization
  (ULA.CanonicalBrownian.vectorProbability J) (higherOrderForceDynamics D α γ)
  (sourceModel D α γ)
  (higherOrder_compatibility D.F D.G D.parameterLip D.samplerLip
    D.parameter_bound D.sampler_bound α γ (physicalColumns α)) Geo μ hμ a
  (input α) (input_continuous α) (input_zero α) N D.nonempty Variance hVariance

/-- The numerical implementation starts at the same actual random initial
cloud and shared optimiser as the constructed continuous dynamics. -/
def initial : HOLState (Lp A 2 (ParticleNoiseSpace.probability (J := J) μ N))
    (Lp (EuclideanSpace ℝ (Fin N × J)) 2 (ParticleNoiseSpace.probability (J := J) μ N)) :=
  higherOrderUnpackLp (ParticleNoiseSpace.probability (J := J) μ N) D
    ((particle D α γ Geo μ hμ a Variance hVariance).state 0)

/-- HOL-MYPGD parameter error, including discretization, relaxation and
finite-particle terms, from the actual independent-force additive model.
All constants are uniform over meshes in the fixed finite horizon.
The initial-state coupling, reference equations, L² coordinate equality,
Gaussian innovation coupling and regularity estimates are conclusions of
prior constructions rather than hypotheses of this theorem. -/
theorem parameter_bound
    (hcloud : D.cloud = euclideanParticleEncoding N J)
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (νStar : Measure (HigherOrderSampler (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HigherOrderSampler (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (aStar : A)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (higherOrderForceDynamics D α γ) νStar hνStar aStar (input α))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (sourceModel D α γ) Geo ρ)
    (hg : (sourceModel D α γ).meanGradient νStar aStar = 0)
    (hV : 0 ≤ Variance) (T : ℝ) :
    ∃ P G C : ℝ, 0 ≤ P ∧ 0 ≤ G ∧ 0 ≤ C ∧
      ∀ (h : ℝ≥0) (n : ℕ), 0 < (h : ℝ) → (h : ℝ) ≤ 1 → n * (h : ℝ) ≤ T →
        ‖(higherOrderPullbackParticleIterate (Fin N × J)
          (ParticleNoiseSpace.probability (J := J) μ N)
          (ParticleNoiseSpace.noise_preserving (J := J) μ N) D α γ h
          (initial D α γ Geo μ hμ a Variance hVariance) n).1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) aStar‖ ≤
        higherOrderDiscretizationBudget (Fin N × J) D α γ G
          (G + γ * P + (D.samplerForceLip : ℝ) * G) P P C h 0 n +
        (Real.sqrt Geo.conditionNumber * Real.exp (-ρ * (n * (h : ℝ))) *
          optimizerLawDistance a aStar μ νStar +
          (1 / ρ) * Real.sqrt (Geo.conditionNumber * Variance / (N : ℝ)) *
            (1 - Real.exp (-ρ * (n * (h : ℝ))))) := by
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  let hf := ParticleNoiseSpace.noise_preserving (J := J) μ N
  let L := higherOrderForceDynamics D α γ
  let M := sourceModel D α γ
  let H := higherOrder_compatibility D.F D.G D.parameterLip D.samplerLip
    D.parameter_bound D.sampler_bound α γ (physicalColumns (J := J) α)
  let Part := particle D α γ Geo μ hμ a Variance hVariance
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
  obtain ⟨P, G, C, hP, hG, hC, hrefs⟩ :=
    MethodSegments.exists_higherOrderReference_of_particle_integral Q hf D hcloud α γ hα hγ
      Part.state Part.continuous hYeq T
  refine ⟨P, G, C, hP, hG, hC, ?_⟩
  intro h n hh hh1 hn
  obtain ⟨Ref, hRef⟩ := hrefs h n hh hh1 hn
  have hparam := higherOrder_parameter_lipschitz D.F D.G α γ (physicalColumns (J := J) α)
  have hcoordinate : (Ref.r n 0).1 = Part.parameter hparam (n * (h : ℝ)) := by
    rw [hRef]
    simp only [add_zero]
    exact higherOrderUnpackLp_parameter Q D α γ (physicalColumns (J := J) α) _
  have hbound := hol_mypgd_constructed_parameter_bound L M H Geo μ hμ a
    (input α) (input_continuous α) (input_zero α) N D.nonempty Variance hVariance
    νStar hνStar aStar Frozen ρ hρ hmono hparam hg
    (by intros; exact neg_zero) hV D Ref
    (initial D α γ Geo μ hμ a Variance hVariance) hcoordinate
  have hinit : Ref.r 0 0 = initial D α γ Geo μ hμ a Variance hVariance := by
    rw [hRef]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rfl
  rw [hinit] at hbound
  have hm : M.parameter aStar = aStar := rfl
  have hl : (L.responseLip : ℝ) = 1 := rfl
  rw [hm, hl] at hbound
  simpa only [holError, sub_self, norm_zero, add_zero] using hbound

/-- The fully constructed HOL implementation also admits the separately
proved original-target bias term from an actual coupled pair of target
observations. The coupling radius is explicit; no model-specific smoothing
radius or proper-prior claim is inferred. -/
theorem original_parameter_bound
    (hcloud : D.cloud = euclideanParticleEncoding N J)
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (νStar : Measure (HigherOrderSampler (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HigherOrderSampler (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (aStar : A)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (higherOrderForceDynamics D α γ) νStar hνStar aStar (input α))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (sourceModel D α γ) Geo ρ)
    (hg : (sourceModel D α γ).meanGradient νStar aStar = 0)
    (hV : 0 ≤ Variance) (T : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : A → A) (fobs : E → A) (obsLip : ℝ≥0) (hobs : LipschitzWith obsLip fobs)
    (m ε : ℝ) (hm : 0 < m) (star : A) (hstar : g star = 0)
    (hstrong : m * ‖aStar - star‖ ^ 2 ≤ ⟪aStar - star, g aStar - g star⟫_ℝ)
    (Xoriginal Xsurrogate : Lp E 2 (ParticleNoiseSpace.probability (J := J) μ N))
    (hgradient : g aStar = ∫ ω, fobs (Xoriginal ω) ∂ParticleNoiseSpace.probability (J := J) μ N)
    (hsurrogate : (∫ ω, fobs (Xsurrogate ω) ∂ParticleNoiseSpace.probability (J := J) μ N) = 0)
    (hcoupling : ‖Xoriginal - Xsurrogate‖ ≤ ε) :
    ∃ P G C : ℝ, 0 ≤ P ∧ 0 ≤ G ∧ 0 ≤ C ∧
      ∀ (h : ℝ≥0) (n : ℕ), 0 < (h : ℝ) → (h : ℝ) ≤ 1 → n * (h : ℝ) ≤ T →
        ‖(higherOrderPullbackParticleIterate (Fin N × J)
          (ParticleNoiseSpace.probability (J := J) μ N)
          (ParticleNoiseSpace.noise_preserving (J := J) μ N) D α γ h
          (initial D α γ Geo μ hμ a Variance hVariance) n).1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) star‖ ≤
        higherOrderDiscretizationBudget (Fin N × J) D α γ G
          (G + γ * P + (D.samplerForceLip : ℝ) * G) P P C h 0 n +
        (Real.sqrt Geo.conditionNumber * Real.exp (-ρ * (n * (h : ℝ))) *
          optimizerLawDistance a aStar μ νStar +
          (1 / ρ) * Real.sqrt (Geo.conditionNumber * Variance / (N : ℝ)) *
            (1 - Real.exp (-ρ * (n * (h : ℝ))))) + (obsLip : ℝ) * ε / m := by
  obtain ⟨P, G, C, hP, hG, hC, hb⟩ := parameter_bound D α γ Geo μ hμ a Variance hVariance
    hcloud hα hγ νStar hνStar aStar Frozen ρ hρ hmono hg hV T
  have htarget := hybrid_target_bias (ParticleNoiseSpace.probability (J := J) μ N)
    g fobs obsLip hobs m ε hm aStar star hstar hstrong
    Xoriginal Xsurrogate hgradient hsurrogate hcoupling
  refine ⟨P, G, C, hP, hG, hC, ?_⟩
  intro h n hh hh1 hn
  exact (numerical_target_shift (ParticleNoiseSpace.probability (J := J) μ N) _ aStar star).trans
    (add_le_add (hb h n hh hh1 hn) htarget)

end PBGSO.FullyConstructedHigherOrder
