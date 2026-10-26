import PBGSO.MomentumIntegralConstruction

/-! # Fully constructed M-MFPO parameter bound
Primitive independent force regularity, actual frozen invariant dynamics,
joint monotonicity and uniform observation variance construct every process
and numerical-reference premise. The initial cloud and full Brownian source
are independent under the actual product seed measure. No reference equation,
node moment/modulus, source/particle weak solution, realization or coordinate
law is a hypothesis of the final theorem.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace PBGSO.FullyConstructedMomentum
open Methods ImplementationDynamics MethodSegments

variable {A J : Type*} {N : ℕ} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)
  (γ : ℝ)

/-- The actual physical diffusion columns, normalized consistently with
`samplerBrownianInput`'s √2 scaling. -/
def diffusionColumns (i : J) : HypocoercivePhase (EuclideanSpace ℝ J) :=
  Real.sqrt 2 • momentumPhysicalDiffusion γ (EuclideanSpace.basisFun J ℝ i)

/-- The complete optimiser/sampler model of the original kinetic method. -/
def model := heavyBallModel γ D.F D.G (diffusionColumns (J := J) γ)

/-- The model diffusion equals the actual physical coefficient of the
constructed Brownian input, including its √2 normalization. -/
theorem physical_column_eq (s : HypocoercivePhase A)
    (z : HypocoercivePhase (EuclideanSpace ℝ J)) (i : J) :
    (model D γ).diffusion s.fst z i = Real.sqrt 2 •
      momentumPhysicalDiffusion γ (EuclideanSpace.basisFun J ℝ i) := rfl

/-- Primitive model identities follow from the actual force definitions. -/
theorem compatibility : AdditiveModelCompatibility (momentumForceDynamics D γ) (model D γ) :=
  momentum_compatibility D.F D.G D.parameterLip D.samplerLip D.parameter_bound D.sampler_bound γ
    (diffusionColumns γ)

/-- The actual physical one-copy Brownian input used by the construction. -/
def input (t : ℝ) : Lp (HypocoercivePhase (EuclideanSpace ℝ J)) 2 (ULA.CanonicalBrownian.vectorProbability J) :=
  samplerBrownianInput (ULA.CanonicalBrownian.vectorProbability J) (momentumPhysicalDiffusion γ)
    ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian 0 t

theorem input_continuous : Continuous (input (J := J) γ) :=
  samplerBrownianInput_continuous _ _ _ _ _

@[simp] theorem input_zero : input (J := J) γ 0 = 0 := samplerBrownianInput_zero _ _ _ _ _

/-- A target parameter has zero optimiser momentum at stationarity. -/
def targetState (star : A) : HypocoercivePhase A := WithLp.toLp 2 (star, 0)

theorem target_fixed (star : A) (t : ℝ) : (model D γ).optimizer t (targetState star) 0 = 0 := by
  apply WithLp.ofLp_injective 2
  simp [model, heavyBallModel, targetState]

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

/-- Actual interacting process selected from primitive Picard construction,
with true synchronous iid reference copies and the physical Brownian input. -/
def particles := AdditiveConstructed.particleRealization (ULA.CanonicalBrownian.vectorProbability J)
  (momentumForceDynamics D γ) (model D γ) (compatibility D γ) Geometry μ hμ a
  (input γ) (input_continuous γ) (input_zero γ) N D.nonempty Variance hVariance

/-- Actual numerical initial phase: the same optimiser and iid sampler cloud
as the constructed interacting process, in the original method coordinates. -/
def initial := momentumUnpackLp (ParticleNoiseSpace.probability (J := J) μ N) D
  ((particles D γ Geometry μ hμ a Variance hVariance).state 0)

/-- Fully constructed finite-horizon M-MFPO parameter guarantee. Its three
terms are verified discretization, mean-field relaxation and finite-particle
interaction. All mesh constants are derived uniformly on the chosen horizon.
Only source frozen invariance, A3 and uniform observation variance remain as
analytic/statistical hypotheses, alongside primitive force regularity. -/
theorem numerical_parameter_bound
    (hcloud : D.cloud = euclideanParticleEncoding N J) (hγ : 0 ≤ γ)
    (star : A) (νStar : Measure (HypocoercivePhase (EuclideanSpace ℝ J))) [IsProbabilityMeasure νStar]
    (hνStar : MemLp (fun z : HypocoercivePhase (EuclideanSpace ℝ J) ↦ z) 2 νStar)
    (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
      (momentumForceDynamics D γ) νStar hνStar (targetState star) (input γ))
    (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity (model D γ) Geometry ρ)
    (hg : (model D γ).meanGradient νStar (targetState star) = 0)
    (hV : 0 ≤ Variance) (T : ℝ) :
    ∃ P G R : ℝ, 0 ≤ P ∧ 0 ≤ G ∧ 0 ≤ R ∧
      ∀ (h : ℝ), 0 < h → h ≤ 1 → ∀ n : ℕ, (n : ℝ) * h ≤ T →
        ‖(momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
          (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
          D γ h (initial D γ Geometry μ hμ a Variance hVariance) n).2.1 -
          Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) star‖ ≤
        momentumDiscretizationBudget D γ h R P (G + γ * P) 0 n +
        (Real.sqrt Geometry.conditionNumber * Real.exp (-ρ * (n * h)) *
          optimizerLawDistance a (targetState star) μ νStar +
          ((2 + γ) / ρ) * Real.sqrt (Geometry.conditionNumber * Variance / (N : ℝ)) *
            (1 - Real.exp (-ρ * (n * h)))) := by
  let Q := ParticleNoiseSpace.probability (J := J) μ N
  let W := particleBrownian (J := J) μ N
  let hW := particleBrownian_isPreBrownian (J := J) μ N
  let L := momentumForceDynamics D γ
  let M := model D γ
  let H := compatibility D γ
  let Ptc := particles D γ Geometry μ hμ a Variance hVariance
  let Y : ℝ → Lp (HypocoercivePhase A × (Fin N → HypocoercivePhase (EuclideanSpace ℝ J))) 2 Q := Ptc.state
  have hY : Continuous Y := Ptc.continuous
  have heq (t : ℝ) (ht : 0 ≤ t) : Y t - Y 0 =
      (∫ r in 0..t, ULA.lpDrift Q (L.particleField N) (L.particleField_lipschitz N D.nonempty) (Y r)) +
      samplerBrownianInput Q (ParticleBrownianInput.diffusion (A := HypocoercivePhase A) N
        (momentumPhysicalDiffusion (J := J) γ)) W hW 0 t := by
    exact (Ptc.equation t ht).trans (congrArg (fun b =>
      (∫ r in 0..t, ULA.lpDrift Q (L.particleField N) (L.particleField_lipschitz N D.nonempty) (Y r)) + b)
      (ParticleBrownianInput.packed_input_eq μ N (momentumPhysicalDiffusion (J := J) γ) 0 t))
  obtain ⟨P, G, R, hP, hG, hR, refs⟩ := exists_momentum_references_from_source Q W hW D hcloud γ hγ Y hY heq
    (particleBrownian_grid_paths_independent (J := J) μ N) T
  refine ⟨P, G, R, hP, hG, hR, ?_⟩
  intro h hh hh1 n hn
  obtain ⟨Ref, href⟩ := refs h hh hh1 n hn
  let hp := momentum_parameter_lipschitz D.F D.G γ (diffusionColumns γ)
  have hcoord : (Ref.q n 0).1 = Ptc.parameter hp (n * h) := by
    rw [(href n 0).2]
    simp only [add_zero]
    exact momentumUnpackLp_parameter Q D γ (diffusionColumns γ) (Y (n * h))
  have hbound := m_mfpo_constructed_parameter_bound L M H Geometry μ hμ a
    (input γ) (input_continuous γ) (input_zero γ) N D.nonempty Variance hVariance
    νStar hνStar (targetState star) Frozen ρ hρ hmono hp hg (fun t _ ↦ target_fixed D γ star t) hV
    D Ref (initial D γ Geometry μ hμ a Variance hVariance) hcoord
  have href0 : (Ref.p 0 0, Ref.q 0 0) = initial D γ Geometry μ hμ a Variance hVariance := by
    apply Prod.ext
    · simpa only [Nat.cast_zero, zero_mul, zero_add, initial, Y, Ptc] using (href 0 0).1
    · simpa only [Nat.cast_zero, zero_mul, zero_add, initial, Y, Ptc] using (href 0 0).2
  have he0 : phaseError (initial D γ Geometry μ hμ a Variance hVariance) (Ref.p 0 0, Ref.q 0 0) = 0 := by
    rw [href0]
    simp [phaseError]
  have hstar : M.parameter (targetState star) = star := rfl
  have hresponse : (L.responseLip : ℝ) = 2 + γ := by
    change 2 + ‖γ‖ = 2 + γ
    rw [Real.norm_eq_abs, abs_of_nonneg hγ]
  simpa only [he0, hstar, hresponse] using hbound

end PBGSO.FullyConstructedMomentum
