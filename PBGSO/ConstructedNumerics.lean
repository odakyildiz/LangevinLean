import PBGSO.ConstructedParameterBound
import PBGSO.HOLPullback
import PBGSO.ParticleNoiseSpace

/-! # Numerical target bounds on the actual constructed particle sample space
The source relaxation and particle interaction terms come from actual
constructed additive processes and an actual frozen invariant trajectory.
Parameter-law equality is proved by pointwise projection. The remaining
implementation linkage is an explicit equality of L² coordinates of the
integral reference, rather than a supplied equality of output laws.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace InnerProductSpace
namespace PBGSO
open Methods

section BrownianPullback
variable {Ω : Type*} [MeasurableSpace Ω]
  (J : Type*) [Fintype J]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {f : Ω → ULA.CanonicalBrownian.VectorSample J}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability J))

/-- Actual Brownian coordinates pulled back along the whole-noise source. -/
def canonicalPullbackCoordinate (_hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability J))
    (i : J) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ULA.CanonicalBrownian.coordinate i t (f ω)

/-- Brownian finite-dimensional laws are preserved by the actual pullback. -/
theorem canonicalPullbackCoordinate_isPreBrownian (i : J) :
    IsPreBrownianReal (canonicalPullbackCoordinate J hf i) Q where
  hasLaw s := (ULA.CanonicalBrownian.coordinate_isPreBrownian i).hasLaw s |>.comp hf.hasLaw

/-- The complete grid paths are independent on the actual source, derived
from their true joint law under the whole canonical-noise pullback. -/
theorem canonicalPullbackCoordinate_grid_paths_independent (h : ℝ≥0) :
    iIndepFun (fun i ω (n : ℕ) ↦ canonicalPullbackCoordinate J hf i ((n : ℝ≥0) * h) ω) Q := by
  let C := ULA.CanonicalBrownian.vectorProbability J
  let X := fun i (ω : ULA.CanonicalBrownian.VectorSample J) (n : ℕ) ↦
    ULA.CanonicalBrownian.coordinate i ((n : ℝ≥0) * h) ω
  have hX (i : J) : HasLaw (X i) (C.map (X i)) C :=
    ⟨(Measurable.of_eval fun n ↦ (ULA.CanonicalBrownian.process_measurable _).comp
      (measurable_pi_apply i)).aemeasurable, rfl⟩
  have hXi := ULA.CanonicalBrownian.coordinate_grid_paths_independent J h
  have hall := hXi.hasLaw_pi hX
  have hfull := hall.comp hf.hasLaw
  exact (iIndepFun_iff_hasLaw_pi_pi (fun i ↦ (hX i).comp hf.hasLaw)).mpr hfull

end BrownianPullback
section ConstructedTarget
variable {S A Z X Y J K : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [Fintype J] [DecidableEq J] [Fintype K]
  (L : LipschitzDynamics S Z A) (M : Model S A Z Y K)
  (H : AdditiveModelCompatibility L M) (D : TwistedGeometry S Z)
  (μ : Measure Z) [IsProbabilityMeasure μ] (hμ : MemLp (fun z : Z ↦ z) 2 μ) (a : S)
  (B : ℝ → Lp Z 2 (ULA.CanonicalBrownian.vectorProbability J))
  (hB : Continuous B) (hB0 : B 0 = 0)
  (N : ℕ) (hN : 0 < N) (Variance : ℝ)
  (hVariance : ∀ r, 0 ≤ r →
    (∫ z, ‖M.observation
      (M.parameter (AdditiveCanonical.optimizer (ULA.CanonicalBrownian.vectorProbability J)
        L μ hμ a B hB hB0 r)) (M.position z) -
      M.meanGradient (AdditiveCanonical.law (ULA.CanonicalBrownian.vectorProbability J)
        L μ hμ a B hB hB0 r)
        (AdditiveCanonical.optimizer (ULA.CanonicalBrownian.vectorProbability J) L μ hμ a B hB hB0 r)‖ ^ 2
      ∂AdditiveCanonical.law (ULA.CanonicalBrownian.vectorProbability J) L μ hμ a B hB hB0 r) ≤ Variance)
  (νStar : Measure Z) [IsProbabilityMeasure νStar]
  (hνStar : MemLp (fun z : Z ↦ z) 2 νStar) (aStar : S)
  (Frozen : AdditiveStationary.FrozenTrajectory (ULA.CanonicalBrownian.vectorProbability J)
    L νStar hνStar aStar B)
  (ρ : ℝ) (hρ : 0 < ρ) (hmono : TwistedJointMonotonicity M D ρ)
  (hparam : LipschitzWith 1 M.parameter)
  (hg : M.meanGradient νStar aStar = 0)
  (hfix : ∀ t, 0 ≤ t → M.optimizer t aStar 0 = 0) (hV : 0 ≤ Variance)

/-- The actual Brownian-coordinate process on the independent particle
initial/noise source. Its complete source law is canonical by construction. -/
def particleBrownian (i : Fin N × J) (t : ℝ≥0)
    (ω : Fin N → Z × ULA.CanonicalBrownian.VectorSample J) : ℝ :=
  canonicalPullbackCoordinate (Fin N × J) (ParticleNoiseSpace.noise_preserving (J := J) μ N) i t ω

theorem particleBrownian_isPreBrownian (i : Fin N × J) :
    IsPreBrownianReal (particleBrownian (J := J) μ N i) (ParticleNoiseSpace.probability (J := J) μ N) :=
  canonicalPullbackCoordinate_isPreBrownian (Fin N × J) (ParticleNoiseSpace.noise_preserving μ N) i

theorem particleBrownian_grid_paths_independent (h : ℝ≥0) :
    iIndepFun (fun i ω (n : ℕ) ↦ particleBrownian (J := J) μ N i ((n : ℝ≥0) * h) ω)
      (ParticleNoiseSpace.probability (J := J) μ N) :=
  canonicalPullbackCoordinate_grid_paths_independent (Fin N × J) (ParticleNoiseSpace.noise_preserving μ N) h

include Frozen hρ hmono hg hfix hV

/-- M-MFPO parameter error combines the proved Gaussian discretization rate
with the actually constructed source parameter bound. The only remaining
reference linkage is the displayed actual L² coordinate identity; no
output-law compatibility or weak particle-process premise is supplied. -/
theorem m_mfpo_constructed_parameter_bound
    (Force : ParticleForceData A X (EuclideanSpace ℝ (Fin N × J)) N)
    {γ h R P F : ℝ} {n : ℕ}
    (Ref : MomentumIntegralReference (ParticleNoiseSpace.probability (J := J) μ N)
      (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
      Force γ h R P F n)
    (z : ((Lp A 2 (ParticleNoiseSpace.probability (J := J) μ N)) ×
        Lp (EuclideanSpace ℝ (Fin N × J)) 2 (ParticleNoiseSpace.probability (J := J) μ N)) ×
      ((Lp A 2 (ParticleNoiseSpace.probability (J := J) μ N)) ×
        Lp (EuclideanSpace ℝ (Fin N × J)) 2 (ParticleNoiseSpace.probability (J := J) μ N)))
    (coordinate : (Ref.q n 0).1 =
      (AdditiveConstructed.particleRealization (ULA.CanonicalBrownian.vectorProbability J)
        L M H D μ hμ a B hB hB0 N hN Variance hVariance).parameter hparam (n * h)) :
    ‖(momentumParticleIterate (ParticleNoiseSpace.probability (J := J) μ N)
        (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N)
        Force γ h z n).2.1 - Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N)
          (M.parameter aStar)‖ ≤
      momentumDiscretizationBudget Force γ h R P F (phaseError z (Ref.p 0 0, Ref.q 0 0)) n +
      (Real.sqrt D.conditionNumber * Real.exp (-ρ * (n * h)) * optimizerLawDistance a aStar μ νStar +
        ((L.responseLip : ℝ) / ρ) * Real.sqrt (D.conditionNumber * Variance / (N : ℝ)) *
          (1 - Real.exp (-ρ * (n * h)))) := by
  have hn := MomentumIntegralReference.finite_bound (ParticleNoiseSpace.probability (J := J) μ N)
    (particleBrownian (J := J) μ N) (particleBrownian_isPreBrownian (J := J) μ N) Force Ref z
  have hc := AdditiveConstructed.parameter_bound (ULA.CanonicalBrownian.vectorProbability J)
    L M H D μ hμ a B hB hB0 N hN Variance hVariance νStar hνStar aStar Frozen
    ρ hρ hmono hparam hg hfix hV (n * h) (mul_nonneg (Nat.cast_nonneg n) Ref.step_pos.le)
  rw [← coordinate] at hc
  exact (momentum_parameter_triangle (ParticleNoiseSpace.probability (J := J) μ N) _
    (Ref.p n 0, Ref.q n 0) (M.parameter aStar)).trans (add_le_add hn hc)

/-- HOL-MYPGD parameter error on the actual random-initial particle space.
Its full correlated Gaussian innovation array is pulled back along the
proved actual-noise projection, and the source target/particle laws are
constructed internally. The remaining coordinate identity is explicit. -/
theorem hol_mypgd_constructed_parameter_bound
    (Force : ParticleForceData A X (EuclideanSpace ℝ (Fin N × J)) N)
    {α γ Fθ FG U V C : ℝ} {h : ℝ≥0} {n : ℕ}
    (Ref : HigherOrderPullbackIntegralReference (Fin N × J)
      (ParticleNoiseSpace.probability (J := J) μ N) (ParticleNoiseSpace.noise_preserving (J := J) μ N)
      Force α γ Fθ FG U V C h n)
    (z : HOLState (Lp A 2 (ParticleNoiseSpace.probability (J := J) μ N))
      (Lp (EuclideanSpace ℝ (Fin N × J)) 2 (ParticleNoiseSpace.probability (J := J) μ N)))
    (coordinate : (Ref.r n 0).1 =
      (AdditiveConstructed.particleRealization (ULA.CanonicalBrownian.vectorProbability J)
        L M H D μ hμ a B hB hB0 N hN Variance hVariance).parameter hparam (n * (h : ℝ))) :
    ‖(higherOrderPullbackParticleIterate (Fin N × J) (ParticleNoiseSpace.probability (J := J) μ N)
        (ParticleNoiseSpace.noise_preserving (J := J) μ N) Force α γ h z n).1 -
      Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) (M.parameter aStar)‖ ≤
      higherOrderDiscretizationBudget (Fin N × J) Force α γ Fθ FG U V C h
        (holError z (Ref.r 0 0)) n +
      (Real.sqrt D.conditionNumber * Real.exp (-ρ * (n * (h : ℝ))) * optimizerLawDistance a aStar μ νStar +
        ((L.responseLip : ℝ) / ρ) * Real.sqrt (D.conditionNumber * Variance / (N : ℝ)) *
          (1 - Real.exp (-ρ * (n * (h : ℝ))))) := by
  have hn := HigherOrderPullbackIntegralReference.finite_bound (Fin N × J)
    (ParticleNoiseSpace.probability (J := J) μ N) (ParticleNoiseSpace.noise_preserving (J := J) μ N)
    Force Ref z
  have hc := AdditiveConstructed.parameter_bound (ULA.CanonicalBrownian.vectorProbability J)
    L M H D μ hμ a B hB hB0 N hN Variance hVariance νStar hνStar aStar Frozen
    ρ hρ hmono hparam hg hfix hV (n * (h : ℝ)) (by positivity)
  rw [← coordinate] at hc
  exact (higherOrder_parameter_triangle (ParticleNoiseSpace.probability (J := J) μ N) _
    (Ref.r n 0) (M.parameter aStar)).trans (add_le_add hn hc)

/-- The actually constructed HOL target bound to an original target adds
only the separately proved observation-coupling bias. The original and
surrogate target variables are an actual same-space L² coupling. -/
theorem hol_mypgd_constructed_original_parameter_bound
    (Force : ParticleForceData A X (EuclideanSpace ℝ (Fin N × J)) N)
    {α γ Fθ FG U V C : ℝ} {h : ℝ≥0} {n : ℕ}
    (Ref : HigherOrderPullbackIntegralReference (Fin N × J)
      (ParticleNoiseSpace.probability (J := J) μ N) (ParticleNoiseSpace.noise_preserving (J := J) μ N)
      Force α γ Fθ FG U V C h n)
    (z : HOLState (Lp A 2 (ParticleNoiseSpace.probability (J := J) μ N))
      (Lp (EuclideanSpace ℝ (Fin N × J)) 2 (ParticleNoiseSpace.probability (J := J) μ N)))
    (coordinate : (Ref.r n 0).1 =
      (AdditiveConstructed.particleRealization (ULA.CanonicalBrownian.vectorProbability J)
        L M H D μ hμ a B hB hB0 N hN Variance hVariance).parameter hparam (n * (h : ℝ)))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : A → A) (fobs : E → A) (obsLip : ℝ≥0) (hobs : LipschitzWith obsLip fobs)
    (m ε : ℝ) (hm : 0 < m) (star : A) (hstar : g star = 0)
    (hstrong : m * ‖M.parameter aStar - star‖ ^ 2 ≤
      ⟪M.parameter aStar - star, g (M.parameter aStar) - g star⟫_ℝ)
    (Xoriginal Xsurrogate : Lp E 2 (ParticleNoiseSpace.probability (J := J) μ N))
    (hgradient : g (M.parameter aStar) =
      ∫ ω, fobs (Xoriginal ω) ∂ParticleNoiseSpace.probability (J := J) μ N)
    (hsurrogate : (∫ ω, fobs (Xsurrogate ω) ∂ParticleNoiseSpace.probability (J := J) μ N) = 0)
    (hcoupling : ‖Xoriginal - Xsurrogate‖ ≤ ε) :
    ‖(higherOrderPullbackParticleIterate (Fin N × J) (ParticleNoiseSpace.probability (J := J) μ N)
        (ParticleNoiseSpace.noise_preserving (J := J) μ N) Force α γ h z n).1 -
      Lp.const 2 (ParticleNoiseSpace.probability (J := J) μ N) star‖ ≤
      higherOrderDiscretizationBudget (Fin N × J) Force α γ Fθ FG U V C h
        (holError z (Ref.r 0 0)) n +
      (Real.sqrt D.conditionNumber * Real.exp (-ρ * (n * (h : ℝ))) * optimizerLawDistance a aStar μ νStar +
        ((L.responseLip : ℝ) / ρ) * Real.sqrt (D.conditionNumber * Variance / (N : ℝ)) *
          (1 - Real.exp (-ρ * (n * (h : ℝ))))) + (obsLip : ℝ) * ε / m := by
  have hn := hol_mypgd_constructed_parameter_bound L M H D μ hμ a B hB hB0 N hN Variance hVariance
    νStar hνStar aStar Frozen ρ hρ hmono hparam hg hfix hV Force Ref z coordinate
  have hb := hybrid_target_bias (ParticleNoiseSpace.probability (J := J) μ N)
    g fobs obsLip hobs m ε hm (M.parameter aStar) star hstar hstrong
    Xoriginal Xsurrogate hgradient hsurrogate hcoupling
  exact (numerical_target_shift (ParticleNoiseSpace.probability (J := J) μ N) _
    (M.parameter aStar) star).trans (add_le_add hn hb)


end ConstructedTarget
end PBGSO
