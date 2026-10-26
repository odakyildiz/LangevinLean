import PBGSO.AdditiveCanonicalRealization
import PBGSO.NumericsTarget

/-! # Actual frozen invariance builds the additive stationary target data

The frozen sampler input is an actual continuous L² trajectory with its
integral equation and constant output law. This is the source frozen
invariance assumption, not a conclusion inferred from an empty test family.
Its constant optimiser extension is derived, primitive uniqueness identifies
the canonical target process, and every initial coupling is then realized by
the already constructed product extension. No relaxation bound or realizer
is a hypothesis.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace PBGSO
namespace AdditiveStationary
variable {Ξ A G Z X I : Type*} [MeasurableSpace Ξ]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (R : Measure Ξ) [IsProbabilityMeasure R]
  (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
  (H : AdditiveModelCompatibility L M)
  (νStar : Measure Z) [IsProbabilityMeasure νStar]
  (hνStar : MemLp (fun z : Z => z) 2 νStar) (aStar : A)
  (B : ℝ → Lp Z 2 R) (hB : Continuous B) (hB0 : B 0 = 0)

/-- Actual frozen invariant dynamics with the model's sampler drift and the
same initial-law/noise source as the canonical construction. -/
structure FrozenTrajectory where
  sampler : ℝ → Lp Z 2 (νStar.prod R)
  continuous : Continuous sampler
  initial : sampler 0 = AdditiveCanonical.initialSampler R νStar hνStar
  equation : ∀ t, 0 ≤ t → sampler t - sampler 0 =
    (∫ r in 0..t, liftMap (νStar.prod R) (L.sampler aStar) (L.sampler_state aStar)
      (sampler r)) + AdditiveCanonical.input R νStar B t
  stationary_law : ∀ t, 0 ≤ t → (νStar.prod R).map (sampler t) = νStar

variable (F : FrozenTrajectory R L νStar hνStar aStar B)
include H F

/-- The optimiser's zero observation follows from the actual frozen law. -/
theorem expectedObservation_zero
    (hg : M.meanGradient νStar aStar = 0) (t : ℝ) (ht : 0 ≤ t) :
    L.expectedObservation (νStar.prod R) aStar (F.sampler t) = 0 := by
  rw [← model_meanGradient_eq_expectedObservation (νStar.prod R) L M H,
    F.stationary_law t ht, hg]

/-- The fixed optimiser plus the actual frozen sampler satisfy the complete
mean-field integral equation; optimiser stationarity is derived. -/
theorem frozen_is_global_solution
    (hg : M.meanGradient νStar aStar = 0)
    (hfix : ∀ t, 0 ≤ t → M.optimizer t aStar 0 = 0) :
    IsGlobalAdditiveIntegralSolution (νStar.prod R) L
      (fun t => (aStar, F.sampler t)) (AdditiveCanonical.input R νStar B) where
  continuous := continuous_const.prodMk F.continuous
  equation := by
    intro t ht
    have hr : L.response (aStar, 0) = 0 := (H.response 0 le_rfl aStar 0).symm.trans (hfix 0 le_rfl)
    have hf (r : ℝ) (hr' : 0 ≤ r) :
        L.field (νStar.prod R) (aStar, F.sampler r) =
          (0, liftMap (νStar.prod R) (L.sampler aStar) (L.sampler_state aStar)
            (F.sampler r)) := by
      simp only [LipschitzDynamics.field, expectedObservation_zero R L M H νStar hνStar
        aStar B F hg r hr', hr]
    have hi : IntervalIntegrable
        (fun r => liftMap (νStar.prod R) (L.sampler aStar) (L.sampler_state aStar)
          (F.sampler r)) volume 0 t :=
      ((liftMap_lipschitz (νStar.prod R) _ _).continuous.comp F.continuous).intervalIntegrable _ _
    have hint : (∫ r in 0..t, L.field (νStar.prod R) (aStar, F.sampler r)) =
        (0, ∫ r in 0..t,
          liftMap (νStar.prod R) (L.sampler aStar) (L.sampler_state aStar) (F.sampler r)) := by
      calc
        _ = ∫ r in 0..t, (ContinuousLinearMap.inr ℝ A (Lp Z 2 (νStar.prod R)))
            (liftMap (νStar.prod R) (L.sampler aStar) (L.sampler_state aStar) (F.sampler r)) := by
          apply intervalIntegral.integral_congr
          intro r hr'
          exact hf r ((uIcc_of_le ht) ▸ hr').1
        _ = _ := (ContinuousLinearMap.inr ℝ A (Lp Z 2 (νStar.prod R))).intervalIntegral_comp_comm hi
    rw [hint]
    apply Prod.ext
    · simp
    · exact F.equation t ht

/-- The canonical target flow has the actual stationary optimiser and law;
this is proved by primitive same-input uniqueness against the frozen flow. -/
theorem canonical_target_stationary
    (hg : M.meanGradient νStar aStar = 0)
    (hfix : ∀ t, 0 ≤ t → M.optimizer t aStar 0 = 0) (t : ℝ) (ht : 0 ≤ t) :
    AdditiveCanonical.optimizer R L νStar hνStar aStar B hB hB0 t = aStar ∧
      AdditiveCanonical.law R L νStar hνStar aStar B hB hB0 t = νStar := by
  have hf := frozen_is_global_solution R L M H νStar hνStar aStar B F hg hfix
  have hc := (AdditiveCanonical.flow_spec R L νStar hνStar aStar B hB hB0).1
  have hz : AdditiveCanonical.flow R L νStar hνStar aStar B hB hB0 0 =
      (aStar, F.sampler 0) := by
    rw [(AdditiveCanonical.flow_spec R L νStar hνStar aStar B hB hB0).2, F.initial]
  have he := hc.eq_of_initial hf hz t ht
  constructor
  · exact congrArg Prod.fst he
  · change (νStar.prod R).map _ = νStar
    rw [congrArg Prod.snd he]
    exact F.stationary_law t ht

/-- The actual frozen invariant trajectory builds every stationary-target
process premise used by the finite-particle/numerical theorem. In particular,
its all-initial-couplings realizer is a conclusion of the construction. -/
def stationaryParameterData (D : TwistedGeometry A Z) (ρ : ℝ) (hρ : 0 < ρ)
    (hmono : TwistedJointMonotonicity M D ρ)
    (hprojection : LipschitzWith 1 M.parameter)
    (hg : M.meanGradient νStar aStar = 0)
    (hfix : ∀ t, 0 ≤ t → M.optimizer t aStar 0 = 0)
    (μ : Measure Z) [IsProbabilityMeasure μ] (hμ : MemLp (fun z : Z => z) 2 μ) (a : A) :
    StationaryParameterData M D (AdditiveCanonical.optimizer R L μ hμ a B hB hB0)
      (AdditiveCanonical.law R L μ hμ a B hB hB0) ρ := by
  have hmoment : HasFiniteSecondMoment νStar :=
    (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).mp hνStar
  have hint : Integrable
      (fun z => M.observation (M.parameter aStar) (M.position z)) νStar := by
    simp_rw [H.observation]
    exact observation_integrable_of_lipschitz νStar _ (L.observation_state aStar) hmoment
  refine
    { projection := hprojection
      tests := ∅
      pairTests := {couplingQuadratic D}
      mean_solution := (AdditiveCanonical.flow_spec R L μ hμ a B hB hB0).1.isWeakSolution_empty M H
      sStar := aStar
      νStar := νStar
      frozen_stationary := ?_
      gradient_integrable := hint
      gradient_zero := hg
      optimizer_fixed := hfix
      quadratic_test := Set.mem_singleton _
      rate_positive := hρ
      joint_monotonicity := hmono
      realize := ?_ }
  · exact
      { probability := inferInstance
        second_moment := hmoment
        test_integrable := by simp
        generator_integrable := by simp
        generator_zero := by simp }
  · intro c
    let c' : ULA.Coupling μ νStar :=
      ⟨c.joint, c.fst.trans (AdditiveCanonical.law_zero R L μ hμ a B hB hB0), c.snd⟩
    obtain ⟨Λ, hc, hzero⟩ := AdditiveCanonical.realize_all_initial_couplings R L M H D
      μ νStar hμ hνStar a aStar B hB hB0 c'
    have hs := canonical_target_stationary R L M H νStar hνStar aStar B hB hB0 F hg hfix
    refine ⟨Λ, ?_, hzero⟩
    refine
      { coupling := ?_
        test_integrable := hc.test_integrable
        generator_integrable := ?_
        forward_equation := ?_ }
    · intro t ht
      simpa only [(hs t ht).2] using hc.coupling t ht
    · intro φ hφ t ht
      simpa only [(hs t ht).1] using hc.generator_integrable φ hφ t ht
    · intro φ hφ t ht
      simpa only [(hs t ht).1] using hc.forward_equation φ hφ t ht

end AdditiveStationary
end PBGSO
