import PBGSO.StoppedIntegralRealization
import PBGSO.ConstructedContinuousIntegral

/-! # Bounded stopping for every original Brownian driver
Actual continuous Brownian and integral modifications are constructed
internally and their original-driver stochastic outputs are identified.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Every original Brownian driver admits actual continuous original and
stopped martingales, with simultaneous literal stopping and exact stopped
physical-column energy. No Brownian path-continuity, noise, martingale,
isometry, uniform-integrability or stochastic-limit premise remains. -/
theorem exists_constructed_bounded_stopped_martingale (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    ∃ M N : ℝ≥0 → Ω → Z, Martingale M D.filtration Q ∧ Martingale N D.filtration Q ∧
      (∀ᵐ ω ∂Q, Continuous (fun t => M t ω)) ∧
      (∀ᵐ ω ∂Q, Continuous (fun t => N t ω)) ∧
      (∀ t, M t =ᵐ[Q] closedIntegral Q D T U t) ∧
      (∀ t, N t =ᵐ[Q] closedIntegral Q D T (boundedStoppedDomain Q D T τ hτ hstop U) t) ∧
      (∀ᵐ ω ∂Q, ∀ t, N t ω = M (min t (τ ω)) ω) ∧
      (∀ (W : Z →L[ℝ] Z), (∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ) →
        ∀ t : ℝ≥0, t ≤ T →
          (∫ ω, ⟪M (min t (τ ω)) ω, W (M (min t (τ ω)) ω)⟫_ℝ ∂Q) =
            ∫ r in Ioc (0 : ℝ) t, ∑ i,
              ∫ ω in {ω | r ≤ (τ ω : ℝ)},
                ⟪(U.val r).ofLp i ω, W ((U.val r).ofLp i ω)⟫_ℝ ∂Q) := by
  obtain ⟨M, hMM, hMC, hM⟩ := exists_constructed_continuous_martingale_version Q D T U
  obtain ⟨N, hNM, hNC, hN⟩ := exists_constructed_continuous_martingale_version Q D T
    (boundedStoppedDomain Q D T τ hτ hstop U)
  refine ⟨M, N, hMM, hNM, hMC, hNC, hM, hN, ?_, ?_⟩
  · apply continuous_versions_indistinguishable Q N (fun t ω => M (min t (τ ω)) ω) hNC
    · exact hMC.mono (fun ω hc => hc.comp (continuous_id.min continuous_const))
    · intro t
      exact (hN t).trans
        (boundedStoppedIntegral_realizes_of_continuous Q D T τ hτ hstop U M hM hMC t)
  · intro W hW t ht
    exact boundedStopped_path_isometry Q D T τ hτ hstop U M hM hMC W hW t ht

end PBGSO.FilteredBrownian
