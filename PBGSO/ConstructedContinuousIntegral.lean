import PBGSO.ContinuousBrownianDriver
import PBGSO.ClosedIntegralContinuousVersion
import PBGSO.FilteredIntegralModification

/-! # Actual continuous martingale versions without a Brownian path premise
A strict-past continuous Brownian modification is constructed internally.
Its valid Driver has the exact original filtration, and actual integral
invariance identifies the resulting paths with the original computed noise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Every actual completed integral admits an actual continuous martingale
modification in its original filtration. No Brownian path-continuity,
computed-output-matching or filtration-completion hypothesis is supplied. -/
theorem exists_constructed_continuous_martingale_version (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    ∃ M : ℝ≥0 → Ω → Z, Martingale M D.filtration Q ∧
      (∀ᵐ ω ∂Q, Continuous (fun t => M t ω)) ∧
      ∀ t, M t =ᵐ[Q] closedIntegral Q D T U t := by
  let E := continuousDriver Q D
  let V := enlargeClosedDomain Q D E (fun _ => le_refl _) (dyadicGrids T) U
  obtain ⟨M, hM, hc, he⟩ := exists_continuous_martingale_version Q E T V
    (continuousDriver_joint_continuous Q D)
  refine ⟨M, hM, hc, ?_⟩
  intro t
  have hi : closedIntegral Q E T V t = closedIntegral Q D T U t :=
    closedIntegral_congr_ae Q D E
      (fun i r => (continuousDriver_process_ae Q D i r).symm) (fun _ => le_refl _) T U t
  exact (he t).trans (Eventually.of_forall (fun ω => congrArg (fun A : Lp Z 2 Q => A ω) hi))

end PBGSO.FilteredBrownian
