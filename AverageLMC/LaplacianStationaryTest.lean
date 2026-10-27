import AverageLMC.Assumptions
import AverageLMC.LaplacianWeightedTest

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace AverageLMC

variable {Ω H E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology H] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Stationarity transports every genuine L² observation to the actual
process, without an assumed moment estimate. -/
theorem stationary_observation_memLp
    (P : Measure Ω) (π : Measure H) (F : H → E) (hF : MemLp F 2 π)
    (Y : Lp H 2 P) (hlaw : P.map Y = π) : MemLp (fun a ↦ F (Y a)) 2 P := by
  rw [← hlaw] at hF
  exact hF.comp_of_map (Lp.aestronglyMeasurable Y).aemeasurable

/-- The L² vector represented by an observation of a stationary state. -/
def stationaryObservation
    (P : Measure Ω) (π : Measure H) (F : H → E) (hF : MemLp F 2 π)
    (Y : Lp H 2 P) (hlaw : P.map Y = π) : Lp E 2 P :=
  (stationary_observation_memLp P π F hF Y hlaw).toLp (fun a ↦ F (Y a))

omit [SecondCountableTopology H] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem stationaryObservation_coe
    (P : Measure Ω) (π : Measure H) (F : H → E) (hF : MemLp F 2 π)
    (Y : Lp H 2 P) (hlaw : P.map Y = π) :
    stationaryObservation P π F hF Y hlaw =ᵐ[P] fun a ↦ F (Y a) :=
  MemLp.coeFn_toLp _

omit [SecondCountableTopology H] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Its actual L² norm is exactly the Gibbs observation moment. -/
theorem stationaryObservation_norm_sq
    (P : Measure Ω) (π : Measure H) (F : H → E) (hFc : Continuous F) (hF : MemLp F 2 π)
    (Y : Lp H 2 P) (hlaw : P.map Y = π) :
    ‖stationaryObservation P π F hF Y hlaw‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ a, ‖F (Y a)‖ ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [stationaryObservation_coe P π F hF Y hlaw] with a ha
      rw [ha, real_inner_self_eq_norm_sq]
    _ = _ := by
      rw [← hlaw]
      simpa only [Pi.pow_apply] using (integral_map (Lp.aestronglyMeasurable Y).aemeasurable
        (hFc.norm.pow 2).aestronglyMeasurable).symm

omit [SecondCountableTopology H] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Squared Gibbs approximation error is exactly the squared L² error on
every actual stationary marginal, including differences of observations. -/
theorem stationaryObservation_sub_norm_sq
    (P : Measure Ω) (π : Measure H) (F G : H → E)
    (hFc : Continuous F) (hGc : Continuous G) (hF : MemLp F 2 π) (hG : MemLp G 2 π)
    (Y : Lp H 2 P) (hlaw : P.map Y = π) :
    ‖stationaryObservation P π F hF Y hlaw - stationaryObservation P π G hG Y hlaw‖ ^ 2 =
      ∫ x, ‖F x - G x‖ ^ 2 ∂π := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ a, ‖F (Y a) - G (Y a)‖ ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (stationaryObservation P π F hF Y hlaw)
        (stationaryObservation P π G hG Y hlaw),
        stationaryObservation_coe P π F hF Y hlaw,
        stationaryObservation_coe P π G hG Y hlaw] with a hs hf hg
      simp only [hs, Pi.sub_apply, hf, hg, real_inner_self_eq_norm_sq]
    _ = _ := by
      rw [← hlaw]
      simpa only [Pi.pow_apply, Pi.sub_apply] using
        (integral_map (Lp.aestronglyMeasurable Y).aemeasurable
          ((hFc.sub hGc).norm.pow 2).aestronglyMeasurable).symm

section Coordinates
variable {p : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- A vector L² pairing equals the finite sum of its genuine scalar weighted
expectations. This converts compact coordinate Dynkin formulas into a vector
duality estimate without dimension losses. -/
theorem stationaryObservation_inner_eq_sum
    (π : Measure (State p)) (F : State p → State p) (hFc : Continuous F)
    (hF : MemLp F 2 π) (Y : Lp (State p) 2 P) (hlaw : P.map Y = π)
    (Ψ : Lp (State p) 2 P) :
    inner ℝ Ψ (stationaryObservation P π F hF Y hlaw) =
      ∑ j : Fin p, lpWeightedTest P (fun a ↦ Ψ a j) (fun x ↦ F x j) Y := by
  have hObs := stationary_observation_memLp P π F hF Y hlaw
  have hdom := (Lp.memLp Ψ).norm.integrable_mul hObs.norm
  have hi (j : Fin p) : Integrable (fun a ↦ Ψ a j * F (Y a) j) P := by
    apply hdom.mono' _ (ae_of_all _ fun a ↦ ?_)
    · exact (((EuclideanSpace.proj j).continuous.measurable.comp
        (Lp.stronglyMeasurable Ψ).measurable).mul
        ((EuclideanSpace.proj j).continuous.measurable.comp
          (hFc.measurable.comp (Lp.stronglyMeasurable Y).measurable))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (Ψ a) j)
        (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (F (Y a)) j)
        (abs_nonneg _) (norm_nonneg _)
  rw [L2.inner_def]
  calc
    _ = ∫ a, ∑ j : Fin p, Ψ a j * F (Y a) j ∂P := by
      apply integral_congr_ae
      filter_upwards [stationaryObservation_coe P π F hF Y hlaw] with a ha
      rw [ha]
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun j _ ↦ hi j)]
      rfl

end Coordinates
end AverageLMC
