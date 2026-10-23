import AverageLMC.LaplacianWeightedTest
import UnadjustedLangevin.Generator

set_option linter.style.header false

/-!
# Compact `C²` observations and their true Langevin generators

Both observations are bounded and uniformly continuous, under exactly a
Lipschitz gradient for the potential. Their weighted expectations are
therefore uniformly continuous on the actual `L²` state space.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace AverageLMC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

theorem continuous_langevinGenerator_compact_test
    (f : H → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient f))
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) : Continuous (ULA.langevinGenerator f φ) := by
  unfold ULA.langevinGenerator
  exact continuous_finsetSum _ (fun i _ ↦ ULA.continuous_directionalGenerator f L hLip φ hφ _)

theorem hasCompactSupport_langevinGenerator_compact_test
    (f φ : H → ℝ) (hc : HasCompactSupport φ) :
    HasCompactSupport (ULA.langevinGenerator f φ) := by
  classical
  have hs (s : Finset (Fin (Module.finrank ℝ H))) : HasCompactSupport
      (fun x ↦ ∑ i ∈ s, ULA.directionalGenerator f φ (stdOrthonormalBasis ℝ H i) x) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change IsCompact _
      simp
    | @insert i s hi ih =>
      have he : (fun x ↦ ∑ j ∈ insert i s,
          ULA.directionalGenerator f φ (stdOrthonormalBasis ℝ H j) x) =
          ULA.directionalGenerator f φ (stdOrthonormalBasis ℝ H i) +
            (fun x ↦ ∑ j ∈ s, ULA.directionalGenerator f φ (stdOrthonormalBasis ℝ H j) x) := by
        funext x
        simp only [Finset.sum_insert hi, Pi.add_apply]
      rw [he]
      exact (ULA.hasCompactSupport_directionalGenerator f φ hc (stdOrthonormalBasis ℝ H i)).add ih
  exact hs Finset.univ

theorem compact_test_bounded_uniformContinuous
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    UniformContinuous φ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |φ x| ≤ C := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  refine ⟨hc.uniformContinuous_of_continuous hφ.continuous,
    max 0 C, le_max_left _ _, fun x ↦ ?_⟩
  exact (show |φ x| ≤ C by simpa only [Real.norm_eq_abs] using hC x).trans (le_max_right _ _)

theorem compact_test_generator_bounded_uniformContinuous
    (f : H → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient f))
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    UniformContinuous (ULA.langevinGenerator f φ) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |ULA.langevinGenerator f φ x| ≤ C := by
  have hcont := continuous_langevinGenerator_compact_test f L hLip φ hφ
  have hcomp := hasCompactSupport_langevinGenerator_compact_test f φ hc
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support hcomp
  refine ⟨hcomp.uniformContinuous_of_continuous hcont,
    max 0 C, le_max_left _ _, fun x ↦ ?_⟩
  exact (show |ULA.langevinGenerator f φ x| ≤ C by
    simpa only [Real.norm_eq_abs] using hC x).trans (le_max_right _ _)

/-- The compact test and its generator give the two uniformly continuous
observations required by the actual Euler-to-Dynkin limit. -/
theorem lpWeightedTest_compact_test_uniformContinuous
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (w : Ω → ℝ) (hw : Measurable w) (A : ℝ) (hA : 0 ≤ A)
    (hwA : ∀ᵐ a ∂P, |w a| ≤ A)
    (f : H → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient f))
    (φ : H → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    UniformContinuous (lpWeightedTest P w φ) ∧
      UniformContinuous (lpWeightedTest P w (ULA.langevinGenerator f φ)) := by
  obtain ⟨hUC, C, hC, hbound⟩ := compact_test_bounded_uniformContinuous φ hφ hc
  obtain ⟨hUCg, D, hD, hboundg⟩ :=
    compact_test_generator_bounded_uniformContinuous f L hLip φ hφ hc
  exact ⟨lpWeightedTest_uniformContinuous P w hw A hA hwA φ hUC C hC hbound,
    lpWeightedTest_uniformContinuous P w hw A hA hwA _ hUCg D hD hboundg⟩

end AverageLMC
