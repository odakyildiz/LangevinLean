import PBGSO.ClosedStepIntegration

/-! # Actual difference algebra on the literal predictable-step closure
Common Brownian refinements preserve both finite inputs and outputs.
Subtraction therefore extends by limits to the entire closed domain.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- A genuine finite input and output can both be represented at any finer
compatible level, by repeating the actual past-measurable coefficients. -/
theorem finiteStep_refine_exists (G : RefiningGrids)
    (A : FiniteStepData (Z := Z) Q D G) (k : ℕ) (hk : A.1 ≤ k) :
    ∃ B : Coefficients (Z := Z) Q D (G.time k),
      coefficientStep Q D (G.time k) B (G.count k) = finiteStepInput Q D G A ∧
      stochasticStep Q D (G.time k) (G.monotone k) B (G.count k) = finiteStepOutput Q D G A := by
  obtain ⟨d, hd, hcount, htime⟩ := G.compatible A.1 k hk
  let B := refine Q D (G.time A.1) (G.time k) (G.monotone k) d hd htime A.2
  refine ⟨B, ?_, ?_⟩
  · rw [hcount]
    exact coefficientStep_refine Q D (G.time A.1) (G.time k)
      (G.monotone k) d hd htime A.2 (G.count A.1)
  · rw [hcount]
    exact stochasticStep_refine Q D (G.time A.1) (G.time k)
      (G.monotone A.1) (G.monotone k) d hd htime A.2 (G.count A.1)

/-- Finite actual predictable inputs and outputs are jointly closed under
subtraction, even when originally represented on different grid levels. -/
theorem finiteStep_sub_exists (G : RefiningGrids)
    (A B : FiniteStepData (Z := Z) Q D G) :
    ∃ C : FiniteStepData (Z := Z) Q D G,
      finiteStepInput Q D G C = finiteStepInput Q D G A - finiteStepInput Q D G B ∧
      finiteStepOutput Q D G C = finiteStepOutput Q D G A - finiteStepOutput Q D G B := by
  obtain ⟨A', hA, hA'⟩ := finiteStep_refine_exists Q D G A (max A.1 B.1) (le_max_left _ _)
  obtain ⟨B', hB, hB'⟩ := finiteStep_refine_exists Q D G B (max A.1 B.1) (le_max_right _ _)
  refine ⟨⟨max A.1 B.1, subtract Q D _ A' B'⟩, ?_, ?_⟩
  · change coefficientStep Q D _ _ _ = _
    rw [coefficientStep_sub, hA, hB]
  · change stochasticStep Q D _ _ _ _ = _
    rw [stochasticStep_sub, hA', hB']

/-- The literal closed predictable-step domain is closed under differences;
its approximation sequence is derived from closure membership. -/
theorem closedStep_sub_mem (G : RefiningGrids)
    (u v : ClosedStepDomain (Z := Z) Q D G) :
    u.val - v.val ∈ closure (range (finiteStepInput (Z := Z) Q D G)) := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G u
  obtain ⟨B, hB⟩ := exists_finiteStep_approximation Q D G v
  choose C hC using fun n => finiteStep_sub_exists Q D G (A n) (B n)
  apply isClosed_closure.mem_of_tendsto (hA.sub hB)
  apply Eventually.of_forall
  intro n
  rw [← (hC n).1]
  exact subset_closure (mem_range_self _)

def closedSub (G : RefiningGrids) (u v : ClosedStepDomain (Z := Z) Q D G) :
    ClosedStepDomain (Z := Z) Q D G := ⟨u.val - v.val, closedStep_sub_mem Q D G u v⟩

/-- Actual completed integrals preserve differences on their full literal
closed domain. No linearity or equality of limiting outputs is assumed. -/
theorem closedStepIntegral_sub (G : RefiningGrids)
    (u v : ClosedStepDomain (Z := Z) Q D G) :
    closedStepIntegral Q D G (closedSub Q D G u v) =
      closedStepIntegral Q D G u - closedStepIntegral Q D G v := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G u
  obtain ⟨B, hB⟩ := exists_finiteStep_approximation Q D G v
  choose C hC using fun n => finiteStep_sub_exists Q D G (A n) (B n)
  have hI : Tendsto (fun n => finiteStepInput Q D G (C n)) atTop
      (𝓝 (closedSub Q D G u v).val) := by
    change Tendsto _ atTop (𝓝 (u.val - v.val))
    simpa only [fun n => (hC n).1] using hA.sub hB
  have hC' := closedStepIntegral_tendsto Q D G C (closedSub Q D G u v) hI
  apply tendsto_nhds_unique hC'
  simpa only [fun n => (hC n).2] using
    (closedStepIntegral_tendsto Q D G A u hA).sub (closedStepIntegral_tendsto Q D G B v hB)

end PBGSO.FilteredBrownian
