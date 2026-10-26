import PBGSO.FilteredWeightedCompletion
import PBGSO.ClosedIsometricExtension
import Mathlib.Topology.Sequences

/-! # Integration on the literal closed predictable-step domain -/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
open PBGSO.QuadraticMartingale
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

abbrev FiniteStepData (G : RefiningGrids) := Σ n, Coefficients (Z := Z) Q D (G.time n)

def finiteStepInput (G : RefiningGrids) (A : FiniteStepData (Z := Z) Q D G) :
    Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) :=
  coefficientStep Q D (G.time A.1) A.2 (G.count A.1)

def finiteStepOutput (G : RefiningGrids) (A : FiniteStepData (Z := Z) Q D G) : Lp Z 2 Q :=
  stochasticStep Q D (G.time A.1) (G.monotone A.1) A.2 (G.count A.1)

theorem finiteStep_distance (G : RefiningGrids) (A C : FiniteStepData (Z := Z) Q D G) :
    dist (finiteStepOutput Q D G A) (finiteStepOutput Q D G C) =
      dist (finiteStepInput Q D G A) (finiteStepInput Q D G C) :=
  stochasticStep_dist_cross Q D G A.1 C.1 A.2 C.2

/-- Literal topological closure of every finite predictable-step input.
This definition does not assume any approximation sequence for its members. -/
abbrev ClosedStepDomain (G : RefiningGrids) :=
  ClosedIsometricExtension.Domain (finiteStepInput (Z := Z) Q D G)

/-- Actual Brownian integration on the entire closed step domain. -/
def closedStepIntegral (G : RefiningGrids) : ClosedStepDomain (Z := Z) Q D G → Lp Z 2 Q :=
  ClosedIsometricExtension.extend (finiteStepInput Q D G) (finiteStepOutput Q D G)

theorem closedStepIntegral_isometry (G : RefiningGrids) :
    Isometry (closedStepIntegral (Z := Z) Q D G) :=
  ClosedIsometricExtension.extend_isometry (finiteStepInput Q D G) (finiteStepOutput Q D G)
    (finiteStep_distance Q D G)

theorem closedStepIntegral_tendsto (G : RefiningGrids) (A : ℕ → FiniteStepData (Z := Z) Q D G)
    (u : ClosedStepDomain (Z := Z) Q D G)
    (hu : Tendsto (fun n => finiteStepInput Q D G (A n)) atTop (𝓝 u.val)) :
    Tendsto (fun n => finiteStepOutput Q D G (A n)) atTop (𝓝 (closedStepIntegral Q D G u)) :=
  ClosedIsometricExtension.tendsto_extend (finiteStepInput Q D G) (finiteStepOutput Q D G)
    (finiteStep_distance Q D G) A u hu

/-- Every member of the literal closure has genuine finite-step
approximations, with no density premise. -/
theorem exists_finiteStep_approximation (G : RefiningGrids) (u : ClosedStepDomain (Z := Z) Q D G) :
    ∃ A : ℕ → FiniteStepData (Z := Z) Q D G,
      Tendsto (fun n => finiteStepInput Q D G (A n)) atTop (𝓝 u.val) := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp u.property
  choose A hA using hv
  exact ⟨A, (show (fun n => finiteStepInput Q D G (A n)) = v from funext hA) ▸ hlim⟩

/-- The previously constructed compatible-grid domain embeds into the
literal closed domain by its actual coefficient approximations. -/
def toClosedStepDomain (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q D G) :
    ClosedStepDomain (Z := Z) Q D G := by
  refine ⟨u.val, ?_⟩
  obtain ⟨A, hA⟩ := u.property
  apply isClosed_closure.mem_of_tendsto hA
  exact Eventually.of_forall (fun n => subset_closure (show coefficientStep Q D (G.time n) (A n)
    (G.count n) ∈ Set.range (finiteStepInput Q D G) from ⟨⟨n, A n⟩, rfl⟩))

/-- The closure construction agrees exactly with the previous actual
integral, retaining its weighted, martingale and pullback APIs. -/
theorem closedStepIntegral_eq_stochasticIntegral (G : RefiningGrids)
    (u : IntegralDomain (Z := Z) Q D G) :
    closedStepIntegral Q D G (toClosedStepDomain Q D G u) = stochasticIntegral Q D G u := by
  obtain ⟨A, hA⟩ := u.property
  have hc := closedStepIntegral_tendsto Q D G (fun n => ⟨n, A n⟩) (toClosedStepDomain Q D G u) hA
  exact tendsto_nhds_unique hc (stochasticIntegral_tendsto Q D G u A hA)

/-- Exact weighted Itô isometry on the literal closed step domain. -/
theorem closedStepIntegral_weighted (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (G : RefiningGrids) (u : ClosedStepDomain (Z := Z) Q D G) :
    weightedPairing Q W (closedStepIntegral Q D G u) (closedStepIntegral Q D G u) =
      ⟪u.val, (columnWeight (I := I) Q W).compLpL 2 (volume : Measure ℝ) u.val⟫_ℝ := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G u
  have hI := closedStepIntegral_tendsto Q D G A u hA
  have hl := (weightedPairing Q W).continuous₂.tendsto _ |>.comp (hI.prodMk_nhds hI)
  have hr := Filter.Tendsto.inner (𝕜 := ℝ) hA
    (((columnWeight (I := I) Q W).compLpL 2 (volume : Measure ℝ)).continuous.tendsto u.val |>.comp hA)
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall (fun n =>
    (stochasticStep_weighted Q D W hW (G.time (A n).1) (G.monotone (A n).1) (A n).2
      (G.count (A n).1)).symm)))

end PBGSO.FilteredBrownian
