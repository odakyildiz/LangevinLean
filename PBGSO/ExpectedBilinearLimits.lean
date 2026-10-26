import PBGSO.PartitionQuadraticEnergy
import PBGSO.PartitionVariationBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Actual expectation limits of weighted partition sums
The functions are literal pairings of actual L² variables. Their
measurability and finite-expectation properties are derived here.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.ExpectedBilinearLimits
open QuadraticMartingale
variable {Ω Z : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [MeasurableSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (W : Z →L[ℝ] Z)

/-- The original weighted spatial bilinear form. -/
def spatialPairing : Z →L[ℝ] Z →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ Z) W

@[simp] theorem spatialPairing_apply (z w : Z) : spatialPairing W z w = ⟪z, W w⟫_ℝ := rfl

/-- Actual finite sums of L² pairings have an integrable raw realization. -/
theorem pairSum_integrable (A C : ℕ → Lp Z 2 Q) (n : ℕ) :
    Integrable (fun ω => ∑ k ∈ Finset.range n, spatialPairing W (A k ω) (C k ω)) Q := by
  apply integrable_finsetSum
  intro k hk
  exact lp_weighted_pairing_integrable Q W (A k) (C k)

/-- Integrating the raw partition sum gives exactly the actual weighted L² sum. -/
theorem pairSum_integral (A C : ℕ → Lp Z 2 Q) (n : ℕ) :
    (∫ ω, ∑ k ∈ Finset.range n, spatialPairing W (A k ω) (C k ω) ∂Q) =
      ∑ k ∈ Finset.range n, weightedPairing Q W (A k) (C k) := by
  simp only [spatialPairing_apply]
  rw [integral_finsetSum _ (fun k _ => lp_weighted_pairing_integrable Q W (A k) (C k))]
  apply Finset.sum_congr rfl
  intro k hk
  exact (lp_weighted_pairing_eq_integral Q W (A k) (C k)).symm

/-- Dominated convergence for actual finite L² pair sums. The raw limiting
function becomes integrable as a conclusion, with no measurability premise. -/
theorem pairSum_limit (A C : ℕ → ℕ → Lp Z 2 Q) (count : ℕ → ℕ)
    (g : Ω → ℝ) (R : Ω → ℝ) (hR : Integrable R Q)
    (hbound : ∀ n, ∀ᵐ ω ∂Q,
      ‖∑ k ∈ Finset.range (count n), spatialPairing W (A n k ω) (C n k ω)‖ ≤ R ω)
    (hlim : ∀ᵐ ω ∂Q, Tendsto
      (fun n => ∑ k ∈ Finset.range (count n), spatialPairing W (A n k ω) (C n k ω))
        atTop (𝓝 (g ω))) :
    Integrable g Q ∧ Tendsto (fun n => ∑ k ∈ Finset.range (count n),
      weightedPairing Q W (A n k) (C n k)) atTop (𝓝 (∫ ω, g ω ∂Q)) := by
  let f (n : ℕ) (ω : Ω) := ∑ k ∈ Finset.range (count n),
    spatialPairing W (A n k ω) (C n k ω)
  have hfm (n : ℕ) : AEStronglyMeasurable (f n) Q :=
    (pairSum_integrable Q W (A n) (C n) (count n)).aestronglyMeasurable
  have hgm : AEStronglyMeasurable g Q := aestronglyMeasurable_of_tendsto_ae atTop hfm hlim
  have hgb : ∀ᵐ ω ∂Q, ‖g ω‖ ≤ R ω := by
    filter_upwards [hlim, ae_all_iff.mpr hbound] with ω hω hb
    exact le_of_tendsto' hω.norm hb
  refine ⟨hR.mono' hgm hgb, ?_⟩
  have hh := tendsto_integral_of_dominated_convergence R hfm hR hbound hlim
  simpa only [f, pairSum_integral] using hh

end PBGSO.ExpectedBilinearLimits
