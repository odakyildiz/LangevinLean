import PBGSO.PredictableIntegralTransport

/-! # Computed integrals are invariant under Brownian process modifications
Fixed-time almost-everywhere coordinate equality is sufficient. No equality
of whole raw paths or of computed stochastic outputs is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D E : Driver (I := I) Q)
  (hprocess : ∀ i t, D.process i t =ᵐ[Q] E.process i t)
  (henlarge : ∀ t, D.filtration t ≤ E.filtration t)

include hprocess henlarge

/-- Finite actual stochastic sums depend only on the Brownian coordinates'
fixed-time random variables, even when their raw path representatives differ. -/
theorem stochasticStep_congr_ae (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    stochasticStep Q E τ hτ (enlargeCoefficients Q D E henlarge τ A) n =
      stochasticStep Q D τ hτ A n := by
  have hcoord : ∀ᵐ ω ∂Q, ∀ k : Fin n, ∀ i,
      D.process i (τ k) ω = E.process i (τ k) ω ∧
      D.process i (τ (k + 1)) ω = E.process i (τ (k + 1)) ω :=
    ae_all_iff.mpr (fun k => ae_all_iff.mpr (fun i =>
      (hprocess i (τ k)).and (hprocess i (τ (k + 1)))))
  apply Lp.ext
  filter_upwards [(gridSum_memLp Q E τ hτ (enlargeCoefficients Q D E henlarge τ A) n).coeFn_toLp,
    (gridSum_memLp Q D τ hτ A n).coeFn_toLp, hcoord] with ω hE hD hc
  change (stochasticStep Q E τ hτ _ n) ω = _ at hE
  change (stochasticStep Q D τ hτ A n) ω = _ at hD
  rw [hE, hD]
  unfold gridSum
  apply Finset.sum_congr rfl
  intro k _
  unfold noiseStep PredictableIsometry.stepSum
  apply Finset.sum_congr rfl
  intro i _
  simp only [increment, enlargeCoefficients, enlargeCoefficient]
  rw [← (hc k i).1, ← (hc k i).2]

/-- Actual closed-domain stochastic integration is invariant under a valid
Brownian modification and filtration enlargement. -/
theorem closedStepIntegral_congr_ae (G : RefiningGrids)
    (u : ClosedStepDomain (Z := Z) Q D G) :
    closedStepIntegral Q E G (enlargeClosedDomain Q D E henlarge G u) =
      closedStepIntegral Q D G u := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G u
  let B (n : ℕ) : FiniteStepData (Z := Z) Q E G :=
    ⟨(A n).1, enlargeCoefficients Q D E henlarge (G.time (A n).1) (A n).2⟩
  have h1 := closedStepIntegral_tendsto Q E G B (enlargeClosedDomain Q D E henlarge G u) hA
  have h2 := closedStepIntegral_tendsto Q D G A u hA
  apply tendsto_nhds_unique h1
  simpa only [B, finiteStepOutput, stochasticStep_congr_ae Q D E hprocess henlarge] using h2

/-- Same represented integrand, valid modified Brownian coordinates, same
computed integral. This derives the stochastic-output identity. -/
theorem closedStepIntegral_eq_of_congr_ae (G : RefiningGrids)
    (u : ClosedStepDomain (Z := Z) Q D G) (v : ClosedStepDomain (Z := Z) Q E G)
    (hval : v.val = u.val) : closedStepIntegral Q E G v = closedStepIntegral Q D G u := by
  have hv : v = enlargeClosedDomain Q D E henlarge G u := Subtype.ext hval
  rw [hv]
  exact closedStepIntegral_congr_ae Q D E hprocess henlarge G u

theorem closedIntegral_congr_ae (T : ℝ≥0)
    (u : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    closedIntegral Q E T (enlargeClosedDomain Q D E henlarge (dyadicGrids T) u) t =
      closedIntegral Q D T u t := by
  exact closedStepIntegral_eq_of_congr_ae Q D E hprocess henlarge (dyadicGrids T)
    (closedCutDomain Q D T u 0 t)
    (closedCutDomain Q E T (enlargeClosedDomain Q D E henlarge (dyadicGrids T) u) 0 t) rfl

/-- Merely time-L² adapted diffusion curves have exactly the same computed
noise under valid fixed-time Brownian modifications. -/
theorem predictableCurveIntegral_congr_ae (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hD : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q)
    (hE : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[E.filtration t] (u t i) Q)
    (t : ℝ≥0) :
    predictableCurveIntegral Q E T u hu hE t = predictableCurveIntegral Q D T u hu hD t := by
  exact closedStepIntegral_eq_of_congr_ae Q D E hprocess henlarge (dyadicGrids T)
    (closedCutDomain Q D T (predictableDomain Q D T _ (curveHorizon_pastAdapted Q D T u hu hD)) 0 t)
    (closedCutDomain Q E T (predictableDomain Q E T _ (curveHorizon_pastAdapted Q E T u hu hE)) 0 t) rfl

end PBGSO.FilteredBrownian
