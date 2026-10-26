import PBGSO.StoppingLpLimit
import PBGSO.ClosedIntegralContinuousVersion
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.DenseEmbedding

/-! # Actual bounded stopping of constructed Brownian integrals -/
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
  {Q : Measure Ω} [IsProbabilityMeasure Q] {D : Driver (I := I) Q}

/-- Finite random-time selection preserves every actual modification of
the computed integral, by a genuine finite union of null sets. -/
theorem GridStoppingIndex.stoppedIntegral_coe_version (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (M : ℝ≥0 → Ω → Z) (hM : ∀ s, M s =ᵐ[Q] closedIntegral Q D T U s) (t : ℝ≥0) :
    σ.stoppedIntegral T m U t =ᵐ[Q] fun ω => M
      (min t ((dyadicGrids T).time m (σ.index ω))) ω := by
  filter_upwards [σ.select_coe (fun j => closedIntegral Q D T U
      (min t ((dyadicGrids T).time m j))),
    ae_all_iff.mpr (fun j : Fin ((dyadicGrids T).count m + 1) =>
      hM (min t ((dyadicGrids T).time m j)))] with ω hselect hj
  exact hselect.trans (hj (σ.finIndex ω)).symm

variable (Q D)

/-- Bounded stopping identity for the actual completed integral. The input
mask converges in L²; simultaneous path continuity identifies its limit with
literal evaluation at the random stopping time. No UI/energy premise is used. -/
theorem boundedStoppedIntegral_realizes_of_continuous (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (M : ℝ≥0 → Ω → Z) (hM : ∀ s, M s =ᵐ[Q] closedIntegral Q D T U s)
    (hcont : ∀ᵐ ω ∂Q, Continuous (fun t => M t ω)) (t : ℝ≥0) :
    closedIntegral Q D T (boundedStoppedDomain Q D T τ hτ hstop U) t =ᵐ[Q]
      fun ω => M (min t (τ ω)) ω := by
  let σ m := dyadicStoppingIndex Q D T τ hτ hstop m
  have hl := dyadicStoppedIntegral_tendsto Q D T τ hτ hstop U t
  obtain ⟨φ, hφ, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hl).exists_seq_tendsto_ae
  have hfinite (m : ℕ) : (σ m).stoppedIntegral T m U t =ᵐ[Q]
      fun ω => M (min t (dyadicStop T τ hτ m ω)) ω :=
    (σ m).stoppedIntegral_coe_version T m U M hM t
  filter_upwards [hAE, hcont, ae_all_iff.mpr hfinite] with ω hω hc hf
  have ht : Tendsto (fun m => min t (dyadicStop T τ hτ m ω)) atTop (𝓝 (min t (τ ω))) :=
    tendsto_const_nhds.min (dyadicStop_tendsto T τ hτ ω)
  have hm := (hc.continuousAt.tendsto.comp ht).comp hφ.tendsto_atTop
  have hm' : Tendsto (fun n => (σ (φ n)).stoppedIntegral T (φ n) U t ω)
      atTop (𝓝 (M (min t (τ ω)) ω)) :=
    hm.congr' (Eventually.of_forall (fun n => (hf (φ n)).symm))
  exact tendsto_nhds_unique hω hm'

/-- Continuous modifications agreeing at each fixed time agree at every
time on one common probability-one event. -/
theorem continuous_versions_indistinguishable (M N : ℝ≥0 → Ω → Z)
    (hM : ∀ᵐ ω ∂Q, Continuous (fun t => M t ω))
    (hN : ∀ᵐ ω ∂Q, Continuous (fun t => N t ω))
    (hMN : ∀ t, M t =ᵐ[Q] N t) : ∀ᵐ ω ∂Q, ∀ t, M t ω = N t ω := by
  filter_upwards [hM, hN, ae_all_iff.mpr (fun n => hMN (TopologicalSpace.denseSeq ℝ≥0 n))] with ω hm hn he
  have hEq := (TopologicalSpace.denseRange_denseSeq ℝ≥0).equalizer hm hn (funext he)
  exact congrFun hEq

/-- For every actual bounded stopping time, the original constructed
Brownian integral has a simultaneous continuous martingale version whose
stopped path is itself an actual continuous martingale. Every stochastic
realization and equality is derived from the actual Brownian completion. -/
theorem exists_bounded_stopped_martingale (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (hB : ∀ᵐ ω ∂Q, ∀ i, Continuous (fun t => D.process i t ω)) :
    ∃ M N : ℝ≥0 → Ω → Z, Martingale M D.filtration Q ∧ Martingale N D.filtration Q ∧
      (∀ᵐ ω ∂Q, Continuous (fun t => M t ω)) ∧
      (∀ᵐ ω ∂Q, Continuous (fun t => N t ω)) ∧
      (∀ t, M t =ᵐ[Q] closedIntegral Q D T U t) ∧
      (∀ t, N t =ᵐ[Q] closedIntegral Q D T (boundedStoppedDomain Q D T τ hτ hstop U) t) ∧
      (∀ᵐ ω ∂Q, ∀ t, N t ω = M (min t (τ ω)) ω) := by
  obtain ⟨M, hMM, hMC, hM⟩ := exists_continuous_martingale_version Q D T U hB
  obtain ⟨N, hNM, hNC, hN⟩ := exists_continuous_martingale_version Q D T
    (boundedStoppedDomain Q D T τ hτ hstop U) hB
  refine ⟨M, N, hMM, hNM, hMC, hNC, hM, hN, ?_⟩
  apply continuous_versions_indistinguishable Q N (fun t ω => M (min t (τ ω)) ω) hNC
  · exact hMC.mono (fun ω hc => hc.comp (continuous_id.min continuous_const))
  · intro t
    exact (hN t).trans (boundedStoppedIntegral_realizes_of_continuous Q D T τ hτ hstop U M hM hMC t)

/-- Exact bounded-stopping weighted isometry, with the original columns
restricted by the literal actual stopping indicator. -/
theorem boundedStoppedIntegral_isometry (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ) (t : ℝ≥0) :
    QuadraticMartingale.weightedPairing Q W
      (closedIntegral Q D T (boundedStoppedDomain Q D T τ hτ hstop U) t)
      (closedIntegral Q D T (boundedStoppedDomain Q D T τ hτ hstop U) t) =
      ∫ r in Ioc (0 : ℝ) t, ∑ i, QuadraticMartingale.weightedPairing Q W
        ((randomStopCurve Q T τ (stoppingTime_measurable Q D τ hstop) U.val r).ofLp i)
        ((randomStopCurve Q T τ (stoppingTime_measurable Q D τ hstop) U.val r).ofLp i) := by
  have he := closedIntegral_increment_isometry Q D T (boundedStoppedDomain Q D T τ hτ hstop U) W hW 0 t (by simp)
  rw [closedIntegral_zero, sub_zero] at he
  rw [he]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (randomStoppedInput_coe Q D T τ hτ hstop U.val)] with r hr
  change (∑ i, QuadraticMartingale.weightedPairing Q W
    ((randomStoppedInput Q D T τ hτ hstop U.val r).ofLp i)
    ((randomStoppedInput Q D T τ hτ hstop U.val r).ofLp i)) = _
  rw [hr]

/-- The event-mask operator's energy is the actual restricted expectation. -/
theorem eventMask_weighted (E : Set Ω) (hE : MeasurableSet E)
    (V : Lp Z 2 Q) (W : Z →L[ℝ] Z) :
    QuadraticMartingale.weightedPairing Q W (eventMask Q E hE V) (eventMask Q E hE V) =
      ∫ ω in E, ⟪V ω, W (V ω)⟫_ℝ ∂Q := by
  rw [QuadraticMartingale.weightedPairing_apply, lp_weighted_pairing_eq_integral,
    ← integral_indicator hE]
  apply integral_congr_ae
  filter_upwards [eventMask_coe Q E hE V] with ω hω
  rw [hω]
  by_cases he : ω ∈ E <;> simp [Set.indicator, he]

/-- The stopped isometry in original physical-column coordinates: the
right side is the exact original diffusion energy up to the actual stop. -/
theorem boundedStoppedIntegral_isometry_explicit (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (t : ℝ≥0) (ht : t ≤ T) :
    QuadraticMartingale.weightedPairing Q W
      (closedIntegral Q D T (boundedStoppedDomain Q D T τ hτ hstop U) t)
      (closedIntegral Q D T (boundedStoppedDomain Q D T τ hτ hstop U) t) =
      ∫ r in Ioc (0 : ℝ) t, ∑ i,
        ∫ ω in {ω | r ≤ (τ ω : ℝ)}, ⟪(U.val r).ofLp i ω, W ((U.val r).ofLp i ω)⟫_ℝ ∂Q := by
  rw [boundedStoppedIntegral_isometry Q D T τ hτ hstop U W hW t]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hR : r ∈ Ioc 0 (T : ℝ) := ⟨hr.1, hr.2.trans (by exact_mod_cast ht)⟩
  simp only [randomStopCurve, ite_eq_left hR, columnEventMask_apply]
  exact Finset.sum_congr rfl (fun i _ => eventMask_weighted Q _ _ _ W)

/-- Exact stopped weighted moments of the actual continuous noise path,
with no moment/isometry premise and no abstract stopped-process replacement. -/
theorem boundedStopped_path_isometry (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (M : ℝ≥0 → Ω → Z) (hM : ∀ s, M s =ᵐ[Q] closedIntegral Q D T U s)
    (hcont : ∀ᵐ ω ∂Q, Continuous (fun t => M t ω))
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, ⟪M (min t (τ ω)) ω, W (M (min t (τ ω)) ω)⟫_ℝ ∂Q) =
      ∫ r in Ioc (0 : ℝ) t, ∑ i,
        ∫ ω in {ω | r ≤ (τ ω : ℝ)}, ⟪(U.val r).ofLp i ω, W ((U.val r).ofLp i ω)⟫_ℝ ∂Q := by
  rw [← boundedStoppedIntegral_isometry_explicit Q D T τ hτ hstop U W hW t ht,
    QuadraticMartingale.weightedPairing_apply, lp_weighted_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [boundedStoppedIntegral_realizes_of_continuous Q D T τ hτ hstop U M hM hcont t]
    with ω hω
  rw [hω]

end PBGSO.FilteredBrownian
