import PBGSO.RawDiffusionTransport
import PBGSO.ConstructedStoppedIntegral
import PBGSO.LocalizedDiffusion

/-! # Actual stopping commutes with raw-field stochastic integration -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- The actual closed coefficient-domain entry for the literal raw field. -/
def rawDiffusionDomain (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) :
    ClosedStepDomain (Z := Z) Q D (dyadicGrids T) :=
  predictableDomain Q D T
    (curveHorizon Q T (rawDiffusionCurve Q σ) (rawDiffusionCurve_square Q T σ hσ h2))
    (curveHorizon_pastAdapted Q D T _ _ (rawDiffusionCurve_adapted Q D σ hA))

theorem rawDiffusionDomain_coe (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) :
    ∀ᵐ r ∂volume, ∀ i,
      ((rawDiffusionDomain Q D T σ hσ h2 hA).val r).ofLp i =ᵐ[Q]
        fun ω => (Ioc 0 (T : ℝ)).indicator (fun r => σ i r ω) r := by
  have hc := ProductLpSections.columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) Q σ hσ h2
  have hc' : ∀ᵐ r ∂volume, r ∈ Ioc 0 (T : ℝ) → ∀ i,
      (rawDiffusionCurve Q σ r).ofLp i =ᵐ[Q] σ i r :=
    (ae_restrict_iff' measurableSet_Ioc).mp hc
  have hH := curveHorizon_coe Q T (rawDiffusionCurve Q σ) (rawDiffusionCurve_square Q T σ hσ h2)
  have hcut := timeCut_coe Q
    (curveHorizon Q T (rawDiffusionCurve Q σ) (rawDiffusionCurve_square Q T σ hσ h2)) 0 T
  filter_upwards [hc',hH,hcut] with r hr hh ht
  intro i
  change ((timeCut Q _ 0 T) r).ofLp i =ᵐ[Q] _
  rw [ht]
  by_cases hrt : r ∈ Ioc 0 (T : ℝ)
  · rw [Set.indicator_of_mem hrt, hh, Set.indicator_of_mem hrt]
    simpa only [Set.indicator_of_mem hrt] using hr hrt i
  · rw [Set.indicator_of_notMem hrt]
    change (0 : Lp Z 2 Q) =ᵐ[Q] _
    filter_upwards [Lp.coeFn_zero (E := Z) (p := 2) (μ := Q)] with ω hz
    change (0 : Lp Z 2 Q) ω = (0 : Z) at hz
    simpa only [Set.indicator_of_notMem hrt] using hz

/-- The actual completed domain of the stopped raw field equals the
completed random-time mask of its original domain. -/
theorem rawDiffusionDomain_stopped_eq (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hs : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (v : I → ℝ → Ω → Z)
    (hv : ∀ i, StronglyMeasurable (Function.uncurry (v i)))
    (hv2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖v i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hvA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (v i t) Q)
    (he : ∀ i r ω, v i r ω = LocalizedDiffusion.stoppedField τ (σ i) r ω) :
    rawDiffusionDomain Q D T v hv hv2 hvA =
      boundedStoppedDomain Q D T τ hτ hs (rawDiffusionDomain Q D T σ hσ h2 hA) := by
  apply Subtype.ext
  apply Lp.ext
  have hcσ := rawDiffusionDomain_coe Q D T σ hσ h2 hA
  have hcv := rawDiffusionDomain_coe Q D T v hv hv2 hvA
  have hcm := randomStoppedInput_coe Q D T τ hτ hs (rawDiffusionDomain Q D T σ hσ h2 hA).val
  filter_upwards [hcσ,hcv,hcm] with r hσr hvr hmr
  change (rawDiffusionDomain Q D T v hv hv2 hvA).val r =
    randomStoppedInput Q D T τ hτ hs (rawDiffusionDomain Q D T σ hσ h2 hA).val r
  rw [hmr]
  apply PiLp.ext
  intro i
  apply Lp.ext
  by_cases hrt : r ∈ Ioc 0 (T : ℝ)
  · have hmE : MeasurableSet {ω | r ≤ (τ ω : ℝ)} := measurableSet_le measurable_const
      (measurable_coe_nnreal_real.comp (stoppingTime_measurable Q D τ hs))
    have hmask := eventMask_coe Q {ω | r ≤ (τ ω : ℝ)} hmE
      (((rawDiffusionDomain Q D T σ hσ h2 hA).val r).ofLp i)
    filter_upwards [hσr i,hvr i,hmask] with ω hσω hvω hmω
    change (((rawDiffusionDomain Q D T v hv hv2 hvA).val r).ofLp i) ω = _
    simp only [randomStopCurve, ite_eq_left hrt, columnEventMask_apply]
    rw [hmω,hvω]
    by_cases hτω : r ≤ (τ ω : ℝ) <;>
      simp [Set.indicator, hrt, hτω, he, LocalizedDiffusion.stoppedField, hσω]
  · filter_upwards [hvr i, Lp.coeFn_zero (E := Z) (p := 2) (μ := Q)] with ω hvω hz
    simp only [randomStopCurve, ite_eq_right hrt]
    change (((rawDiffusionDomain Q D T v hv hv2 hvA).val r).ofLp i) ω = (0 : Lp Z 2 Q) ω
    rw [hz]
    simpa only [Set.indicator_of_notMem hrt, Pi.zero_apply] using hvω

/-- Actual continuous modifications of the two computed raw integrals
satisfy literal stopping simultaneously at every time. -/
theorem rawDiffusionIntegral_stopped_version (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hs : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (σ v : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (hv : ∀ i, StronglyMeasurable (Function.uncurry (v i)))
    (hv2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖v i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hvA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (v i t) Q)
    (he : ∀ i r ω, v i r ω = LocalizedDiffusion.stoppedField τ (σ i) r ω)
    (M N : ℝ≥0 → Ω → Z)
    (hM : ∀ t, M t =ᵐ[Q] rawDiffusionIntegral Q D T σ hσ h2 hA t)
    (hN : ∀ t, N t =ᵐ[Q] rawDiffusionIntegral Q D T v hv hv2 hvA t)
    (hMC : ∀ᵐ ω ∂Q, Continuous (fun t => M t ω))
    (hNC : ∀ᵐ ω ∂Q, Continuous (fun t => N t ω)) :
    ∀ᵐ ω ∂Q, ∀ t, N t ω = M (min t (τ ω)) ω := by
  apply continuous_versions_indistinguishable Q N (fun t ω => M (min t (τ ω)) ω) hNC
  · exact hMC.mono (fun ω hc => hc.comp (continuous_id.min continuous_const))
  · intro t
    apply (hN t).trans
    have hd := rawDiffusionDomain_stopped_eq Q D T τ hτ hs σ hσ h2 hA v hv hv2 hvA he
    change closedIntegral Q D T (rawDiffusionDomain Q D T v hv hv2 hvA) t =ᵐ[Q] _
    rw [hd]
    exact boundedStoppedIntegral_realizes_of_continuous Q D T τ hτ hs
      (rawDiffusionDomain Q D T σ hσ h2 hA) M hM hMC t

end PBGSO.FilteredBrownian
