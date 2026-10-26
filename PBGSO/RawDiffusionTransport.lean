import PBGSO.RawDiffusionIntegral
import PBGSO.PredictableIntegralTransport
import PBGSO.FilteredIntegralModification

/-! # Actual raw diffusion integrals commute with changes of sample space
The raw composed fields supply their own L² curves through the proved section
construction. Their agreement with bounded-linear pullbacks is derived from
actual spatial sections. No matching coefficient/output law is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
open PBGSO.ProductLpSections
variable {Ω Ω' I Z : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

/-- Computed stochastic integrals depend only on the actual horizon time-L²
coefficient class, including when raw fields have exceptional non-L² sections. -/
theorem predictableCurveIntegral_eq_of_ae_coefficients
    (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
    (T : ℝ≥0) (u v : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hv : MemLp v 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q)
    (hV : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((v t).ofLp i) Q)
    (he : u =ᵐ[volume.restrict (Ioc 0 (T : ℝ))] v) (t : ℝ≥0) :
    predictableCurveIntegral Q D T u hu hU t = predictableCurveIntegral Q D T v hv hV t := by
  have hH : curveHorizon Q T u hu = curveHorizon Q T v hv := by
    apply Lp.ext
    exact (curveHorizon_coe Q T u hu).trans
      (((ae_eq_restrict_iff_indicator_ae_eq measurableSet_Ioc).mp he).trans
        (curveHorizon_coe Q T v hv).symm)
  have hD : predictableDomain Q D T (curveHorizon Q T u hu) (curveHorizon_pastAdapted Q D T u hu hU) =
      predictableDomain Q D T (curveHorizon Q T v hv) (curveHorizon_pastAdapted Q D T v hv hV) := by
    apply Subtype.ext
    change timeCut Q (curveHorizon Q T u hu) 0 T = timeCut Q (curveHorizon Q T v hv) 0 T
    rw [hH]
  change closedIntegral Q D T _ t = closedIntegral Q D T _ t
  rw [hD]

section CoefficientCongruence
variable (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Product-a.e. equality of original raw fields yields equality of their
actual L² section curves outside one time-null set. -/
theorem rawDiffusionCurve_congr_ae (T : ℝ≥0) (σ τ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hτ : ∀ i, StronglyMeasurable (Function.uncurry (τ i)))
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hτ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖τ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (he : ∀ i, Function.uncurry (σ i) =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod Q]
      Function.uncurry (τ i)) :
    rawDiffusionCurve Q σ =ᵐ[volume.restrict (Ioc 0 (T : ℝ))] rawDiffusionCurve Q τ := by
  have hraw : ∀ᵐ r ∂volume.restrict (Ioc 0 (T : ℝ)), ∀ i, σ i r =ᵐ[Q] τ i r :=
    ae_all_iff.mpr (fun i => Measure.ae_ae_of_ae_prod (he i))
  filter_upwards [columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) Q σ hσ hσ2,
    columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) Q τ hτ hτ2, hraw] with r hs ht he
  apply PiLp.ext
  intro i
  apply Lp.ext
  exact (hs i).trans ((he i).trans (ht i).symm)

/-- Same-driver computed integrals depend only on the actual product-a.e.
raw diffusion field. This includes masks of already localized raw fields. -/
theorem rawDiffusionIntegral_congr_ae_coefficients (D : Driver (I := I) Q)
    (T : ℝ≥0) (σ τ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hτ : ∀ i, StronglyMeasurable (Function.uncurry (τ i)))
    (hσ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hτ2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖τ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (hB : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (τ i t) Q)
    (he : ∀ i, Function.uncurry (σ i) =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod Q]
      Function.uncurry (τ i)) (t : ℝ≥0) :
    rawDiffusionIntegral Q D T σ hσ hσ2 hA t = rawDiffusionIntegral Q D T τ hτ hτ2 hB t := by
  exact predictableCurveIntegral_eq_of_ae_coefficients Q D T
    (rawDiffusionCurve Q σ) (rawDiffusionCurve Q τ)
    (rawDiffusionCurve_square Q T σ hσ hσ2) (rawDiffusionCurve_square Q T τ hτ hτ2)
    (rawDiffusionCurve_adapted Q D σ hA) (rawDiffusionCurve_adapted Q D τ hB)
    (rawDiffusionCurve_congr_ae Q T σ τ hσ hτ hσ2 hτ2 he) t

end CoefficientCongruence

section Pullback
variable {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R) (D : Driver (I := I) R)
include hf

/-- Joint strong measurability of the actual raw coefficient composition. -/
theorem rawPullback_stronglyMeasurable (σ : I → ℝ → Ω' → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i))) (i : I) :
    StronglyMeasurable (fun p : ℝ × Ω => σ i p.1 (f p.2)) :=
  (hσ i).comp_measurable (measurable_fst.prodMk (hf.measurable.comp measurable_snd))

/-- Actual product square integrability is preserved by probability pullback. -/
theorem rawPullback_square (T : ℝ≥0) (σ : I → ℝ → Ω' → Z)
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω' => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod R)) (i : I) :
    Integrable (fun p : ℝ × Ω => ‖σ i p.1 (f p.2)‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) :=
  ((MeasurePreserving.id (volume.restrict (Ioc 0 (T : ℝ)))).prod hf).integrable_comp_of_integrable (h2 i)

/-- Raw adapted fields pull to the actual comap past; no adaptedness of the
resulting L²-valued curve is assumed. -/
theorem rawPullback_adapted (σ : I → ℝ → Ω' → Z)
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) R)
    (t : ℝ≥0) (i : I) :
    AEStronglyMeasurable[(pullbackDriver hf D).filtration t] (fun ω => σ i t (f ω)) Q := by
  refine ⟨(hA t i).mk (σ i t) ∘ f, ?_, ?_⟩
  · exact (hA t i).stronglyMeasurable_mk.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  · exact hf.quasiMeasurePreserving.ae_eq_comp (hA t i).ae_eq_mk

/-- The literal raw-section curve agrees almost everywhere in time with the
actual bounded-linear pullback of the original curve. -/
theorem rawDiffusionCurve_pullback (T : ℝ≥0) (σ : I → ℝ → Ω' → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω' => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod R)) :
    rawDiffusionCurve Q (fun i r ω => σ i r (f ω)) =ᵐ[volume.restrict (Ioc 0 (T : ℝ))]
      (fun r => columnPullbackCLM (I := I) (Z := Z) hf (rawDiffusionCurve R σ r)) := by
  have hR := columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) R σ hσ h2
  have hQ := columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) Q
    (fun i r ω => σ i r (f ω)) (rawPullback_stronglyMeasurable hf σ hσ)
    (rawPullback_square hf T σ h2)
  filter_upwards [hR, hQ] with r hr hq
  apply PiLp.ext
  intro i
  change sectionLp Q (fun r ω => σ i r (f ω)) r = lpPullbackCLM hf (sectionLp R (σ i) r)
  apply Lp.ext
  have hsec : sectionLp R (σ i) r =ᵐ[R] σ i r := hr i
  have hsecQ : sectionLp Q (fun r ω => σ i r (f ω)) r =ᵐ[Q] (fun ω => σ i r (f ω)) := hq i
  filter_upwards [hsecQ, lpPullback_coe hf (sectionLp R (σ i) r),
    hf.quasiMeasurePreserving.ae_eq_comp hsec] with ω hq hp hs
  change sectionLp R (σ i) r (f ω) = σ i r (f ω) at hs
  exact hq.trans (hp.trans hs).symm

/-- Computed raw-field integration preserves its actual marginal process
under pullback and any valid larger common filtration with the same noise. -/
theorem rawDiffusionIntegral_pullback_enlarge (E : Driver (I := I) Q)
    (hp : (pullbackDriver hf D).process = E.process)
    (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
    (T : ℝ≥0) (σ : I → ℝ → Ω' → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω' => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod R))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) R) (t : ℝ≥0) :
    rawDiffusionIntegral Q E T (fun i r ω => σ i r (f ω))
      (rawPullback_stronglyMeasurable hf σ hσ) (rawPullback_square hf T σ h2)
      (fun r i => (rawPullback_adapted hf D σ hA r i).mono (he r)) t =
      lpPullbackCLM hf (rawDiffusionIntegral R D T σ hσ h2 hA t) := by
  unfold rawDiffusionIntegral
  rw [predictableCurveIntegral_eq_of_ae_coefficients Q E T _
    (fun r => columnPullbackCLM (I := I) (Z := Z) hf (rawDiffusionCurve R σ r))
    _ ((columnPullbackCLM (I := I) (Z := Z) hf).comp_memLp'
      (rawDiffusionCurve_square R T σ hσ h2)) _
    (fun r i => (columnPullback_adapted hf D r ((rawDiffusionCurve R σ r).ofLp i)
      (rawDiffusionCurve_adapted R D σ hA r i)).mono (he r))
    (rawDiffusionCurve_pullback hf T σ hσ h2) t]
  exact predictableCurveIntegral_pullback_enlarge hf D E hp he T
    (rawDiffusionCurve R σ) (rawDiffusionCurve_square R T σ hσ h2)
    (rawDiffusionCurve_adapted R D σ hA) t

/-- Exact pullback, before any enlargement of the natural pulled filtration. -/
theorem rawDiffusionIntegral_pullback (T : ℝ≥0) (σ : I → ℝ → Ω' → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω' => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod R))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) R) (t : ℝ≥0) :
    rawDiffusionIntegral Q (pullbackDriver hf D) T (fun i r ω => σ i r (f ω))
      (rawPullback_stronglyMeasurable hf σ hσ) (rawPullback_square hf T σ h2)
      (rawPullback_adapted hf D σ hA) t =
      lpPullbackCLM hf (rawDiffusionIntegral R D T σ hσ h2 hA t) := by
  exact rawDiffusionIntegral_pullback_enlarge hf D (pullbackDriver hf D) rfl
    (fun _ => le_refl _) T σ hσ h2 hA t

end Pullback
section Enlargement
variable (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D E : Driver (I := I) Q)
  (hp : ∀ i t, D.process i t =ᵐ[Q] E.process i t)
  (he : ∀ t, D.filtration t ≤ E.filtration t)
include hp he

/-- Raw-field integration is invariant under actual Brownian modification
and valid filtration enlargement. The raw coefficient curve is unchanged. -/
theorem rawDiffusionIntegral_enlarge (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) (t : ℝ≥0) :
    rawDiffusionIntegral Q E T σ hσ h2 (fun r i => (hA r i).mono (he r)) t =
      rawDiffusionIntegral Q D T σ hσ h2 hA t := by
  exact predictableCurveIntegral_congr_ae Q D E hp he T
    (rawDiffusionCurve Q σ) (rawDiffusionCurve_square Q T σ hσ h2)
    (rawDiffusionCurve_adapted Q D σ hA)
    (rawDiffusionCurve_adapted Q E σ (fun r i => (hA r i).mono (he r))) t

end Enlargement

section PullbackModification
variable {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R) (D : Driver (I := I) R)

/-- Pullback commutation remains valid for an actual Brownian modification
in the common larger filtration, using fixed-time AE input identities only. -/
theorem rawDiffusionIntegral_pullback_enlarge_ae (E : Driver (I := I) Q)
    (hp : ∀ i t, (pullbackDriver hf D).process i t =ᵐ[Q] E.process i t)
    (he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t)
    (T : ℝ≥0) (σ : I → ℝ → Ω' → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω' => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod R))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) R) (t : ℝ≥0) :
    rawDiffusionIntegral Q E T (fun i r ω => σ i r (f ω))
      (rawPullback_stronglyMeasurable hf σ hσ) (rawPullback_square hf T σ h2)
      (fun r i => (rawPullback_adapted hf D σ hA r i).mono (he r)) t =
      lpPullbackCLM hf (rawDiffusionIntegral R D T σ hσ h2 hA t) := by
  rw [rawDiffusionIntegral_enlarge Q (pullbackDriver hf D) E hp he T _ _ _
    (rawPullback_adapted hf D σ hA)]
  exact rawDiffusionIntegral_pullback hf D T σ hσ h2 hA t

end PullbackModification

end PBGSO.FilteredBrownian
