import PBGSO.RawDiffusionTransport

/-! # Actual Brownian integrals commute with bounded linear state maps
The finite predictable sums, literal closed domains, and raw spatial sections
are all transported through the given continuous linear map. No stochastic
integral identity is supplied as a hypothesis.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω I Z Y : Type*} [mΩ : MeasurableSpace Ω]
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (L : Z →L[ℝ] Y)

/-- Apply the state map to each actual square-integrable noise column. -/
def columnMapCLM : ColumnHilbert (I := I) (Z := Z) Q →L[ℝ]
    ColumnHilbert (I := I) (Z := Y) Q where
  toFun U := WithLp.toLp 2 (fun i => L.compLpL 2 Q (U i))
  map_add' U V := by
    apply PiLp.ext
    intro i
    exact map_add (L.compLpL 2 Q) (U i) (V i)
  map_smul' c U := by
    apply PiLp.ext
    intro i
    exact map_smul (L.compLpL 2 Q) c (U i)
  cont := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => Lp Y 2 Q)).symm.continuous.comp
    (continuous_pi fun i => (L.compLpL 2 Q).continuous.comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : I => Lp Z 2 Q) i).continuous)

@[simp] theorem columnMapCLM_apply (U : ColumnHilbert (I := I) (Z := Z) Q) (i : I) :
    columnMapCLM Q L U i = L.compLpL 2 Q (U i) := rfl

def timeMapCLM := (columnMapCLM (I := I) Q L).compLpL 2 (volume : Measure ℝ)

variable (D : Driver (I := I) Q)

def mapCoefficient {t : ℝ≥0} (A : Coefficient (Z := Z) Q D t) :
    Coefficient (Z := Y) Q D t where
  value i ω := L (A.value i ω)
  adapted i := L.continuous.comp_stronglyMeasurable (A.adapted i)
  square i := L.comp_memLp' (A.square i)

theorem mapCoefficient_toLp {t : ℝ≥0} (A : Coefficient (Z := Z) Q D t) :
    (mapCoefficient Q L D A).toLp = columnMapCLM Q L A.toLp := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [((mapCoefficient Q L D A).square i).coeFn_toLp,
    L.coeFn_compLpL ((A.square i).toLp (A.value i)),
    (A.square i).coeFn_toLp] with ω hnew hL hold
  change (((mapCoefficient Q L D A).square i).toLp _) ω = _ at hnew
  change (((mapCoefficient Q L D A).square i).toLp _) ω =
    (L.compLpL 2 Q ((A.square i).toLp (A.value i))) ω
  rw [hnew, hL, hold]
  rfl

def mapCoefficients (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) :
    Coefficients (Z := Y) Q D τ := fun k => mapCoefficient Q L D (A k)

theorem coefficientStep_map (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    coefficientStep Q D τ (mapCoefficients Q L D τ A) n =
      timeMapCLM Q L (coefficientStep Q D τ A n) := by
  simp only [coefficientStep, mapCoefficients, mapCoefficient_toLp, timeMapCLM, time_grid_map]

theorem stochasticStep_map (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    stochasticStep Q D τ hτ (mapCoefficients Q L D τ A) n =
      L.compLpL 2 Q (stochasticStep Q D τ hτ A n) := by
  apply Lp.ext
  filter_upwards [(gridSum_memLp Q D τ hτ (mapCoefficients Q L D τ A) n).coeFn_toLp,
    L.coeFn_compLpL (stochasticStep Q D τ hτ A n),
    (gridSum_memLp Q D τ hτ A n).coeFn_toLp] with ω hnew hL hold
  change (stochasticStep Q D τ hτ (mapCoefficients Q L D τ A) n) ω = _ at hnew
  change (stochasticStep Q D τ hτ A n) ω = gridSum Q D τ A n ω at hold
  rw [hnew, hL, hold]
  simp only [gridSum, noiseStep, PredictableIsometry.stepSum, map_sum, map_smul,
    mapCoefficients, mapCoefficient]

def mapFiniteStep (G : RefiningGrids) (A : FiniteStepData (Z := Z) Q D G) :
    FiniteStepData (Z := Y) Q D G :=
  ⟨A.1, mapCoefficients Q L D (G.time A.1) A.2⟩

@[simp] theorem finiteStepInput_map (G : RefiningGrids) (A : FiniteStepData (Z := Z) Q D G) :
    finiteStepInput Q D G (mapFiniteStep Q L D G A) = timeMapCLM Q L (finiteStepInput Q D G A) :=
  coefficientStep_map Q L D (G.time A.1) A.2 (G.count A.1)

@[simp] theorem finiteStepOutput_map (G : RefiningGrids) (A : FiniteStepData (Z := Z) Q D G) :
    finiteStepOutput Q D G (mapFiniteStep Q L D G A) = L.compLpL 2 Q (finiteStepOutput Q D G A) :=
  stochasticStep_map Q L D (G.time A.1) (G.monotone A.1) A.2 (G.count A.1)

/-- Literal closure membership is preserved by the state map. -/
def mapClosedDomain (G : RefiningGrids) (u : ClosedStepDomain (Z := Z) Q D G) :
    ClosedStepDomain (Z := Y) Q D G := by
  refine ⟨timeMapCLM Q L u.val, ?_⟩
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G u
  have hlim := ((timeMapCLM (I := I) Q L).continuous.tendsto u.val).comp hA
  apply isClosed_closure.mem_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  change timeMapCLM Q L (finiteStepInput Q D G (A n)) ∈ _
  rw [← finiteStepInput_map Q L D G (A n)]
  exact subset_closure (Set.mem_range_self _)

theorem closedStepIntegral_map (G : RefiningGrids) (u : ClosedStepDomain (Z := Z) Q D G) :
    closedStepIntegral Q D G (mapClosedDomain Q L D G u) =
      L.compLpL 2 Q (closedStepIntegral Q D G u) := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G u
  have hB : Tendsto (fun n => finiteStepInput Q D G (mapFiniteStep Q L D G (A n)))
      atTop (𝓝 (mapClosedDomain Q L D G u).val) := by
    simpa only [finiteStepInput_map, Function.comp_def, mapClosedDomain] using
      ((timeMapCLM (I := I) Q L).continuous.tendsto u.val).comp hA
  have h1 := closedStepIntegral_tendsto Q D G (fun n => mapFiniteStep Q L D G (A n))
    (mapClosedDomain Q L D G u) hB
  have h2 := ((L.compLpL 2 Q).continuous.tendsto (closedStepIntegral Q D G u)).comp
    (closedStepIntegral_tendsto Q D G A u hA)
  apply tendsto_nhds_unique h1
  simpa only [finiteStepOutput_map, Function.comp_def] using h2

theorem timeCut_map (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (s t : ℝ) :
    timeCut Q (timeMapCLM Q L U) s t = timeMapCLM Q L (timeCut Q U s t) := by
  apply Lp.ext
  filter_upwards [timeCut_coe Q (timeMapCLM Q L U) s t,
    (columnMapCLM (I := I) Q L).coeFn_compLpL U,
    (columnMapCLM (I := I) Q L).coeFn_compLpL (timeCut Q U s t),
    timeCut_coe Q U s t] with r hcut hU hT hmask
  change (timeMapCLM Q L U) r = columnMapCLM Q L (U r) at hU
  change (timeMapCLM Q L (timeCut Q U s t)) r = _ at hT
  rw [hcut, hT, hmask]
  by_cases hr : r ∈ Ioc s t
  · simp only [Set.indicator_of_mem hr, hU]
  · simp only [Set.indicator_of_notMem hr, map_zero]

theorem closedIntegral_map (T : ℝ≥0)
    (u : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    closedIntegral Q D T (mapClosedDomain Q L D (dyadicGrids T) u) t =
      L.compLpL 2 Q (closedIntegral Q D T u t) := by
  have he : closedCutDomain Q D T (mapClosedDomain Q L D (dyadicGrids T) u) 0 t =
      mapClosedDomain Q L D (dyadicGrids T) (closedCutDomain Q D T u 0 t) := by
    apply Subtype.ext
    exact timeCut_map Q L u.val 0 t
  rw [closedIntegral, he, closedStepIntegral_map]
  rfl

/-- Actual past measurability is preserved by the state map. -/
theorem columnMap_adapted (t : ℝ≥0) (U : Lp Z 2 Q)
    (hU : AEStronglyMeasurable[D.filtration t] U Q) :
    AEStronglyMeasurable[D.filtration t] (L.compLpL 2 Q U) Q := by
  refine ⟨L ∘ hU.mk U, L.continuous.comp_stronglyMeasurable hU.stronglyMeasurable_mk, ?_⟩
  exact (L.coeFn_compLpL U).trans (hU.ae_eq_mk.fun_comp L)

theorem curveHorizon_map (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (T : ℝ)))) :
    curveHorizon Q T (fun r => columnMapCLM Q L (u r)) ((columnMapCLM (I := I) Q L).comp_memLp' hu) =
      timeMapCLM Q L (curveHorizon Q T u hu) := by
  apply Lp.ext
  filter_upwards [curveHorizon_coe Q T (fun r => columnMapCLM Q L (u r))
      ((columnMapCLM (I := I) Q L).comp_memLp' hu), curveHorizon_coe Q T u hu,
    (columnMapCLM (I := I) Q L).coeFn_compLpL (curveHorizon Q T u hu)] with r hnew hold hL
  change (timeMapCLM Q L (curveHorizon Q T u hu)) r = _ at hL
  rw [hnew, hL, hold]
  by_cases hr : r ∈ Ioc 0 (T : ℝ)
  · simp only [Set.indicator_of_mem hr]
  · simp only [Set.indicator_of_notMem hr, map_zero]

theorem predictableCurveIntegral_map (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q)
    (t : ℝ≥0) :
    predictableCurveIntegral Q D T (fun r => columnMapCLM Q L (u r))
      ((columnMapCLM (I := I) Q L).comp_memLp' hu)
      (fun r i => columnMap_adapted Q L D r ((u r).ofLp i) (hU r i)) t =
      L.compLpL 2 Q (predictableCurveIntegral Q D T u hu hU t) := by
  let UZ := predictableDomain Q D T (curveHorizon Q T u hu) (curveHorizon_pastAdapted Q D T u hu hU)
  let UY := predictableDomain Q D T
    (curveHorizon Q T (fun r => columnMapCLM Q L (u r)) ((columnMapCLM (I := I) Q L).comp_memLp' hu))
    (curveHorizon_pastAdapted Q D T _ _ (fun r i => columnMap_adapted Q L D r ((u r).ofLp i) (hU r i)))
  have he : UY = mapClosedDomain Q L D (dyadicGrids T) UZ := by
    apply Subtype.ext
    change timeCut Q (curveHorizon Q T _ _) 0 T = timeMapCLM Q L (timeCut Q (curveHorizon Q T u hu) 0 T)
    rw [curveHorizon_map, timeCut_map]
  change closedIntegral Q D T UY t = L.compLpL 2 Q (closedIntegral Q D T UZ t)
  rw [he, closedIntegral_map]

section Raw
open PBGSO.ProductLpSections

/-- The transformed raw diffusion remains jointly strongly measurable. -/
theorem rawMap_stronglyMeasurable (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i))) (i : I) :
    StronglyMeasurable (fun p : ℝ × Ω => L (σ i p.1 p.2)) :=
  L.continuous.comp_stronglyMeasurable (hσ i)

/-- Its expected integrated square is derived from boundedness of the map. -/
theorem rawMap_square (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) (i : I) :
    Integrable (fun p : ℝ × Ω => ‖L (σ i p.1 p.2)‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have hs := (memLp_two_iff_integrable_sq_norm (hσ i).aestronglyMeasurable).mpr (h2 i)
  exact (L.comp_memLp' hs).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

/-- Raw adaptation is inherited directly from the original coefficient. -/
theorem rawMap_adapted (σ : I → ℝ → Ω → Z)
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (t : ℝ≥0) (i : I) :
    AEStronglyMeasurable[D.filtration t] (fun ω => L (σ i t ω)) Q := by
  refine ⟨L ∘ (hA t i).mk (σ i t),
    L.continuous.comp_stronglyMeasurable (hA t i).stronglyMeasurable_mk, ?_⟩
  exact (hA t i).ae_eq_mk.fun_comp L

/-- Actual raw spatial sections commute with the state map outside one
horizon time-null set. Exceptional non-L² sections create no extra premise. -/
theorem rawDiffusionCurve_map (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    rawDiffusionCurve Q (fun i r ω => L (σ i r ω)) =ᵐ[volume.restrict (Ioc 0 (T : ℝ))]
      (fun r => columnMapCLM Q L (rawDiffusionCurve Q σ r)) := by
  have hZ := columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) Q σ hσ h2
  have hY := columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) Q
    (fun i r ω => L (σ i r ω)) (rawMap_stronglyMeasurable L σ hσ)
    (rawMap_square Q L T σ hσ h2)
  filter_upwards [hZ, hY] with r hz hy
  apply PiLp.ext
  intro i
  change sectionLp Q (fun r ω => L (σ i r ω)) r = L.compLpL 2 Q (sectionLp Q (σ i) r)
  apply Lp.ext
  filter_upwards [hy i, L.coeFn_compLpL (sectionLp Q (σ i) r), hz i] with ω hnew hL hold
  exact hnew.trans (hL.trans (congrArg L hold)).symm

/-- The actual computed raw stochastic integral commutes with every bounded
linear state map. All finite-step, closure, section, and noise identities are
proved; no matching stochastic-output hypothesis is required. -/
theorem rawDiffusionIntegral_map (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (t : ℝ≥0) :
    rawDiffusionIntegral Q D T (fun i r ω => L (σ i r ω))
      (rawMap_stronglyMeasurable L σ hσ) (rawMap_square Q L T σ hσ h2)
      (rawMap_adapted Q L D σ hA) t =
      L.compLpL 2 Q (rawDiffusionIntegral Q D T σ hσ h2 hA t) := by
  unfold rawDiffusionIntegral
  rw [predictableCurveIntegral_eq_of_ae_coefficients Q D T _
    (fun r => columnMapCLM Q L (rawDiffusionCurve Q σ r)) _
    ((columnMapCLM (I := I) Q L).comp_memLp' (rawDiffusionCurve_square Q T σ hσ h2)) _
    (fun r i => columnMap_adapted Q L D r ((rawDiffusionCurve Q σ r).ofLp i)
      (rawDiffusionCurve_adapted Q D σ hA r i)) (rawDiffusionCurve_map Q L T σ hσ h2) t]
  exact predictableCurveIntegral_map Q L D T (rawDiffusionCurve Q σ)
    (rawDiffusionCurve_square Q T σ hσ h2) (rawDiffusionCurve_adapted Q D σ hA) t
end Raw
end PBGSO.FilteredBrownian
