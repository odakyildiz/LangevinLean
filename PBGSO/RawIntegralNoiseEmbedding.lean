import PBGSO.RawDiffusionTransport

/-! # Literal inclusion of Brownian noise coordinates
Injecting a finite set of Brownian coordinates into a larger Driver and
padding its original diffusion columns by zero leaves the actual stochastic
integral unchanged. All coefficient/domain identities are derived from the
finite sums and their actual Hilbert completion.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I J Z : Type*} [mΩ : MeasurableSpace Ω]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

def embedFamily {V : Type*} [AddCommMonoid V] (f : I ↪ J) (u : I → V) (j : J) : V :=
  ∑ i, if f i = j then u i else 0

theorem embedFamily_image {V : Type*} [AddCommMonoid V] (f : I ↪ J) (u : I → V) (i : I) :
    embedFamily f u (f i) = u i := by
  simp [embedFamily, f.injective.eq_iff]

theorem embedFamily_outside {V : Type*} [AddCommMonoid V] (f : I ↪ J) (u : I → V) (j : J)
    (hj : j ∉ range f) : embedFamily f u j = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact ite_eq_right (fun h => hj ⟨i,h⟩)

variable (Q : Measure Ω) [IsProbabilityMeasure Q] (f : I ↪ J)

def columnEmbedCLM : ColumnHilbert (I := I) (Z := Z) Q →L[ℝ]
    ColumnHilbert (I := J) (Z := Z) Q where
  toFun u := WithLp.toLp 2 (embedFamily f u.ofLp)
  map_add' u v := by
    apply PiLp.ext
    intro j
    change (∑ i, if f i = j then u.ofLp i + v.ofLp i else 0) =
      (∑ i, if f i = j then u.ofLp i else 0) + ∑ i, if f i = j then v.ofLp i else 0
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  map_smul' c u := by
    apply PiLp.ext
    intro j
    change (∑ i, if f i = j then c • u.ofLp i else 0) =
      c • ∑ i, if f i = j then u.ofLp i else 0
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  cont := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : J => Lp Z 2 Q)).symm.continuous.comp
    (continuous_pi fun j => continuous_finsetSum _ (fun i _ => by
      by_cases h : f i = j
      · simpa only [ite_eq_left h, Function.comp_def] using ((continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : I => Lp Z 2 Q)))
      · simpa only [ite_eq_right h] using (continuous_const : Continuous (fun _ :
          ColumnHilbert (I := I) (Z := Z) Q => (0 : Lp Z 2 Q)))))

@[simp] theorem columnEmbed_image (u : ColumnHilbert (I := I) (Z := Z) Q) (i : I) :
    (columnEmbedCLM Q f u).ofLp (f i) = u.ofLp i := embedFamily_image f u.ofLp i

theorem columnEmbed_outside (u : ColumnHilbert (I := I) (Z := Z) Q) (j : J) (hj : j ∉ range f) :
    (columnEmbedCLM Q f u).ofLp j = 0 := embedFamily_outside f u.ofLp j hj

def timeEmbedCLM := (columnEmbedCLM (Z := Z) Q f).compLpL 2 (volume : Measure ℝ)

variable (D : Driver (I := I) Q) (E : Driver (I := J) Q)
  (hF : D.filtration = E.filtration)
  (hp : ∀ i t, D.process i t = E.process (f i) t)
include hF hp

def injectCoefficient {t : ℝ≥0} (A : Coefficient (Z := Z) Q D t) : Coefficient (Z := Z) Q E t where
  value j ω := embedFamily f (fun i => A.value i ω) j
  adapted j := by
    rw [← hF]
    by_cases hj : j ∈ range f
    · obtain ⟨i,rfl⟩ := hj
      simpa only [embedFamily_image] using A.adapted i
    · simpa only [embedFamily_outside f _ j hj] using
        (stronglyMeasurable_const : StronglyMeasurable[D.filtration t] (fun _ : Ω => (0 : Z)))
  square j := by
    by_cases hj : j ∈ range f
    · obtain ⟨i,rfl⟩ := hj
      simpa only [embedFamily_image] using A.square i
    · simpa only [embedFamily_outside f _ j hj] using (memLp_const (0 : Z) : MemLp (fun _ : Ω => (0 : Z)) 2 Q)

theorem injectCoefficient_toLp {t : ℝ≥0} (A : Coefficient (Z := Z) Q D t) :
    (injectCoefficient Q f D E hF A).toLp = columnEmbedCLM Q f A.toLp := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  by_cases hj : j ∈ range f
  · obtain ⟨i,rfl⟩ := hj
    rw [columnEmbed_image]
    filter_upwards [((injectCoefficient Q f D E hF A).square (f i)).coeFn_toLp,
      (A.square i).coeFn_toLp] with ω hn ho
    change (((injectCoefficient Q f D E hF A).square (f i)).toLp _) ω =
      ((A.square i).toLp _) ω
    rw [hn,ho]
    exact embedFamily_image f (fun i => A.value i ω) i
  · rw [columnEmbed_outside Q f A.toLp j hj]
    filter_upwards [((injectCoefficient Q f D E hF A).square j).coeFn_toLp,
      Lp.coeFn_zero (E := Z) (p := 2) (μ := Q)] with ω hn hz
    change (((injectCoefficient Q f D E hF A).square j).toLp _) ω = (0 : Lp Z 2 Q) ω
    rw [hn,hz]
    exact embedFamily_outside f (fun i => A.value i ω) j hj

def injectCoefficients (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) :
    Coefficients (Z := Z) Q E τ := fun k => injectCoefficient Q f D E hF (A k)

theorem coefficientStep_embed (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    coefficientStep Q E τ (injectCoefficients Q f D E hF τ A) n =
      timeEmbedCLM Q f (coefficientStep Q D τ A n) := by
  simp only [coefficientStep, injectCoefficients, injectCoefficient_toLp Q f D E hF hp, timeEmbedCLM, time_grid_map]

theorem stochasticStep_embed (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    stochasticStep Q E τ hτ (injectCoefficients Q f D E hF τ A) n =
      stochasticStep Q D τ hτ A n := by
  apply Lp.ext
  filter_upwards [(gridSum_memLp Q E τ hτ (injectCoefficients Q f D E hF τ A) n).coeFn_toLp,
    (gridSum_memLp Q D τ hτ A n).coeFn_toLp] with ω hn ho
  change (stochasticStep Q E τ hτ (injectCoefficients Q f D E hF τ A) n) ω = _ at hn
  change (stochasticStep Q D τ hτ A n) ω = gridSum Q D τ A n ω at ho
  rw [hn,ho]
  unfold gridSum noiseStep PredictableIsometry.stepSum
  apply Finset.sum_congr rfl
  intro k hk
  change (∑ j, (E.process j (τ (k+1)) ω - E.process j (τ k) ω) •
    ∑ i, if f i = j then (A k).value i ω else 0) = _
  simp only [Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← hp i (τ (k+1)), ← hp i (τ k)]
  rfl

def injectFiniteStep (G : RefiningGrids) (A : FiniteStepData (Z := Z) Q D G) :
    FiniteStepData (Z := Z) Q E G :=
  ⟨A.1, injectCoefficients Q f D E hF (G.time A.1) A.2⟩

theorem finiteStepInput_embed (G : RefiningGrids) (A : FiniteStepData (Z := Z) Q D G) :
    finiteStepInput Q E G (injectFiniteStep Q f D E hF G A) =
      timeEmbedCLM Q f (finiteStepInput Q D G A) :=
  coefficientStep_embed Q f D E hF hp (G.time A.1) A.2 (G.count A.1)

theorem finiteStepOutput_embed (G : RefiningGrids) (A : FiniteStepData (Z := Z) Q D G) :
    finiteStepOutput Q E G (injectFiniteStep Q f D E hF G A) = finiteStepOutput Q D G A :=
  stochasticStep_embed Q f D E hF hp (G.time A.1) (G.monotone A.1) A.2 (G.count A.1)

def injectClosedDomain (G : RefiningGrids) (u : ClosedStepDomain (Z := Z) Q D G) :
    ClosedStepDomain (Z := Z) Q E G := by
  refine ⟨timeEmbedCLM Q f u.val, ?_⟩
  obtain ⟨A,hA⟩ := exists_finiteStep_approximation Q D G u
  apply isClosed_closure.mem_of_tendsto (((timeEmbedCLM (Z := Z) Q f).continuous.tendsto u.val).comp hA)
  apply Eventually.of_forall
  intro n
  change timeEmbedCLM Q f (finiteStepInput Q D G (A n)) ∈ _
  rw [← finiteStepInput_embed Q f D E hF hp G (A n)]
  exact subset_closure (Set.mem_range_self _)

theorem closedStepIntegral_embed (G : RefiningGrids) (u : ClosedStepDomain (Z := Z) Q D G) :
    closedStepIntegral Q E G (injectClosedDomain Q f D E hF hp G u) = closedStepIntegral Q D G u := by
  obtain ⟨A,hA⟩ := exists_finiteStep_approximation Q D G u
  have hB : Tendsto (fun n => finiteStepInput Q E G (injectFiniteStep Q f D E hF G (A n)))
      atTop (𝓝 (injectClosedDomain Q f D E hF hp G u).val) := by
    simpa only [finiteStepInput_embed Q f D E hF hp, Function.comp_def, injectClosedDomain] using
      ((timeEmbedCLM (Z := Z) Q f).continuous.tendsto u.val).comp hA
  have h1 := closedStepIntegral_tendsto Q E G (fun n => injectFiniteStep Q f D E hF G (A n))
    (injectClosedDomain Q f D E hF hp G u) hB
  apply tendsto_nhds_unique h1
  simpa only [finiteStepOutput_embed Q f D E hF hp] using closedStepIntegral_tendsto Q D G A u hA

theorem timeCut_embed (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (s t : ℝ) : timeCut Q (timeEmbedCLM Q f u) s t = timeEmbedCLM Q f (timeCut Q u s t) := by
  apply Lp.ext
  filter_upwards [timeCut_coe Q (timeEmbedCLM Q f u) s t,
    (columnEmbedCLM (Z := Z) Q f).coeFn_compLpL u,
    (columnEmbedCLM (Z := Z) Q f).coeFn_compLpL (timeCut Q u s t),
    timeCut_coe Q u s t] with r hc hu ht hm
  change (timeEmbedCLM Q f u) r = columnEmbedCLM Q f (u r) at hu
  change (timeEmbedCLM Q f (timeCut Q u s t)) r = _ at ht
  rw [hc,ht,hm]
  by_cases hr : r ∈ Ioc s t
  · simp only [Set.indicator_of_mem hr,hu]
  · simp only [Set.indicator_of_notMem hr,map_zero]

theorem closedIntegral_embed (T : ℝ≥0) (u : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (t : ℝ≥0) :
    closedIntegral Q E T (injectClosedDomain Q f D E hF hp (dyadicGrids T) u) t =
      closedIntegral Q D T u t := by
  have he : closedCutDomain Q E T (injectClosedDomain Q f D E hF hp (dyadicGrids T) u) 0 t =
      injectClosedDomain Q f D E hF hp (dyadicGrids T) (closedCutDomain Q D T u 0 t) := by
    apply Subtype.ext
    exact timeCut_embed Q f D E hF hp u.val 0 t
  rw [closedIntegral,he,closedStepIntegral_embed]
  rfl

theorem columnEmbed_adapted (t : ℝ≥0) (u : ColumnHilbert (I := I) (Z := Z) Q)
    (hu : ∀ i, AEStronglyMeasurable[D.filtration t] (u.ofLp i) Q) (j : J) :
    AEStronglyMeasurable[E.filtration t] ((columnEmbedCLM Q f u).ofLp j) Q := by
  rw [← hF]
  by_cases hj : j ∈ range f
  · obtain ⟨i,rfl⟩ := hj
    rw [columnEmbed_image]
    exact hu i
  · rw [columnEmbed_outside Q f u j hj]
    exact aestronglyMeasurable_zero.congr (Lp.coeFn_zero (E := Z) (p := 2) (μ := Q)).symm

theorem curveHorizon_embed (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (T : ℝ)))) :
    curveHorizon Q T (fun r => columnEmbedCLM Q f (u r)) ((columnEmbedCLM (Z := Z) Q f).comp_memLp' hu) =
      timeEmbedCLM Q f (curveHorizon Q T u hu) := by
  apply Lp.ext
  filter_upwards [curveHorizon_coe Q T (fun r => columnEmbedCLM Q f (u r))
      ((columnEmbedCLM (Z := Z) Q f).comp_memLp' hu), curveHorizon_coe Q T u hu,
    (columnEmbedCLM (Z := Z) Q f).coeFn_compLpL (curveHorizon Q T u hu)] with r hn ho he
  change (timeEmbedCLM Q f (curveHorizon Q T u hu)) r = _ at he
  rw [hn,he,ho]
  by_cases hr : r ∈ Ioc 0 (T : ℝ)
  · simp only [Set.indicator_of_mem hr]
  · simp only [Set.indicator_of_notMem hr,map_zero]

theorem predictableCurveIntegral_embed (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : MemLp u 2 (volume.restrict (Ioc 0 (T : ℝ))))
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] ((u t).ofLp i) Q) (t : ℝ≥0) :
    predictableCurveIntegral Q E T (fun r => columnEmbedCLM Q f (u r))
      ((columnEmbedCLM (Z := Z) Q f).comp_memLp' hu)
      (fun r j => columnEmbed_adapted Q f D E hF hp r (u r) (hU r) j) t =
      predictableCurveIntegral Q D T u hu hU t := by
  let U := predictableDomain Q D T (curveHorizon Q T u hu) (curveHorizon_pastAdapted Q D T u hu hU)
  let V := predictableDomain Q E T
    (curveHorizon Q T (fun r => columnEmbedCLM Q f (u r)) ((columnEmbedCLM (Z := Z) Q f).comp_memLp' hu))
    (curveHorizon_pastAdapted Q E T _ _ (fun r j => columnEmbed_adapted Q f D E hF hp r (u r) (hU r) j))
  have he : V = injectClosedDomain Q f D E hF hp (dyadicGrids T) U := by
    apply Subtype.ext
    change timeCut Q (curveHorizon Q T _ _) 0 T = timeEmbedCLM Q f (timeCut Q (curveHorizon Q T u hu) 0 T)
    rw [curveHorizon_embed Q f D E hF hp, timeCut_embed Q f D E hF hp]
  change closedIntegral Q E T V t = closedIntegral Q D T U t
  rw [he,closedIntegral_embed]

omit hF hp

def rawEmbed (σ : I → ℝ → Ω → Z) (j : J) (r : ℝ) (ω : Ω) : Z :=
  embedFamily f (fun i => σ i r ω) j

@[simp] theorem rawEmbed_image (σ : I → ℝ → Ω → Z) (i : I) :
    rawEmbed f σ (f i) = σ i := by
  funext r ω
  exact embedFamily_image f (fun i => σ i r ω) i

theorem rawEmbed_outside (σ : I → ℝ → Ω → Z) (j : J) (hj : j ∉ range f) :
    rawEmbed f σ j = fun _ _ => 0 := by
  funext r ω
  exact embedFamily_outside f (fun i => σ i r ω) j hj

theorem rawEmbed_stronglyMeasurable (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i))) (j : J) :
    StronglyMeasurable (Function.uncurry (rawEmbed f σ j)) := by
  by_cases hj : j ∈ range f
  · obtain ⟨i,rfl⟩ := hj
    simpa only [rawEmbed_image] using hσ i
  · rw [rawEmbed_outside f σ j hj]
    change StronglyMeasurable (fun _ : ℝ × Ω => (0 : Z))
    exact stronglyMeasurable_const

theorem rawEmbed_square (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) (j : J) :
    Integrable (fun p : ℝ × Ω => ‖rawEmbed f σ j p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  by_cases hj : j ∈ range f
  · obtain ⟨i,rfl⟩ := hj
    simpa only [rawEmbed_image] using h2 i
  · simp only [rawEmbed,embedFamily_outside f _ j hj,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
    exact (integrable_const (0 : ℝ) : Integrable (fun _ : ℝ × Ω => (0 : ℝ))
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))

include hF
theorem rawEmbed_adapted (σ : I → ℝ → Ω → Z)
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (t : ℝ≥0) (j : J) : AEStronglyMeasurable[E.filtration t] (rawEmbed f σ j t) Q := by
  rw [← hF]
  by_cases hj : j ∈ range f
  · obtain ⟨i,rfl⟩ := hj
    simpa only [rawEmbed_image] using hA t i
  · simpa only [rawEmbed_outside f σ j hj] using
      (aestronglyMeasurable_const : AEStronglyMeasurable[D.filtration t] (fun _ : Ω => (0 : Z)) Q)

omit hF
theorem rawDiffusionCurve_embed (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q)) :
    rawDiffusionCurve Q (rawEmbed f σ) =ᵐ[volume.restrict (Ioc 0 (T : ℝ))]
      (fun r => columnEmbedCLM Q f (rawDiffusionCurve Q σ r)) := by
  unfold rawDiffusionCurve
  filter_upwards [ProductLpSections.columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) Q
    (rawEmbed f σ) (rawEmbed_stronglyMeasurable f σ hσ) (rawEmbed_square Q f T σ h2),
    ProductLpSections.columnSections_ae (volume.restrict (Ioc 0 (T : ℝ))) Q σ hσ h2]
      with r hn ho
  apply PiLp.ext
  intro j
  by_cases hj : j ∈ range f
  · obtain ⟨i,rfl⟩ := hj
    rw [columnEmbed_image]
    apply Lp.ext
    have hn' := hn (f i)
    rw [rawEmbed_image] at hn'
    exact hn'.trans (ho i).symm
  · rw [columnEmbed_outside Q f (ProductLpSections.columnSections Q σ r) j hj]
    apply Lp.ext
    filter_upwards [hn j,Lp.coeFn_zero (E := Z) (p := 2) (μ := Q)] with ω hω hz
    rw [hω,hz]
    exact embedFamily_outside f (fun i => σ i r ω) j hj

include hF hp
/-- The actual original Brownian integral is unchanged by a literal
injection of its noise indices into the full common Driver. -/
theorem rawDiffusionIntegral_embed (T : ℝ≥0) (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (h2 : ∀ i, Integrable (fun p : ℝ × Ω => ‖σ i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q) (t : ℝ≥0) :
    rawDiffusionIntegral Q E T (rawEmbed f σ) (rawEmbed_stronglyMeasurable f σ hσ)
      (rawEmbed_square Q f T σ h2) (rawEmbed_adapted Q f D E hF σ hA) t =
      rawDiffusionIntegral Q D T σ hσ h2 hA t := by
  unfold rawDiffusionIntegral
  rw [predictableCurveIntegral_eq_of_ae_coefficients Q E T _
    (fun r => columnEmbedCLM Q f (rawDiffusionCurve Q σ r)) _
    ((columnEmbedCLM (Z := Z) Q f).comp_memLp' (rawDiffusionCurve_square Q T σ hσ h2)) _
    (fun r j => columnEmbed_adapted Q f D E hF hp r (rawDiffusionCurve Q σ r)
      (rawDiffusionCurve_adapted Q D σ hA r) j)
    (rawDiffusionCurve_embed Q f T σ hσ h2) t]
  exact predictableCurveIntegral_embed Q f D E hF hp T _
    (rawDiffusionCurve_square Q T σ hσ h2) (rawDiffusionCurve_adapted Q D σ hA) t

end PBGSO.FilteredBrownian
