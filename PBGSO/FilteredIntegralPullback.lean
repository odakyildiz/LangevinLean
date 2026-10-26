import PBGSO.FilteredWeightedCompletion
import PBGSO.FilteredBrownianPullback
import PBGSO.LpPullback

/-! # Constructed Brownian integration commutes with actual probability-space pullback
Predictable coefficients, finite stochastic sums and completed integrals all
transport through a measure-preserving source map. No integral-commutation,
noise-isometry, or output-law identity is a premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian

section TimeMap
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A deterministic bounded linear map acts on actual time columns. -/
theorem time_column_map (T : E →L[ℝ] F) (a b : ℝ) (x : E) :
    T.compLpL 2 (volume : Measure ℝ) (TimeGridEnergy.column a b x) =
      TimeGridEnergy.column a b (T x) := by
  apply Lp.ext
  filter_upwards [T.coeFn_compLpL (TimeGridEnergy.column a b x),
    indicatorConstLp_coeFn (μ := (volume : Measure ℝ)) (p := 2)
      (hs := measurableSet_Ioc) (hμs := by simp) (c := x) (s := Ioc a b),
    indicatorConstLp_coeFn (μ := (volume : Measure ℝ)) (p := 2)
      (hs := measurableSet_Ioc) (hμs := by simp) (c := T x) (s := Ioc a b)] with r hT hx hTx
  change (TimeGridEnergy.column a b x) r = _ at hx
  change (TimeGridEnergy.column a b (T x)) r = _ at hTx
  rw [hT, hx, hTx]
  by_cases hr : r ∈ Ioc a b
  · simp only [Set.indicator_of_mem hr]
  · simp only [Set.indicator_of_notMem hr, map_zero]

/-- Bounded linear maps act on literal finite time grids. -/
theorem time_grid_map (T : E →L[ℝ] F) (τ : ℕ → ℝ≥0) (A : ℕ → E) (n : ℕ) :
    T.compLpL 2 (volume : Measure ℝ) (TimeGridEnergy.grid τ A n) =
      TimeGridEnergy.grid τ (fun k => T (A k)) n := by
  simp only [TimeGridEnergy.grid, map_sum, time_column_map]

end TimeMap

variable {Ω Ω' I Z : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R)

/-- The actual pullback of all diffusion columns as a bounded linear map. -/
def columnPullbackCLM : ColumnHilbert (I := I) (Z := Z) R →L[ℝ]
    ColumnHilbert (I := I) (Z := Z) Q where
  toFun U := WithLp.toLp 2 (fun i => lpPullbackCLM hf (U i))
  map_add' U V := by
    apply PiLp.ext
    intro i
    change lpPullbackCLM hf (U i + V i) = _
    exact map_add (lpPullbackCLM hf) _ _
  map_smul' c U := by
    apply PiLp.ext
    intro i
    change lpPullbackCLM hf (c • U i) = _
    exact map_smul (lpPullbackCLM hf) c (U i)
  cont := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => Lp Z 2 Q)).symm.continuous.comp
    (continuous_pi fun i => (lpPullbackCLM hf).continuous.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : I => Lp Z 2 R) i).continuous)

@[simp] theorem columnPullbackCLM_apply (U : ColumnHilbert (I := I) (Z := Z) R) (i : I) :
    columnPullbackCLM (I := I) hf U i = lpPullbackCLM hf (U i) := rfl

/-- The actual coefficient-time pullback. -/
def timePullbackCLM : Lp (ColumnHilbert (I := I) (Z := Z) R) 2 (volume : Measure ℝ) →L[ℝ]
    Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) :=
  (columnPullbackCLM (I := I) (Z := Z) hf).compLpL 2 (volume : Measure ℝ)

variable (D : Driver (I := I) R)

/-- Actual predictable coefficients on the pulled filtration. -/
def pullbackCoefficient {t : ℝ≥0} (A : Coefficient (Z := Z) R D t) :
    Coefficient (Z := Z) Q (pullbackDriver hf D) t where
  value i := A.value i ∘ f
  adapted i := (A.adapted i).comp_measurable (measurable_iff_comap_le.mpr le_rfl)
  square i := (A.square i).comp_measurePreserving hf

/-- The actual L² column packing agrees with column pullback. -/
theorem pullbackCoefficient_toLp {t : ℝ≥0} (A : Coefficient (Z := Z) R D t) :
    (pullbackCoefficient hf D A).toLp = columnPullbackCLM (I := I) hf A.toLp := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [((pullbackCoefficient hf D A).square i).coeFn_toLp,
    lpPullback_coe hf ((A.square i).toLp (A.value i)),
    hf.quasiMeasurePreserving.ae_eq_comp (A.square i).coeFn_toLp] with ω hQ hP hR
  change (((pullbackCoefficient hf D A).square i).toLp _) ω = _ at hQ
  change (((pullbackCoefficient hf D A).square i).toLp _) ω =
    (lpPullbackCLM hf ((A.square i).toLp (A.value i))) ω
  rw [hQ]
  change A.value i (f ω) = (lpPullbackCLM hf ((A.square i).toLp (A.value i))) ω
  rw [hP]
  exact hR.symm

def pullbackCoefficients (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) R D τ) :
    Coefficients (Z := Z) Q (pullbackDriver hf D) τ := fun k => pullbackCoefficient hf D (A k)

/-- Actual coefficient-step embeddings transport linearly. -/
theorem coefficientStep_pullback (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) R D τ) (n : ℕ) :
    coefficientStep Q (pullbackDriver hf D) τ (pullbackCoefficients hf D τ A) n =
      timePullbackCLM (I := I) hf (coefficientStep R D τ A n) := by
  simp only [coefficientStep, pullbackCoefficients, pullbackCoefficient_toLp,
    timePullbackCLM, time_grid_map]

/-- The same finite stochastic sum on the actual pulled Brownian driver. -/
theorem stochasticStep_pullback (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) R D τ) (n : ℕ) :
    stochasticStep Q (pullbackDriver hf D) τ hτ (pullbackCoefficients hf D τ A) n =
      lpPullbackCLM hf (stochasticStep R D τ hτ A n) := by
  apply Lp.ext
  filter_upwards [(gridSum_memLp Q (pullbackDriver hf D) τ hτ
      (pullbackCoefficients hf D τ A) n).coeFn_toLp,
    lpPullback_coe hf (stochasticStep R D τ hτ A n),
    hf.quasiMeasurePreserving.ae_eq_comp (gridSum_memLp R D τ hτ A n).coeFn_toLp]
    with ω hQ hP hR
  change (stochasticStep Q (pullbackDriver hf D) τ hτ (pullbackCoefficients hf D τ A) n) ω = _ at hQ
  change (stochasticStep R D τ hτ A n) (f ω) = gridSum R D τ A n (f ω) at hR
  rw [hQ, hP, hR]
  rfl

/-- An actual integral-domain pullback; its approximation is proved by continuity. -/
def pullbackDomain (G : GridIntegralCompletion.RefiningGrids)
    (u : IntegralDomain (Z := Z) R D G) :
    IntegralDomain (Z := Z) Q (pullbackDriver hf D) G := by
  refine ⟨timePullbackCLM (I := I) hf u.val, ?_⟩
  obtain ⟨A, hA⟩ := u.property
  refine ⟨fun n => pullbackCoefficients hf D (G.time n) (A n), ?_⟩
  simpa only [coefficientStep_pullback, Function.comp_def] using
    ((timePullbackCLM (I := I) hf).continuous.tendsto u.val).comp hA

/-- The constructed stochastic integral commutes with actual source pullback.
Every coefficient, finite-noise and limiting identity is derived. -/
theorem stochasticIntegral_pullback (G : GridIntegralCompletion.RefiningGrids)
    (u : IntegralDomain (Z := Z) R D G) :
    stochasticIntegral Q (pullbackDriver hf D) G (pullbackDomain hf D G u) =
      lpPullbackCLM hf (stochasticIntegral R D G u) := by
  obtain ⟨A, hA⟩ := u.property
  have hQ : Tendsto (fun n => coefficientStep Q (pullbackDriver hf D) (G.time n)
      (pullbackCoefficients hf D (G.time n) (A n)) (G.count n)) atTop
      (𝓝 (pullbackDomain hf D G u).val) := by
    simpa only [coefficientStep_pullback, pullbackDomain, Function.comp_def] using
      ((timePullbackCLM (I := I) hf).continuous.tendsto u.val).comp hA
  have h1 := stochasticIntegral_tendsto Q (pullbackDriver hf D) G (pullbackDomain hf D G u)
    (fun n => pullbackCoefficients hf D (G.time n) (A n)) hQ
  have h2 := ((lpPullbackCLM hf).continuous.tendsto (stochasticIntegral R D G u)).comp
    (stochasticIntegral_tendsto R D G u A hA)
  have h2' : Tendsto (fun n => stochasticStep Q (pullbackDriver hf D) (G.time n)
      (G.monotone n) (pullbackCoefficients hf D (G.time n) (A n)) (G.count n)) atTop
      (𝓝 (lpPullbackCLM hf (stochasticIntegral R D G u))) := by
    simpa only [stochasticStep_pullback, Function.comp_def] using h2
  exact tendsto_nhds_unique h1 h2'

end PBGSO.FilteredBrownian
