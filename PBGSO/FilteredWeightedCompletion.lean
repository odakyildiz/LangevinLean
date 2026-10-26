import PBGSO.FilteredIntegralCompletion
import PBGSO.BrownianWeightedCompletion

/-! # Weighted completion and interval consistency for a Brownian vector -/
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

/-- The literal diagonal action of a state-space weight on every random
diffusion column. -/
def columnWeight (W : Z →L[ℝ] Z) : ColumnHilbert (I := I) (Z := Z) Q →L[ℝ]
    ColumnHilbert (I := I) (Z := Z) Q :=
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => Lp Z 2 Q)
  e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun i : I => (W.compLpL 2 Q).comp (ContinuousLinearMap.proj i))).comp
      e.toContinuousLinearMap)

@[simp] theorem columnWeight_apply (W : Z →L[ℝ] Z) (x : ColumnHilbert (I := I) (Z := Z) Q) (i : I) :
    (columnWeight (I := I) Q W x).ofLp i = W.compLpL 2 Q (x.ofLp i) := rfl

theorem columnWeight_inner (W : Z →L[ℝ] Z) (x y : ColumnHilbert (I := I) (Z := Z) Q) :
    ⟪x, columnWeight (I := I) Q W y⟫_ℝ = ∑ i, weightedPairing Q W (x.ofLp i) (y.ofLp i) := by
  rw [PiLp.inner_apply]
  rfl

theorem stochasticStep_weighted (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    weightedPairing Q W (stochasticStep Q D τ hτ A n) (stochasticStep Q D τ hτ A n) =
    ⟪coefficientStep Q D τ A n,
      (columnWeight (I := I) Q W).compLpL 2 (volume : Measure ℝ) (coefficientStep Q D τ A n)⟫_ℝ := by
  rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
  have he : (∫ ω, ⟪stochasticStep Q D τ hτ A n ω, W (stochasticStep Q D τ hτ A n ω)⟫_ℝ ∂Q) =
      ∫ ω, ⟪gridSum Q D τ A n ω, W (gridSum Q D τ A n ω)⟫_ℝ ∂Q := by
    apply integral_congr_ae
    filter_upwards [(gridSum_memLp Q D τ hτ A n).coeFn_toLp] with ω hω
    change ⟪(gridSum_memLp Q D τ hτ A n).toLp _ ω,
      W ((gridSum_memLp Q D τ hτ A n).toLp _ ω)⟫_ℝ = _
    rw [hω]
  rw [he, gridSum_isometry Q D W hW τ hτ A n,
    coefficientStep]
  have ht := TimeGridEnergy.grid_weighted (columnWeight (I := I) Q W) τ hτ
    (fun k => (A k).toLp) n
  rw [ht]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [columnWeight_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [((A k).square i).coeFn_toLp] with ω hω
  change ⟪(A k).value i ω, W ((A k).value i ω)⟫_ℝ =
    ⟪((A k).square i).toLp _ ω, W (((A k).square i).toLp _ ω)⟫_ℝ
  rw [hω]

theorem stochasticIntegral_limit_weighted (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (G : RefiningGrids) (A : ∀ n, Coefficients (Z := Z) Q D (G.time n))
    (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (J : Lp Z 2 Q)
    (hu : Tendsto (fun n => coefficientStep Q D (G.time n) (A n) (G.count n)) atTop (𝓝 u))
    (hJ : Tendsto (fun n => stochasticStep Q D (G.time n) (G.monotone n) (A n) (G.count n))
      atTop (𝓝 J)) :
    weightedPairing Q W J J = ⟪u, (columnWeight (I := I) Q W).compLpL 2 (volume : Measure ℝ) u⟫_ℝ := by
  have hJl := (weightedPairing Q W).continuous₂.tendsto (J, J) |>.comp (hJ.prodMk_nhds hJ)
  have hul := Filter.Tendsto.inner (𝕜 := ℝ) hu
    (((columnWeight (I := I) Q W).compLpL 2 (volume : Measure ℝ)).continuous.tendsto u |>.comp hu)
  exact tendsto_nhds_unique hJl (hul.congr' (Eventually.of_forall (fun n =>
    (stochasticStep_weighted Q D W hW (G.time n) (G.monotone n) (A n) (G.count n)).symm)))

theorem stochasticIntegral_weighted (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q D G) :
    weightedPairing Q W (stochasticIntegral Q D G u) (stochasticIntegral Q D G u) =
      ⟪u.val, (columnWeight (I := I) Q W).compLpL 2 (volume : Measure ℝ) u.val⟫_ℝ := by
  obtain ⟨A, hA⟩ := u.property
  exact stochasticIntegral_limit_weighted Q D W hW G A u.val _ hA
    (stochasticIntegral_tendsto Q D G u A hA)
/-- The constructed domain is closed under subtraction, derived from
actual adapted coefficient subtraction. -/
def domainSub (G : RefiningGrids) (u v : IntegralDomain (Z := Z) Q D G) :
    IntegralDomain (Z := Z) Q D G := by
  refine ⟨u.val - v.val, ?_⟩
  obtain ⟨A, hA⟩ := u.property
  obtain ⟨C, hC⟩ := v.property
  refine ⟨fun n => subtract Q D (G.time n) (A n) (C n), ?_⟩
  exact (hA.sub hC).congr' (Eventually.of_forall (fun n =>
    (coefficientStep_sub Q D (G.time n) (A n) (C n) (G.count n)).symm))

theorem stochasticIntegral_sub (G : RefiningGrids) (u v : IntegralDomain (Z := Z) Q D G) :
    stochasticIntegral Q D G (domainSub Q D G u v) =
      stochasticIntegral Q D G u - stochasticIntegral Q D G v := by
  obtain ⟨A, hA⟩ := u.property
  obtain ⟨C, hC⟩ := v.property
  have hsub := stochasticIntegral_tendsto Q D G (domainSub Q D G u v)
    (fun n => subtract Q D (G.time n) (A n) (C n))
    ((hA.sub hC).congr' (Eventually.of_forall (fun n =>
      (coefficientStep_sub Q D (G.time n) (A n) (C n) (G.count n)).symm)))
  have hdiff := (stochasticIntegral_tendsto Q D G u A hA).sub
    (stochasticIntegral_tendsto Q D G v C hC)
  exact tendsto_nhds_unique hsub (hdiff.congr' (Eventually.of_forall (fun n =>
    (stochasticStep_sub Q D (G.time n) (G.monotone n) (A n) (C n) (G.count n)).symm)))

/-- Exact weighted isometry for differences of the completed integrals. -/
theorem stochasticIntegral_sub_weighted (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (G : RefiningGrids) (u v : IntegralDomain (Z := Z) Q D G) :
    weightedPairing Q W (stochasticIntegral Q D G u - stochasticIntegral Q D G v)
      (stochasticIntegral Q D G u - stochasticIntegral Q D G v) =
      ⟪u.val - v.val, (columnWeight (I := I) Q W).compLpL 2 (volume : Measure ℝ) (u.val - v.val)⟫_ℝ := by
  rw [← stochasticIntegral_sub]
  exact stochasticIntegral_weighted Q D W hW G (domainSub Q D G u v)



/-- Literal interval restriction of a time-L² integrand. -/
def timeCut (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (s t : ℝ) :
    Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) :=
  ((Lp.memLp u).indicator measurableSet_Ioc).toLp ((Ioc s t).indicator u)

theorem timeCut_coe (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (s t : ℝ) :
    timeCut Q u s t =ᵐ[volume] (Ioc s t).indicator u :=
  ((Lp.memLp u).indicator measurableSet_Ioc).coeFn_toLp

/-- Deterministic interval consistency of the actual time-L² integrands. -/
theorem timeCut_sub (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    timeCut Q u 0 t - timeCut Q u 0 s = timeCut Q u s t := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (timeCut Q u 0 t) (timeCut Q u 0 s),
    timeCut_coe Q u 0 t, timeCut_coe Q u 0 s, timeCut_coe Q u s t] with r hsub ht' hs' hst'
  rw [hsub, Pi.sub_apply, ht', hs', hst']
  by_cases hr0 : r ≤ 0
  · have hrs : r ≤ s := hr0.trans hs
    simp [Set.indicator, Set.mem_Ioc, not_lt.mpr hr0, not_lt.mpr hrs]
  · have h0r : 0 < r := lt_of_not_ge hr0
    by_cases hrs : r ≤ s
    · have hrt : r ≤ t := hrs.trans hst
      simp [Set.indicator, Set.mem_Ioc, h0r, hrs, hrt, not_lt.mpr hrs]
    · have hsr : s < r := lt_of_not_ge hrs
      simp [Set.indicator, Set.mem_Ioc, h0r, hsr, hrs]

theorem timeCut_weighted (W : Z →L[ℝ] Z)
    (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (s t : ℝ) :
    ⟪timeCut Q u s t, (columnWeight (I := I) Q W).compLpL 2 (volume : Measure ℝ) (timeCut Q u s t)⟫_ℝ =
      ∫ r in Ioc s t, ∑ i, weightedPairing Q W ((u r).ofLp i) ((u r).ofLp i) := by
  rw [L2.inner_def, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [(columnWeight (I := I) Q W).coeFn_compLpL (timeCut Q u s t), timeCut_coe Q u s t]
    with r hw hcut
  rw [hw, hcut]
  by_cases hr : r ∈ Ioc s t
  · simp only [Set.indicator_of_mem hr, columnWeight_inner]
  · simp only [Set.indicator_of_notMem hr, map_zero, inner_zero_left]

/-- The constructed stochastic integrals have the exact weighted increment
isometry. Inputs identify only their actual interval-restricted
coefficient functions; no stochastic increment-moment identity is assumed. -/
theorem stochasticIntegral_increment_isometry (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (G : RefiningGrids) (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (Us Ut : IntegralDomain (Z := Z) Q D G)
    (hUs : Us.val = timeCut Q u 0 s) (hUt : Ut.val = timeCut Q u 0 t) :
    weightedPairing Q W (stochasticIntegral Q D G Ut - stochasticIntegral Q D G Us)
      (stochasticIntegral Q D G Ut - stochasticIntegral Q D G Us) =
      ∫ r in Ioc s t, ∑ i, weightedPairing Q W ((u r).ofLp i) ((u r).ofLp i) := by
  rw [stochasticIntegral_sub_weighted Q D W hW G Ut Us, hUt, hUs,
    timeCut_sub Q u s t hs hst, timeCut_weighted]


end PBGSO.FilteredBrownian
