import PBGSO.GridIntegralCompletion

/-! Weighted Itô isometry for the constructed Brownian completion. -/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.TimeGridEnergy
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]

theorem columns_inner (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (i j : ℕ) (a b : R) :
    ⟪column (τ i) (τ (i + 1)) a, column (τ j) (τ (j + 1)) b⟫_ℝ =
      if i = j then ((τ (i + 1) : ℝ) - τ i) * ⟪a, b⟫_ℝ else 0 := by
  rw [column_inner]
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, Set.inter_self]
    simp only [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal
      (sub_nonneg.mpr (show (τ i : ℝ) ≤ τ (i + 1) from hτ (Nat.le_succ i)))]
  · rw [ite_eq_right hij]
    have hd : Disjoint (Ioc (τ i : ℝ) (τ (i + 1))) (Ioc (τ j : ℝ) (τ (j + 1))) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      obtain h | h := lt_or_gt_of_ne hij
      · have hh : (τ (i + 1) : ℝ) ≤ τ j := hτ (Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hx.2.trans hh)) hy.1
      · have hh : (τ (j + 1) : ℝ) ≤ τ i := hτ (Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hy.2.trans hh)) hx.1
    rw [Set.disjoint_iff_inter_eq_empty.mp hd]
    simp

theorem grid_inner (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A C : ℕ → R) (n : ℕ) :
    ⟪grid τ A n, grid τ C n⟫_ℝ =
      ∑ k : Fin n, ((τ (k + 1) : ℝ) - τ k) * ⟪A k, C k⟫_ℝ := by
  simp only [grid, sum_inner, inner_sum]
  simp_rw [columns_inner τ hτ]
  simp only [Fin.val_inj]
  simp

theorem column_postmap (W : R →L[ℝ] R) (s t : ℝ) (a : R) :
    W.compLpL 2 (volume : Measure ℝ) (column s t a) = column s t (W a) := by
  apply Lp.ext
  filter_upwards [W.coeFn_compLpL (column s t a),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc) (hμs := by simp)
      (c := a) (s := Ioc s t),
    indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc) (hμs := by simp)
      (c := W a) (s := Ioc s t)] with r hw h1 h2
  rw [hw]
  change column s t a r = _ at h1
  change column s t (W a) r = _ at h2
  rw [h1, h2]
  by_cases hr : r ∈ Ioc s t
  · simp only [Set.indicator_of_mem hr]
  · simp only [Set.indicator_of_notMem hr, map_zero]

theorem grid_postmap (W : R →L[ℝ] R) (τ : ℕ → ℝ≥0) (A : ℕ → R) (n : ℕ) :
    W.compLpL 2 (volume : Measure ℝ) (grid τ A n) = grid τ (fun k => W (A k)) n := by
  simp only [grid, map_sum, column_postmap]

theorem grid_weighted (W : R →L[ℝ] R) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : ℕ → R) (n : ℕ) :
    ⟪grid τ A n, W.compLpL 2 (volume : Measure ℝ) (grid τ A n)⟫_ℝ =
      ∑ k : Fin n, ((τ (k + 1) : ℝ) - τ k) * ⟪A k, W (A k)⟫_ℝ := by
  rw [grid_postmap, grid_inner τ hτ]

end PBGSO.TimeGridEnergy

namespace PBGSO.GridIntegralCompletion
open PBGSO.BrownianGridIsometry PBGSO.QuadraticMartingale
variable {Ω Z : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q)
  (hBm : ∀ t, Measurable (B t))

include hB in
theorem stochasticStep_weighted (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : Coefficients (Z := Z) Q B hBm τ) (n : ℕ) :
    weightedPairing Q W (stochasticStep Q B hB hBm τ hτ A n)
      (stochasticStep Q B hB hBm τ hτ A n) =
    ⟪coefficientStep Q B hBm τ A n,
      (W.compLpL 2 Q).compLpL 2 (volume : Measure ℝ) (coefficientStep Q B hBm τ A n)⟫_ℝ := by
  rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
  let hS := gridSum_memLp Q B hB hBm τ hτ (fun k => (A k).value)
    (fun k => (A k).adapted) (fun k => (A k).square) n
  have he : (∫ ω, ⟪stochasticStep Q B hB hBm τ hτ A n ω,
      W (stochasticStep Q B hB hBm τ hτ A n ω)⟫_ℝ ∂Q) =
      ∫ ω, ⟪gridSum B τ (fun k => (A k).value) n ω,
        W (gridSum B τ (fun k => (A k).value) n ω)⟫_ℝ ∂Q := by
    apply integral_congr_ae
    filter_upwards [hS.coeFn_toLp] with ω hω
    change ⟪hS.toLp _ ω, W (hS.toLp _ ω)⟫_ℝ = _
    rw [hω]
  rw [he, gridSum_isometry Q B hB hBm W hW τ hτ
    (fun k => (A k).value) (fun k => (A k).adapted) (fun k => (A k).square) n,
    coefficientStep, TimeGridEnergy.grid_weighted (W.compLpL 2 Q) τ hτ]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [lp_weighted_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(A k).square.coeFn_toLp] with ω hω
  change ⟪(A k).value ω, W ((A k).value ω)⟫_ℝ =
    ⟪(A k).square.toLp _ ω, W ((A k).square.toLp _ ω)⟫_ℝ
  rw [hω]

include hB in
/-- Weighted isometry of the actual stochastic limit, derived by
continuity of the two quadratic forms from the finite Brownian sums. -/
theorem stochasticIntegral_limit_weighted (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (G : RefiningGrids) (A : ∀ n, Coefficients (Z := Z) Q B hBm (G.time n))
    (u : Lp (Lp Z 2 Q) 2 (volume : Measure ℝ)) (I : Lp Z 2 Q)
    (hu : Tendsto (fun n => coefficientStep Q B hBm (G.time n) (A n) (G.count n)) atTop (𝓝 u))
    (hI : Tendsto (fun n => stochasticStep Q B hB hBm (G.time n) (G.monotone n) (A n) (G.count n))
      atTop (𝓝 I)) :
    weightedPairing Q W I I = ⟪u, (W.compLpL 2 Q).compLpL 2 (volume : Measure ℝ) u⟫_ℝ := by
  have hIl := (weightedPairing Q W).continuous₂.tendsto (I, I) |>.comp (hI.prodMk_nhds hI)
  have hul := Filter.Tendsto.inner (𝕜 := ℝ) hu (((W.compLpL 2 Q).compLpL 2 (volume : Measure ℝ)).continuous.tendsto u |>.comp hu)
  apply tendsto_nhds_unique hIl
  exact hul.congr' (Eventually.of_forall (fun n =>
    (stochasticStep_weighted Q B hB hBm W hW (G.time n) (G.monotone n) (A n) (G.count n)).symm))

include hB in
/-- Exact weighted Itô isometry for the constructed completion integral. -/
theorem stochasticIntegral_weighted (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q B hBm G) :
    weightedPairing Q W (stochasticIntegral Q B hB hBm G u) (stochasticIntegral Q B hB hBm G u) =
      ⟪u.val, (W.compLpL 2 Q).compLpL 2 (volume : Measure ℝ) u.val⟫_ℝ := by
  obtain ⟨A, hA⟩ := u.property
  exact stochasticIntegral_limit_weighted Q B hB hBm W hW G A u.val _ hA
    (stochasticIntegral_tendsto Q B hB hBm G u A hA)



/-- The constructed domain is closed under subtraction, derived from
actual adapted coefficient subtraction. -/
def domainSub (G : RefiningGrids) (u v : IntegralDomain (Z := Z) Q B hBm G) :
    IntegralDomain (Z := Z) Q B hBm G := by
  refine ⟨u.val - v.val, ?_⟩
  obtain ⟨A, hA⟩ := u.property
  obtain ⟨C, hC⟩ := v.property
  refine ⟨fun n => subtract Q B hBm (G.time n) (A n) (C n), ?_⟩
  exact (hA.sub hC).congr' (Eventually.of_forall (fun n =>
    (coefficientStep_sub Q B hBm (G.time n) (A n) (C n) (G.count n)).symm))

include hB in
theorem stochasticIntegral_sub (G : RefiningGrids) (u v : IntegralDomain (Z := Z) Q B hBm G) :
    stochasticIntegral Q B hB hBm G (domainSub Q B hBm G u v) =
      stochasticIntegral Q B hB hBm G u - stochasticIntegral Q B hB hBm G v := by
  obtain ⟨A, hA⟩ := u.property
  obtain ⟨C, hC⟩ := v.property
  have hsub := stochasticIntegral_tendsto Q B hB hBm G (domainSub Q B hBm G u v)
    (fun n => subtract Q B hBm (G.time n) (A n) (C n))
    ((hA.sub hC).congr' (Eventually.of_forall (fun n =>
      (coefficientStep_sub Q B hBm (G.time n) (A n) (C n) (G.count n)).symm)))
  have hdiff := (stochasticIntegral_tendsto Q B hB hBm G u A hA).sub
    (stochasticIntegral_tendsto Q B hB hBm G v C hC)
  exact tendsto_nhds_unique hsub (hdiff.congr' (Eventually.of_forall (fun n =>
    (stochasticStep_sub Q B hB hBm (G.time n) (G.monotone n) (A n) (C n) (G.count n)).symm)))

include hB in
/-- Exact weighted isometry for differences of the completed integrals. -/
theorem stochasticIntegral_sub_weighted (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (G : RefiningGrids) (u v : IntegralDomain (Z := Z) Q B hBm G) :
    weightedPairing Q W (stochasticIntegral Q B hB hBm G u - stochasticIntegral Q B hB hBm G v)
      (stochasticIntegral Q B hB hBm G u - stochasticIntegral Q B hB hBm G v) =
      ⟪u.val - v.val, (W.compLpL 2 Q).compLpL 2 (volume : Measure ℝ) (u.val - v.val)⟫_ℝ := by
  rw [← stochasticIntegral_sub]
  exact stochasticIntegral_weighted Q B hB hBm W hW G (domainSub Q B hBm G u v)

/-- Literal interval restriction of a time-L² integrand. -/
def timeCut (u : Lp (Lp Z 2 Q) 2 (volume : Measure ℝ)) (s t : ℝ) :
    Lp (Lp Z 2 Q) 2 (volume : Measure ℝ) :=
  ((Lp.memLp u).indicator measurableSet_Ioc).toLp ((Ioc s t).indicator u)

theorem timeCut_coe (u : Lp (Lp Z 2 Q) 2 (volume : Measure ℝ)) (s t : ℝ) :
    timeCut Q u s t =ᵐ[volume] (Ioc s t).indicator u :=
  ((Lp.memLp u).indicator measurableSet_Ioc).coeFn_toLp

/-- Deterministic interval consistency of the actual time-L² integrands. -/
theorem timeCut_sub (u : Lp (Lp Z 2 Q) 2 (volume : Measure ℝ)) (s t : ℝ)
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
    (u : Lp (Lp Z 2 Q) 2 (volume : Measure ℝ)) (s t : ℝ) :
    ⟪timeCut Q u s t, (W.compLpL 2 Q).compLpL 2 (volume : Measure ℝ) (timeCut Q u s t)⟫_ℝ =
      ∫ r in Ioc s t, weightedPairing Q W (u r) (u r) := by
  rw [L2.inner_def, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [(W.compLpL 2 Q).coeFn_compLpL (timeCut Q u s t), timeCut_coe Q u s t]
    with r hw hcut
  rw [hw, hcut]
  by_cases hr : r ∈ Ioc s t
  · simp only [Set.indicator_of_mem hr, weightedPairing_apply]
  · simp only [Set.indicator_of_notMem hr, map_zero, inner_zero_left]

include hB in
/-- The constructed stochastic integrals have the exact weighted increment
isometry. Inputs identify only their actual interval-restricted
coefficient functions; no stochastic increment-moment identity is assumed. -/
theorem stochasticIntegral_increment_isometry (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (G : RefiningGrids) (u : Lp (Lp Z 2 Q) 2 (volume : Measure ℝ))
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t)
    (Us Ut : IntegralDomain (Z := Z) Q B hBm G)
    (hUs : Us.val = timeCut Q u 0 s) (hUt : Ut.val = timeCut Q u 0 t) :
    weightedPairing Q W (stochasticIntegral Q B hB hBm G Ut - stochasticIntegral Q B hB hBm G Us)
      (stochasticIntegral Q B hB hBm G Ut - stochasticIntegral Q B hB hBm G Us) =
      ∫ r in Ioc s t, weightedPairing Q W (u r) (u r) := by
  rw [stochasticIntegral_sub_weighted Q B hB hBm W hW G Ut Us, hUt, hUs,
    timeCut_sub Q u s t hs hst, timeCut_weighted]

end PBGSO.GridIntegralCompletion
