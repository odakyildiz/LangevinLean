import PBGSO.FilteredBrownianMartingale
import PBGSO.FilteredContinuousIntegrands
import PBGSO.TimeGridCut

/-! # Martingale realization of the completed filtered Brownian integral

Stopped finite sums are represented on actual cell-splitting grids. Their
L² distances from the masked-grid sums equal the distances between literal
time-step integrands. Their limits therefore give the actual completed
integral, and the martingale property follows by conditional projection.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- The first half-cell contains the old coefficient and the second zero.
The cell split is the observation time clamped between its endpoints. -/
def splitCoefficients (τ : ℕ → ℝ≥0) (t : ℝ≥0)
    (A : Coefficients (Z := Z) Q D τ) :
    Coefficients (Z := Z) Q D (TimeGridCut.splitTime τ t) := fun j =>
  ⟨fun i ω => if j % 2 = 0 then (A (j / 2)).value i ω else 0,
    fun i => by
      by_cases hj : j % 2 = 0
      · have he : j = 2 * (j / 2) := by omega
        have ht : TimeGridCut.splitTime τ t j = τ (j / 2) := by
          conv_lhs => rw [he]
          exact TimeGridCut.splitTime_even τ t (j / 2)
        simp only [hj, ite_true]
        change StronglyMeasurable[D.filtration (TimeGridCut.splitTime τ t j)] ((A (j / 2)).value i)
        rw [ht]
        exact (A (j / 2)).adapted i
      · simp only [hj, ite_false]
        exact stronglyMeasurable_const,
    fun i => by
      by_cases hj : j % 2 = 0
      · simpa only [hj, ite_true] using (A (j / 2)).square i
      · simp only [hj, ite_false]
        exact memLp_const (0 : Z)⟩

theorem splitCoefficients_toLp (τ : ℕ → ℝ≥0) (t : ℝ≥0)
    (A : Coefficients (Z := Z) Q D τ) (j : ℕ) :
    (splitCoefficients Q D τ t A j).toLp = TimeGridCut.splitValues (fun k => (A k).toLp) j := by
  apply PiLp.ext
  intro i
  by_cases hj : j % 2 = 0
  · simp only [Coefficient.toLp, PiLp.toLp_apply, TimeGridCut.splitValues, hj, ite_true]
    congr 1
    funext ω
    simp only [splitCoefficients, hj, ite_true]
  · simp only [Coefficient.toLp, PiLp.toLp_apply, TimeGridCut.splitValues, hj, ite_false]
    apply Lp.ext
    filter_upwards [((splitCoefficients Q D τ t A j).square i).coeFn_toLp,
      Lp.coeFn_zero (E := Z) (μ := Q) (p := 2)] with ω ha hz
    change ((splitCoefficients Q D τ t A j).square i).toLp _ ω = (0 : Lp Z 2 Q) ω
    rw [hz, ha]
    simp only [splitCoefficients, hj, ite_false, Pi.zero_apply]

theorem stoppedStep_eq_clamped (a b t : ℝ≥0) (hab : a ≤ b)
    (A : Coefficient (Z := Z) Q D a) (ω : Ω) :
    stoppedStep Q D a b A t ω = noiseStep Q D a (max a (min t b)) A ω := by
  by_cases hat : a ≤ t
  · simp only [stoppedStep, hat, ite_true, max_eq_right (le_min hat hab)]
  · have hta : t ≤ a := le_of_not_ge hat
    have hm : min t b ≤ a := (min_le_left _ _).trans hta
    simp only [stoppedStep, hat, ite_false, max_eq_left hm,
      noiseStep, PredictableIsometry.stepSum, increment, sub_self, zero_smul,
      Finset.sum_const_zero]

theorem stoppedGridSum_eq_split (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    gridSum Q D (TimeGridCut.splitTime τ t) (splitCoefficients Q D τ t A) (2 * n) ω =
      stoppedGridSum Q D τ A n t ω := by
  induction n with
  | zero => simp only [mul_zero, gridSum_zero, stoppedGridSum, Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      gridSum_succ, gridSum_succ, ih, stoppedGridSum_succ]
    have h0 : 2 * n % 2 = 0 := by omega
    have h1 : (2 * n + 1) % 2 ≠ 0 := by omega
    have hd : 2 * n / 2 = n := by omega
    simp only [noiseStep, PredictableIsometry.stepSum, splitCoefficients, h0, h1,
      ite_true, ite_false, smul_zero, Finset.sum_const_zero, add_zero]
    rw [TimeGridCut.splitTime_even, TimeGridCut.splitTime_odd]
    rw [hd]
    congr 1
    exact (stoppedStep_eq_clamped Q D _ _ t (hτ (Nat.le_succ n)) (A n) ω).symm

def stoppedIntegralLp (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (t : ℝ≥0) : Lp Z 2 Q :=
  (stoppedGridSum_memLp Q D τ hτ A n t).toLp (stoppedGridSum Q D τ A n t)

theorem stoppedIntegralLp_eq_split (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (t : ℝ≥0) :
    stoppedIntegralLp Q D τ hτ A n t =
      stochasticStep Q D (TimeGridCut.splitTime τ t) (TimeGridCut.splitTime_monotone τ hτ t)
        (splitCoefficients Q D τ t A) (2 * n) := by
  apply Lp.ext
  filter_upwards [(stoppedGridSum_memLp Q D τ hτ A n t).coeFn_toLp,
    (gridSum_memLp Q D (TimeGridCut.splitTime τ t) (TimeGridCut.splitTime_monotone τ hτ t)
      (splitCoefficients Q D τ t A) (2 * n)).coeFn_toLp] with ω ha hb
  simp only [stoppedIntegralLp, stochasticStep]
  rw [ha, hb, stoppedGridSum_eq_split Q D τ hτ A n t ω]

/-- The key comparison is exact on a genuine common cell-splitting grid. -/
theorem stoppedIntegralLp_dist (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A C : Coefficients (Z := Z) Q D τ) (n : ℕ) (t : ℝ≥0) :
    dist (stoppedIntegralLp Q D τ hτ A n t) (stochasticStep Q D τ hτ C n) =
      dist (timeCut Q (coefficientStep Q D τ A n) 0 t) (coefficientStep Q D τ C n) := by
  let υ := TimeGridCut.splitTime τ t
  have hυ := TimeGridCut.splitTime_monotone τ hτ t
  have he := TimeGridCut.splitTime_even τ t
  rw [stoppedIntegralLp_eq_split]
  rw [← stochasticStep_refine Q D τ υ hτ hυ 2 (by norm_num) he C n]
  rw [stochasticStep_dist]
  rw [coefficientStep_refine]
  have htime : coefficientStep Q D υ (splitCoefficients Q D τ t A) (2 * n) =
      timeCut Q (coefficientStep Q D τ A n) 0 t := by
    simp only [coefficientStep, splitCoefficients_toLp]
    exact TimeGridCut.split_grid_eq_cut τ (fun k => (A k).toLp) t n
  rw [htime]



/-- Stopped finite sums converge to the constructed masked integral.
Both approximation premises concern actual coefficient functions only;
the stochastic convergence is derived through the common split grid. -/
theorem stoppedIntegralLp_tendsto (G : RefiningGrids)
    (A C : ∀ n, Coefficients (Z := Z) Q D (G.time n))
    (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (t : ℝ≥0) (U : IntegralDomain (Z := Z) Q D G)
    (hU : U.val = timeCut Q u 0 t)
    (hA : Tendsto (fun n => coefficientStep Q D (G.time n) (A n) (G.count n)) atTop (𝓝 u))
    (hC : Tendsto (fun n => coefficientStep Q D (G.time n) (C n) (G.count n)) atTop (𝓝 U.val)) :
    Tendsto (fun n => stoppedIntegralLp Q D (G.time n) (G.monotone n) (A n) (G.count n) t)
      atTop (𝓝 (stochasticIntegral Q D G U)) := by
  have hcut := ((timeCut_lipschitz (I := I) (Z := Z) Q 0 t).continuous.tendsto u).comp hA
  rw [← hU] at hcut
  have hdist := hcut.dist hC
  rw [dist_self] at hdist
  have he := hdist.congr' (Eventually.of_forall (fun n =>
    (stoppedIntegralLp_dist Q D (G.time n) (G.monotone n) (A n) (C n) (G.count n) t).symm))
  have hnoise := stochasticIntegral_tendsto Q D G U C hC
  exact hnoise.congr_dist (he.congr' (Eventually.of_forall (fun n => dist_comm _ _)))

/-- A completed integral with actual coefficient approximations is an
actual martingale. The finite raw processes and their convergence are
constructed, rather than supplied as a limiting-martingale hypothesis. -/
theorem completed_masked_integral_martingale (G : RefiningGrids)
    (A : ∀ n, Coefficients (Z := Z) Q D (G.time n))
    (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hA : Tendsto (fun n => coefficientStep Q D (G.time n) (A n) (G.count n)) atTop (𝓝 u))
    (U : ℝ≥0 → IntegralDomain (Z := Z) Q D G)
    (hU : ∀ t, (U t).val = timeCut Q u 0 t)
    (C : ∀ _t : ℝ≥0, ∀ n, Coefficients (Z := Z) Q D (G.time n))
    (hC : ∀ t, Tendsto (fun n => coefficientStep Q D (G.time n) (C t n) (G.count n))
      atTop (𝓝 (U t).val)) :
    Martingale (MartingaleL2Limit.representative Q D.filtration
      (fun t => stochasticIntegral Q D G (U t))) D.filtration Q := by
  apply stoppedGridSum_limit_martingale Q D G A
  intro t
  exact stoppedIntegralLp_tendsto Q D G A (C t) u t (U t) (hU t) hA (hC t)



/-- Every observation time has an actual masked domain entry, including
times beyond the fixed horizon where the integral stays stopped. -/
def continuousCutDomain (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ≥0) :
    IntegralDomain (Z := Z) Q D (dyadicGrids T) :=
  Classical.choose (exists_masked_continuous_domain Q D T u hu hU 0 t)

theorem continuousCutDomain_coe (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ≥0) :
    (continuousCutDomain Q D T u hu hU t).val =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator ((Ioc 0 (t : ℝ)).indicator u) :=
  Classical.choose_spec (exists_masked_continuous_domain Q D T u hu hU 0 t)

theorem continuousCutDomain_eq_timeCut (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ≥0) :
    (continuousCutDomain Q D T u hu hU t).val =
      timeCut Q (continuousDomain Q D T u hu hU).val 0 t := by
  apply Lp.ext
  filter_upwards [continuousCutDomain_coe Q D T u hu hU t,
    timeCut_coe Q (continuousDomain Q D T u hu hU).val 0 t,
    continuousDomain_coe Q D T u hu hU] with r hcut ht hfull
  rw [hcut, ht]
  by_cases hR : r ∈ Ioc 0 (T : ℝ) <;> by_cases hrt : r ∈ Ioc 0 (t : ℝ)
  all_goals simp only [Set.indicator, hR, hrt, ite_true, ite_false] at hfull ⊢
  all_goals try rw [hfull]

/-- Literal dyadic full-curve coefficients converge to the chosen full domain. -/
theorem curveCoefficients_tendsto (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    Tendsto (fun n => coefficientStep Q D ((dyadicGrids T).time n)
      (curveCoefficients Q D u hU ((dyadicGrids T).time n)) ((dyadicGrids T).count n))
      atTop (𝓝 (continuousDomain Q D T u hu hU).val) := by
  obtain ⟨P, hP0, hP⟩ := TimeGridContinuity.exists_horizon_bound T u hu
  have he : TimeGridContinuity.horizonLp T u hu.aestronglyMeasurable P hP =
      (continuousDomain Q D T u hu hU).val := by
    apply Lp.ext
    exact (TimeGridContinuity.horizon_memLp T u hu.aestronglyMeasurable P hP).coeFn_toLp.trans
      (continuousDomain_coe Q D T u hu hU).symm
  simp only [curveCoefficients_step]
  rw [← he]
  exact TimeGridContinuity.dyadic_grid_tendsto T u hu.aestronglyMeasurable P hP0 hP
    (ae_of_all _ (fun r => hu.continuousAt))

theorem masked_curveCoefficients_tendsto (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ≥0) :
    Tendsto (fun n => coefficientStep Q D ((dyadicGrids T).time n)
      (curveCoefficients Q D ((Ioc 0 (t : ℝ)).indicator u)
        (masked_columns_adapted Q D u hU 0 t) ((dyadicGrids T).time n)) ((dyadicGrids T).count n))
      atTop (𝓝 (continuousCutDomain Q D T u hu hU t).val) := by
  obtain ⟨P, hP0, hP⟩ := TimeGridContinuity.exists_horizon_bound T u hu
  let v := (Ioc 0 (t : ℝ)).indicator u
  have hvm : AEStronglyMeasurable v (volume : Measure ℝ) :=
    hu.aestronglyMeasurable.indicator measurableSet_Ioc
  have hvP : ∀ r ∈ Icc 0 (T : ℝ), ‖v r‖ ≤ P :=
    fun r hr => (norm_indicator_le_norm_self u r).trans (hP r hr)
  have he : TimeGridContinuity.horizonLp T v hvm P hvP =
      (continuousCutDomain Q D T u hu hU t).val := by
    apply Lp.ext
    exact (TimeGridContinuity.horizon_memLp T v hvm P hvP).coeFn_toLp.trans
      (continuousCutDomain_coe Q D T u hu hU t).symm
  simp only [curveCoefficients_step]
  rw [← he]
  exact TimeGridContinuity.dyadic_masked_grid_tendsto T u hu 0 t P hP0 hP

/-- The actual completed Brownian integral of continuous adapted diffusion
columns is a martingale. Approximation convergence and all finite
martingale properties have been derived from the primitive driver. -/
theorem continuous_integral_martingale (T : ℝ≥0) (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q)
    (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) :
    Martingale (MartingaleL2Limit.representative Q D.filtration
      (fun t => stochasticIntegral Q D (dyadicGrids T) (continuousCutDomain Q D T u hu hU t)))
      D.filtration Q := by
  exact completed_masked_integral_martingale Q D (dyadicGrids T)
    (fun n => curveCoefficients Q D u hU ((dyadicGrids T).time n))
    (continuousDomain Q D T u hu hU).val (curveCoefficients_tendsto Q D T u hu hU)
    (continuousCutDomain Q D T u hu hU) (continuousCutDomain_eq_timeCut Q D T u hu hU)
    (fun t n => curveCoefficients Q D ((Ioc 0 (t : ℝ)).indicator u)
      (masked_columns_adapted Q D u hU 0 t) ((dyadicGrids T).time n))
    (masked_curveCoefficients_tendsto Q D T u hu hU)



/-- The actual continuous-column integral is the timewise L² limit of
one fixed sequence of stopped predictable martingales. -/
theorem continuous_integral_stopped_tendsto (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ≥0) :
    Tendsto (fun n => stoppedIntegralLp Q D ((dyadicGrids T).time n) ((dyadicGrids T).monotone n)
      (curveCoefficients Q D u hU ((dyadicGrids T).time n)) ((dyadicGrids T).count n) t)
      atTop (𝓝 (stochasticIntegral Q D (dyadicGrids T) (continuousCutDomain Q D T u hu hU t))) := by
  exact stoppedIntegralLp_tendsto Q D (dyadicGrids T)
    (fun n => curveCoefficients Q D u hU ((dyadicGrids T).time n))
    (fun n => curveCoefficients Q D ((Ioc 0 (t : ℝ)).indicator u)
      (masked_columns_adapted Q D u hU 0 t) ((dyadicGrids T).time n))
    (continuousDomain Q D T u hu hU).val t (continuousCutDomain Q D T u hu hU t)
    (continuousCutDomain_eq_timeCut Q D T u hu hU t)
    (curveCoefficients_tendsto Q D T u hu hU) (masked_curveCoefficients_tendsto Q D T u hu hU t)

/-- The actual adapted martingale representative equals the constructed
L² Brownian integral at each time. -/
theorem continuous_integral_representative_ae (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ≥0) :
    MartingaleL2Limit.representative Q D.filtration
      (fun r => stochasticIntegral Q D (dyadicGrids T) (continuousCutDomain Q D T u hu hU r)) t =ᵐ[Q]
      stochasticIntegral Q D (dyadicGrids T) (continuousCutDomain Q D T u hu hU t) := by
  exact MartingaleL2Limit.representative_ae Q D.filtration
    (fun n => stoppedGridSum Q D ((dyadicGrids T).time n)
      (curveCoefficients Q D u hU ((dyadicGrids T).time n)) ((dyadicGrids T).count n))
    (fun n => stoppedGridSum_martingale Q D ((dyadicGrids T).time n) ((dyadicGrids T).monotone n)
      (curveCoefficients Q D u hU ((dyadicGrids T).time n)) ((dyadicGrids T).count n))
    (fun n r => stoppedGridSum_memLp Q D ((dyadicGrids T).time n) ((dyadicGrids T).monotone n)
      (curveCoefficients Q D u hU ((dyadicGrids T).time n)) ((dyadicGrids T).count n) r)
    (fun r => stochasticIntegral Q D (dyadicGrids T) (continuousCutDomain Q D T u hu hU r))
    (continuous_integral_stopped_tendsto Q D T u hu hU) t

/-- The constructed actual martingale is square integrable. -/
theorem continuous_integral_representative_memLp (T : ℝ≥0)
    (u : ℝ → ColumnHilbert (I := I) (Z := Z) Q) (hu : Continuous u)
    (hU : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (u t i) Q) (t : ℝ≥0) :
    MemLp (MartingaleL2Limit.representative Q D.filtration
      (fun r => stochasticIntegral Q D (dyadicGrids T) (continuousCutDomain Q D T u hu hU r)) t) 2 Q :=
  (memLp_congr_ae (continuous_integral_representative_ae Q D T u hu hU t)).mpr (Lp.memLp _)

end PBGSO.FilteredBrownian
