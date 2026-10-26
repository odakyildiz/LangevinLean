import PBGSO.StoppedIntegralMask
import PBGSO.DyadicStopping

/-! # Actual L² limits of randomly stopped diffusion columns -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian

/-- Dominated convergence in actual L² spaces, derived from the exact square
norm integral and scalar dominated convergence. -/
theorem lp_tendsto_dominated_square {A H : Type*} [MeasurableSpace A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (μ : Measure A) (U : ℕ → Lp H 2 μ) (V : Lp H 2 μ) (B : A → ℝ)
    (hB : Integrable B μ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖U n a - V a‖ ^ 2 ≤ B a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n => U n a) atTop (𝓝 (V a))) :
    Tendsto U atTop (𝓝 V) := by
  have hb (n : ℕ) : ∀ᵐ a ∂μ, ‖‖(U n - V) a‖ ^ 2‖ ≤ B a := by
    filter_upwards [hbound n, Lp.coeFn_sub (U n) V] with a hba hsub
    rw [hsub, Pi.sub_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hba
  have hl : ∀ᵐ a ∂μ, Tendsto (fun n => ‖(U n - V) a‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim, ae_all_iff.mpr (fun n => Lp.coeFn_sub (U n) V)] with a hla hsub
    have he := (hla.sub_const (V a)).norm.pow 2
    have he' : Tendsto (fun n => ‖U n a - V a‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using he
    exact he'.congr' (Eventually.of_forall (fun n => by
      change ‖U n a - V a‖ ^ 2 = ‖(U n - V) a‖ ^ 2
      rw [hsub n]
      rfl))
  have hDCT := tendsto_integral_of_dominated_convergence B
    (fun n => (Lp.aestronglyMeasurable (U n - V)).norm.pow 2) hB hb hl
  have hsq : Tendsto (fun n => ‖U n - V‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [ProximalLangevin.lp_norm_sq_eq_integral, Pi.pow_apply, integral_zero] using hDCT
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hn

variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Event restriction contracts the actual finite-column Hilbert norm. -/
theorem columnEventMask_norm (E : Set Ω) (hE : MeasurableSet E)
    (U : ColumnHilbert (I := I) (Z := Z) Q) : ‖columnEventMask Q E hE U‖ ≤ ‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i _
  rw [columnEventMask_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (eventMaskValue_norm Q E hE (U.ofLp i)) 2

/-- Stabilizing random stopping events pass through actual L² event
restriction by dominated convergence, with no atom-free boundary premise. -/
theorem eventMask_tendsto (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
    (F : Set Ω) (hF : MeasurableSet F) (U : Lp Z 2 Q)
    (hEF : ∀ ω, ∀ᶠ n in atTop, (ω ∈ E n ↔ ω ∈ F)) :
    Tendsto (fun n => eventMask Q (E n) (hE n) U) atTop (𝓝 (eventMask Q F hF U)) := by
  apply lp_tendsto_dominated_square Q _ _ (fun ω => 4 * ‖U ω‖ ^ 2)
  · exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U)).mp (Lp.memLp U)).const_mul 4
  · intro n
    filter_upwards [eventMask_coe Q (E n) (hE n) U, eventMask_coe Q F hF U] with ω hn hf
    rw [hn, hf]
    by_cases he : ω ∈ E n <;> by_cases hf' : ω ∈ F <;>
      simp [Set.indicator, he, hf', norm_neg, sq_nonneg] <;> nlinarith [sq_nonneg ‖U ω‖]
  · filter_upwards [ae_all_iff.mpr (fun n => eventMask_coe Q (E n) (hE n) U),
      eventMask_coe Q F hF U] with ω hn hf
    apply tendsto_const_nhds.congr'
    filter_upwards [hEF ω] with n he
    rw [hn n, hf]
    by_cases h : ω ∈ F <;> simp [Set.indicator, h, he]

/-- The same derived convergence holds simultaneously for all actual
Brownian columns; finite-dimensional coordinate equivalence supplies it. -/
theorem columnEventMask_tendsto (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
    (F : Set Ω) (hF : MeasurableSet F) (U : ColumnHilbert (I := I) (Z := Z) Q)
    (hEF : ∀ ω, ∀ᶠ n in atTop, (ω ∈ E n ↔ ω ∈ F)) :
    Tendsto (fun n => columnEventMask Q (E n) (hE n) U) atTop (𝓝 (columnEventMask Q F hF U)) := by
  have ht : Tendsto (fun n i => eventMask Q (E n) (hE n) (U.ofLp i)) atTop
      (𝓝 (fun i => eventMask Q F hF (U.ofLp i))) :=
    tendsto_pi_nhds.mpr (fun i => eventMask_tendsto Q E hE F hF (U.ofLp i) hEF)
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => Lp Z 2 Q)).symm.continuous.tendsto _).comp ht

/-- Literal original diffusion columns restricted by a measurable bounded
random time; no time-regularity of the coefficients is imposed. -/
def randomStopCurve (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (r : ℝ) : ColumnHilbert (I := I) (Z := Z) Q :=
  if r ∈ Ioc 0 (T : ℝ) then
    columnEventMask Q {ω | r ≤ (τ ω : ℝ)}
      (measurableSet_le measurable_const (measurable_coe_nnreal_real.comp hτ)) (U r)
  else 0

theorem randomStopCurve_norm (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (r : ℝ) :
    ‖randomStopCurve Q T τ hτ U r‖ ≤ ‖U r‖ := by
  unfold randomStopCurve
  split_ifs
  · exact columnEventMask_norm Q _ _ _
  · simp

variable (D : Driver (I := I) Q)

/-- Primitive stopping events imply actual measurability of the random time. -/
theorem stoppingTime_measurable (τ : Ω → ℝ≥0)
    (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t}) : Measurable τ := by
  apply measurable_of_Iic
  intro t
  exact D.filtration.le _ _ (hstop t)

variable {Q D}

theorem GridStoppingIndex.knot_measurable {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) : Measurable (fun ω => τ (σ.index ω)) :=
  (measurable_of_countable τ).comp σ.index_measurable

/-- The finite-grid mask is exactly the literal random-time diffusion curve. -/
theorem GridStoppingIndex.maskInput_eq_randomCurve {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (hτ : Monotone τ) (T : ℝ≥0)
    (hz : τ 0 = 0) (he : τ n = T)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    σ.maskInput U =ᵐ[volume]
      randomStopCurve Q T (fun ω => τ (σ.index ω)) σ.knot_measurable U := by
  filter_upwards [σ.maskInput_raw hτ U] with r hraw
  apply PiLp.ext
  intro i
  apply Lp.ext
  by_cases hr : r ∈ Ioc 0 (T : ℝ)
  · change (σ.maskInput U r).ofLp i =ᵐ[Q] _
    rw [randomStopCurve, if_pos hr, columnEventMask_apply]
    filter_upwards [hraw i, eventMask_coe Q {ω | r ≤ (τ (σ.index ω) : ℝ)}
      (measurableSet_le measurable_const (measurable_coe_nnreal_real.comp σ.knot_measurable))
      ((U r).ofLp i)] with ω hω hE
    rw [hω, hE]
    simp [hz, he, hr, Set.indicator]
  · rw [randomStopCurve, if_neg hr]
    filter_upwards [hraw i, Lp.coeFn_zero Z 2 Q] with ω hω hzero
    simpa only [hz, he, hr, false_and, ite_false, NNReal.coe_zero, PiLp.zero_apply,
      Pi.zero_apply, hzero] using hω

variable (Q D)

/-- Actual measurability of each derived dyadic stopping time. -/
theorem dyadicStop_measurable (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t}) (m : ℕ) :
    Measurable (dyadicStop T τ hτ m) :=
  (dyadicStoppingIndex Q D T τ hτ hstop m).knot_measurable

/-- The actual stopped diffusion curves converge at each time in the
finite-column L²(Ω) norm, by the proved ceiling-indicator stabilization. -/
theorem randomStopCurve_dyadic_tendsto (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (r : ℝ) :
    Tendsto (fun m => randomStopCurve Q T (dyadicStop T τ hτ m)
      (dyadicStop_measurable Q D T τ hτ hstop m) U r) atTop
      (𝓝 (randomStopCurve Q T τ (stoppingTime_measurable Q D τ hstop) U r)) := by
  by_cases hr : r ∈ Ioc 0 (T : ℝ)
  · simp only [randomStopCurve, if_pos hr]
    exact columnEventMask_tendsto Q _ _ _ _ (U r)
      (fun ω => dyadicStop_indicator_eventually T τ hτ r ω)
  · simp only [randomStopCurve, if_neg hr]
    exact tendsto_const_nhds

/-- The original random-time diffusion curve is genuinely time-measurable,
derived as the L²(Ω) limit of actual finite-grid masks. -/
theorem randomStopCurve_aestronglyMeasurable (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    AEStronglyMeasurable (randomStopCurve Q T τ (stoppingTime_measurable Q D τ hstop) U) volume := by
  let σ m := dyadicStoppingIndex Q D T τ hτ hstop m
  have heq (m : ℕ) : (σ m).maskInput U =ᵐ[volume]
      randomStopCurve Q T (dyadicStop T τ hτ m) (dyadicStop_measurable Q D T τ hτ hstop m) U := by
    exact (σ m).maskInput_eq_randomCurve ((dyadicGrids T).monotone m) T
      (by simp [GridIntegralCompletion.dyadicGrids]) (dyadic_time_last T m) U
  apply aestronglyMeasurable_of_tendsto_ae atTop (fun m => Lp.aestronglyMeasurable ((σ m).maskInput U))
  filter_upwards [ae_all_iff.mpr heq] with r hr
  exact (randomStopCurve_dyadic_tendsto Q D T τ hτ hstop U r).congr'
    (Eventually.of_forall (fun m => (hr m).symm))

/-- Time-L² integrability follows from the original diffusion norm, rather
than being supplied as a stopped-process or localization assumption. -/
theorem randomStopCurve_memLp (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    MemLp (randomStopCurve Q T τ (stoppingTime_measurable Q D τ hstop) U) 2 volume :=
  (Lp.memLp U).norm.mono' (randomStopCurve_aestronglyMeasurable Q D T τ hτ hstop U)
    (Eventually.of_forall (fun r => randomStopCurve_norm Q T τ _ U r))

/-- The actual time-L² class of the original randomly stopped diffusion. -/
def randomStoppedInput (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) :=
  (randomStopCurve_memLp Q D T τ hτ hstop U).toLp
    (randomStopCurve Q T τ (stoppingTime_measurable Q D τ hstop) U)


theorem randomStoppedInput_coe (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    randomStoppedInput Q D T τ hτ hstop U =ᵐ[volume]
      randomStopCurve Q T τ (stoppingTime_measurable Q D τ hstop) U :=
  (randomStopCurve_memLp Q D T τ hτ hstop U).coeFn_toLp

/-- Dyadic stopping masks converge in the actual time/space L² norm by two
applications of dominated convergence, both controlled by the original σ. -/
theorem dyadicStoppedInput_tendsto (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    Tendsto (fun m => (dyadicStoppingIndex Q D T τ hτ hstop m).maskInput U) atTop
      (𝓝 (randomStoppedInput Q D T τ hτ hstop U)) := by
  let σ m := dyadicStoppingIndex Q D T τ hτ hstop m
  have heq (m : ℕ) : (σ m).maskInput U =ᵐ[volume]
      randomStopCurve Q T (dyadicStop T τ hτ m) (dyadicStop_measurable Q D T τ hτ hstop m) U :=
    (σ m).maskInput_eq_randomCurve ((dyadicGrids T).monotone m) T
      (by simp [GridIntegralCompletion.dyadicGrids]) (dyadic_time_last T m) U
  apply lp_tendsto_dominated_square volume _ _ (fun r => 4 * ‖U r‖ ^ 2)
  · exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U)).mp (Lp.memLp U)).const_mul 4
  · intro m
    filter_upwards [heq m, randomStoppedInput_coe Q D T τ hτ hstop U] with r hm hv
    rw [hm, hv]
    have hb := (norm_sub_le _ _).trans (add_le_add
      (randomStopCurve_norm Q T (dyadicStop T τ hτ m) (dyadicStop_measurable Q D T τ hτ hstop m) U r)
      (randomStopCurve_norm Q T τ (stoppingTime_measurable Q D τ hstop) U r))
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith
  · filter_upwards [ae_all_iff.mpr heq, randomStoppedInput_coe Q D T τ hτ hstop U]
      with r hm hv
    rw [hv]
    exact (randomStopCurve_dyadic_tendsto Q D T τ hτ hstop U r).congr'
      (Eventually.of_forall (fun m => (hm m).symm))

/-- The original bounded-stopping diffusion lies in the actual predictable
stochastic domain. No density or stochastic-limit premise is supplied. -/
theorem randomStoppedInput_mem_closed (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    randomStoppedInput Q D T τ hτ hstop U.val ∈
      closure (Set.range (finiteStepInput (Z := Z) Q D (dyadicGrids T))) := by
  apply isClosed_closure.mem_of_tendsto (dyadicStoppedInput_tendsto Q D T τ hτ hstop U.val)
  exact Eventually.of_forall (fun m =>
    (dyadicStoppingIndex Q D T τ hτ hstop m).maskInput_mem_closed T m U)

/-- Actual closed-domain entry for an arbitrary bounded stopping time. -/
def boundedStoppedDomain (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    ClosedStepDomain (Z := Z) Q D (dyadicGrids T) :=
  ⟨randomStoppedInput Q D T τ hτ hstop U.val, randomStoppedInput_mem_closed Q D T τ hτ hstop U⟩

/-- A fixed-time computed stochastic integral contracts the actual
coefficient distance, directly from its proved closed-domain isometry. -/
theorem closedIntegral_lipschitz (T t : ℝ≥0) :
    LipschitzWith 1 (fun U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T) => closedIntegral Q D T U t) := by
  apply LipschitzWith.of_dist_le_mul
  intro U V
  simp only [NNReal.coe_one, one_mul]
  rw [closedIntegral, closedIntegral, (closedStepIntegral_isometry Q D (dyadicGrids T)).dist_eq]
  change dist (timeCut Q U.val 0 t) (timeCut Q V.val 0 t) ≤ dist U.val V.val
  simpa only [NNReal.coe_one, one_mul] using
    (timeCut_lipschitz (I := I) (Z := Z) Q 0 t).dist_le_mul U.val V.val

/-- The actual dyadic stopped Brownian noises converge in L² to the
computed integral of the original bounded-stopping diffusion. -/
theorem dyadicStoppedIntegral_tendsto (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω ≤ T) (hstop : ∀ t, MeasurableSet[D.filtration t] {ω | τ ω ≤ t})
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    Tendsto (fun m => (dyadicStoppingIndex Q D T τ hτ hstop m).stoppedIntegral T m U t)
      atTop (𝓝 (closedIntegral Q D T (boundedStoppedDomain Q D T τ hτ hstop U) t)) := by
  have hl := dyadicStoppedInput_tendsto Q D T τ hτ hstop U.val
  have hd : Tendsto (fun m => (dyadicStoppingIndex Q D T τ hτ hstop m).stoppedDomain T m U)
      atTop (𝓝 (boundedStoppedDomain Q D T τ hτ hstop U)) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hl ε hε
    refine ⟨N, fun m hm => ?_⟩
    change dist ((dyadicStoppingIndex Q D T τ hτ hstop m).maskInput U.val)
      (randomStoppedInput Q D T τ hτ hstop U.val) < ε
    exact hN m hm
  have he := ((closedIntegral_lipschitz Q D T t).continuous.tendsto _).comp hd
  exact he.congr' (Eventually.of_forall (fun m =>
    (dyadicStoppingIndex Q D T τ hτ hstop m).closedIntegral_stoppedDomain T m U t))

end PBGSO.FilteredBrownian
