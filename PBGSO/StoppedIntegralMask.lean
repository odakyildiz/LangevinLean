import PBGSO.StoppingSteps

/-! # Actual randomly stopped diffusion columns and completed integral -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- The same literal event restriction on all physical Brownian columns. -/
def columnEventMask (E : Set Ω) (hE : MeasurableSet E) :
    ColumnHilbert (I := I) (Z := Z) Q →L[ℝ] ColumnHilbert (I := I) (Z := Z) Q :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => Lp Z 2 Q)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (eventMask Q E hE).comp (columnEval Q i)))

@[simp] theorem columnEventMask_apply (E : Set Ω) (hE : MeasurableSet E)
    (U : ColumnHilbert (I := I) (Z := Z) Q) (i : I) :
    (columnEventMask Q E hE U).ofLp i = eventMask Q E hE (U.ofLp i) := rfl

theorem columnEventMask_congr (E F : Set Ω) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (h : E = F) : columnEventMask (I := I) (Z := Z) Q E hE = columnEventMask Q F hF := by
  subst F
  rfl

/-- Actual time interval and source event restriction, as a bounded operator. -/
def eventTimePiece (E : Set Ω) (hE : MeasurableSet E) (s t : ℝ)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) :=
  (columnEventMask Q E hE).compLpL 2 (volume : Measure ℝ) (timeCut Q U s t)

theorem eventTimePiece_coe (E : Set Ω) (hE : MeasurableSet E) (s t : ℝ)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    eventTimePiece Q E hE s t U =ᵐ[volume] fun r =>
      if r ∈ Ioc s t then columnEventMask Q E hE (U r) else 0 := by
  filter_upwards [(columnEventMask (I := I) (Z := Z) Q E hE).coeFn_compLpL (timeCut Q U s t),
    timeCut_coe Q U s t] with r hmap hcut
  rw [show eventTimePiece Q E hE s t U r = _ from hmap, hcut]
  by_cases hr : r ∈ Ioc s t <;> simp [Set.indicator, hr]

theorem eventTimePiece_continuous (E : Set Ω) (hE : MeasurableSet E) (s t : ℝ) :
    Continuous (eventTimePiece (I := I) (Z := Z) Q E hE s t) :=
  ((columnEventMask (I := I) (Z := Z) Q E hE).compLpL 2 (volume : Measure ℝ)).continuous.comp
    (timeCut_lipschitz (I := I) (Z := Z) Q s t).continuous

variable {Q D}

/-- The original diffusion is restricted on each stopping-grid cell by the
primitive event that the stopping time has not yet occurred. -/
def GridStoppingIndex.maskInput {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) :=
  ∑ j : Fin n, eventTimePiece Q (σ.active j)
    (D.filtration.le _ _ (σ.active_measurable j)) (τ j) (τ (j + 1)) U

theorem GridStoppingIndex.maskInput_continuous {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) :
    Continuous (σ.maskInput (Z := Z)) := by
  unfold GridStoppingIndex.maskInput
  apply continuous_finsetSum
  intro j _
  exact eventTimePiece_continuous Q _ _ _ _

theorem GridStoppingIndex.maskInput_coe {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    σ.maskInput U =ᵐ[volume] fun r => ∑ j : Fin n,
      if r ∈ Ioc (τ j : ℝ) (τ (j + 1)) then
        columnEventMask Q (σ.active j) (D.filtration.le _ _ (σ.active_measurable j)) (U r) else 0 := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j : Fin n =>
      eventTimePiece Q (σ.active j) (D.filtration.le _ _ (σ.active_measurable j))
        (τ j) (τ (j + 1)) U),
    ae_all_iff.mpr (fun j : Fin n => eventTimePiece_coe Q (σ.active j)
      (D.filtration.le _ _ (σ.active_measurable j)) (τ j) (τ (j + 1)) U)]
    with r hsum hpiece
  rw [GridStoppingIndex.maskInput, hsum]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => hpiece j)

theorem GridStoppingIndex.masked_toLp {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (A : Coefficients (Z := Z) Q D τ) (k : ℕ) :
    (σ.coefficients A k).toLp =
      columnEventMask Q (σ.active k) (D.filtration.le _ _ (σ.active_measurable k)) (A k).toLp := by
  apply PiLp.ext
  intro i
  rw [columnEventMask_apply]
  change ((σ.coefficients A k).square i).toLp _ = eventMask Q (σ.active k)
    (D.filtration.le _ _ (σ.active_measurable k)) (((A k).square i).toLp _)
  apply Lp.ext
  filter_upwards [((σ.coefficients A k).square i).coeFn_toLp,
    ((A k).square i).coeFn_toLp,
    eventMask_coe Q (σ.active k) (D.filtration.le _ _ (σ.active_measurable k))
      (((A k).square i).toLp _)] with ω hmask hA hE
  rw [hmask, hE]
  by_cases h : ω ∈ σ.active k <;> simp [GridStoppingIndex.coefficients, Set.indicator, h, hA]

/-- A cell's unique coarse stopping-grid index is determined from the
actual compatible fine mesh, including non-strict monotone grids. -/
theorem compatible_cell {τ υ : ℕ → ℝ≥0} (hυ : Monotone υ)
    (d : ℕ) (hd : 0 < d) (hgrid : ∀ k, υ (d * k) = τ k)
    (k : ℕ) (r : ℝ) (hr : r ∈ Ioc (υ k : ℝ) (υ (k + 1))) :
    r ∈ Ioc (τ (k / d) : ℝ) (τ (k / d + 1)) := by
  constructor
  · rw [← hgrid]
    exact lt_of_le_of_lt (by exact_mod_cast hυ (Nat.mul_div_le k d)) hr.1
  · rw [← hgrid]
    have hb : k < (k / d + 1) * d :=
      (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (k / d))
    have hb' : k + 1 ≤ d * (k / d + 1) := by
      simpa only [Nat.mul_comm] using Nat.succ_le_of_lt hb
    exact hr.2.trans (by exact_mod_cast hυ hb')

/-- The original finite predictable-step input, stopped on a compatible
coarse grid, is exactly the literal time/event mask of its original input. -/
theorem GridStoppingIndex.coefficientStep_mask {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (hτ : Monotone τ)
    (υ : ℕ → ℝ≥0) (hυ : Monotone υ) (d : ℕ) (hd : 0 < d)
    (hgrid : ∀ k, υ (d * k) = τ k) (m : ℕ) (hm : m = d * n)
    (A : Coefficients (Z := Z) Q D υ) :
    coefficientStep Q D υ ((σ.refine υ hυ d hd hgrid m hm).coefficients A) m =
      σ.maskInput (coefficientStep Q D υ A m) := by
  let σ' := σ.refine υ hυ d hd hgrid m hm
  apply Lp.ext
  filter_upwards [TimeGridContinuity.grid_coe υ (fun k => (σ'.coefficients A k).toLp) m,
    TimeGridContinuity.grid_coe υ (fun k => (A k).toLp) m,
    σ.maskInput_coe (coefficientStep Q D υ A m)] with r hstop hA hmask
  change (coefficientStep Q D υ (σ'.coefficients A) m) r = _
  change (coefficientStep Q D υ (σ'.coefficients A) m) r = _ at hstop
  change (coefficientStep Q D υ A m) r = _ at hA
  rw [hstop, hmask]
  by_cases hr : r ∈ Ioc (υ 0 : ℝ) (υ m)
  · obtain ⟨k, hk⟩ := TimeGridContinuity.exists_interval υ hυ m r hr
    rw [TimeGridContinuity.rawGrid_eq υ hυ _ m k r hk]
    rw [TimeGridContinuity.rawGrid_eq υ hυ _ m k r hk] at hA
    have hj : k.val / d < n := by
      apply (Nat.div_lt_iff_lt_mul hd).mpr
      have hkbound : k.val < d * n := by rw [← hm]; exact k.isLt
      simpa only [Nat.mul_comm] using hkbound
    let j : Fin n := ⟨k / d, hj⟩
    have hcell : r ∈ Ioc (τ j : ℝ) (τ (j + 1)) := compatible_cell hυ d hd hgrid k r hk
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left hcell, hA]
      rw [σ'.masked_toLp A k]
      have he : σ'.active k = σ.active j := by
        ext ω
        change k.val < d * σ.index ω ↔ k.val / d < σ.index ω
        simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hd).symm
      exact congrArg (fun C : ColumnHilbert (I := I) (Z := Z) Q →L[ℝ]
        ColumnHilbert (I := I) (Z := Z) Q => C (A k).toLp)
        (columnEventMask_congr Q _ _ _ _ he)

    · intro l _ hlj
      apply ite_eq_right
      intro hl
      exact hlj (Fin.ext (TimeGridContinuity.interval_unique τ hτ l j r hl hcell))
    · simp
  · rw [TimeGridContinuity.rawGrid_zero_outside υ hυ _ m r hr]
    rw [TimeGridContinuity.rawGrid_zero_outside υ hυ _ m r hr] at hA
    simp [hA]

/-- Both the literal stopped diffusion columns and the stopped Brownian
noise are approximated by the same actual finite predictable sums. -/
theorem GridStoppingIndex.stoppedMask_approximations (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    ∃ A : ℕ → FiniteStepData (Z := Z) Q D (dyadicGrids T),
      Tendsto (fun k => finiteStepInput Q D (dyadicGrids T) (A k)) atTop
        (𝓝 (σ.maskInput U.val)) ∧
      ∀ t, Tendsto (fun k => stoppedIntegralLp Q D ((dyadicGrids T).time (A k).1)
        ((dyadicGrids T).monotone (A k).1) (A k).2 ((dyadicGrids T).count (A k).1) t)
        atTop (𝓝 (σ.stoppedIntegral T m U t)) := by
  let G := dyadicGrids T
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G U
  choose B hB hBout using fun k =>
    finiteStep_refine_exists Q D G (A k) (max m (A k).1) (le_max_right _ _)
  let C : ℕ → FiniteStepData (Z := Z) Q D G := fun k => ⟨max m (A k).1, B k⟩
  have hC : Tendsto (fun k => finiteStepInput Q D G (C k)) atTop (𝓝 U.val) := by
    convert hA using 1
    funext k
    exact hB k
  choose d hd hcount hgrid using fun k => G.compatible m (C k).1 (le_max_left _ _)
  let σ' k : GridStoppingIndex Q D (G.time (C k).1) (G.count (C k).1) :=
    σ.refine (G.time (C k).1) (G.monotone (C k).1) (d k) (hd k) (hgrid k)
      (G.count (C k).1) (hcount k)
  let V : ℕ → FiniteStepData (Z := Z) Q D G :=
    fun k => ⟨(C k).1, (σ' k).coefficients (C k).2⟩
  have hinput (k : ℕ) : finiteStepInput Q D G (V k) =
      σ.maskInput (finiteStepInput Q D G (C k)) :=
    σ.coefficientStep_mask (G.monotone m) (G.time (C k).1) (G.monotone (C k).1)
      (d k) (hd k) (hgrid k) (G.count (C k).1) (hcount k) (C k).2
  refine ⟨V, ?_, ?_⟩
  · have hl := (σ.maskInput_continuous.continuousAt.tendsto).comp hC
    exact hl.congr' (Eventually.of_forall (fun k => (hinput k).symm))
  · intro t
    have hl := σ.select_tendsto
      (fun k j => stoppedIntegralLp Q D (G.time (C k).1) (G.monotone (C k).1)
        (C k).2 (G.count (C k).1) (min t (G.time m j)))
      (fun j => closedIntegral Q D T U (min t (G.time m j)))
      (fun j => closedIntegral_stopped_tendsto Q D T U C hC (min t (G.time m j)))
    convert hl using 1
    · funext k
      apply Lp.ext
      filter_upwards [(stoppedGridSum_memLp Q D (G.time (V k).1) (G.monotone (V k).1)
          (V k).2 (G.count (V k).1) t).coeFn_toLp,
        σ.select_coe (fun j => stoppedIntegralLp Q D (G.time (C k).1) (G.monotone (C k).1)
          (C k).2 (G.count (C k).1) (min t (G.time m j))),
        ae_all_iff.mpr (fun j : Fin (G.count m + 1) =>
          (stoppedGridSum_memLp Q D (G.time (C k).1) (G.monotone (C k).1)
            (C k).2 (G.count (C k).1) (min t (G.time m j))).coeFn_toLp)]
        with ω hV hselect hj
      change (stoppedIntegralLp Q D (G.time (V k).1) (G.monotone (V k).1)
        (V k).2 (G.count (V k).1) t) ω = _
      simp only [stoppedIntegralLp] at hselect ⊢
      rw [hV, hselect, hj (σ.finIndex ω)]
      change FilteredBrownian.stoppedGridSum Q D (G.time (C k).1)
        ((σ' k).coefficients (C k).2) (G.count (C k).1) t ω = _
      rw [(σ' k).stoppedGridSum (G.monotone (C k).1)]
      dsimp only [σ', GridStoppingIndex.refine]
      rw [hgrid k]
      rfl
    · rfl

/-- The actual randomly restricted diffusion belongs to the stochastic
integration domain, with membership derived from genuine finite sums. -/
theorem GridStoppingIndex.maskInput_mem_closed (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    σ.maskInput U.val ∈ closure (Set.range (finiteStepInput (Z := Z) Q D (dyadicGrids T))) := by
  obtain ⟨A, hA, _⟩ := σ.stoppedMask_approximations T m U
  apply isClosed_closure.mem_of_tendsto hA
  exact Eventually.of_forall (fun k => subset_closure (Set.mem_range_self (A k)))

/-- Actual domain entry for the original randomly stopped diffusion. -/
def GridStoppingIndex.stoppedDomain (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    ClosedStepDomain (Z := Z) Q D (dyadicGrids T) :=
  ⟨σ.maskInput U.val, σ.maskInput_mem_closed T m U⟩

/-- Exact stochastic stopping identity: the completed integral of the
original stopped diffusion is the original integral at its random grid stop. -/
theorem GridStoppingIndex.closedIntegral_stoppedDomain (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    closedIntegral Q D T (σ.stoppedDomain T m U) t = σ.stoppedIntegral T m U t := by
  obtain ⟨A, hA, hnoise⟩ := σ.stoppedMask_approximations T m U
  exact tendsto_nhds_unique (closedIntegral_stopped_tendsto Q D T (σ.stoppedDomain T m U) A hA t)
    (hnoise t)

/-- Exact stopped isometry from original diffusion columns restricted by
its actual stopping events. The integral and its stopped law are derived. -/
theorem GridStoppingIndex.stoppedIntegral_isometry (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ) (t : ℝ≥0) :
    QuadraticMartingale.weightedPairing Q W (σ.stoppedIntegral T m U t)
      (σ.stoppedIntegral T m U t) =
      ∫ r in Ioc (0 : ℝ) t, ∑ i,
        QuadraticMartingale.weightedPairing Q W ((σ.maskInput U.val r).ofLp i)
          ((σ.maskInput U.val r).ofLp i) := by
  have he := closedIntegral_increment_isometry Q D T (σ.stoppedDomain T m U) W hW 0 t (by simp)
  rw [closedIntegral_zero, sub_zero, σ.closedIntegral_stoppedDomain T m U t] at he
  exact he

/-- The literal stopped columns are the original columns times the actual
random stopping-time indicator, almost everywhere in time and probability.
This identifies the mask operator with the source's physical diffusion. -/
theorem GridStoppingIndex.maskInput_raw {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (hτ : Monotone τ)
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) :
    ∀ᵐ r ∂(volume : Measure ℝ), ∀ i,
      (σ.maskInput U r).ofLp i =ᵐ[Q] fun ω =>
        if r ∈ Ioc (τ 0 : ℝ) (τ n) ∧ r ≤ (τ (σ.index ω) : ℝ)
          then (U r).ofLp i ω else 0 := by
  filter_upwards [σ.maskInput_coe U] with r hmask
  intro i
  by_cases hr : r ∈ Ioc (τ 0 : ℝ) (τ n)
  · obtain ⟨j, hj⟩ := TimeGridContinuity.exists_interval τ hτ n r hr
    have heq : σ.maskInput U r = columnEventMask Q (σ.active j)
        (D.filtration.le _ _ (σ.active_measurable j)) (U r) := by
      rw [hmask, Finset.sum_eq_single j]
      · exact ite_eq_left hj
      · intro k _ hkj
        apply ite_eq_right
        intro hk
        exact hkj (Fin.ext (TimeGridContinuity.interval_unique τ hτ k j r hk hj))
      · simp
    rw [heq, columnEventMask_apply]
    filter_upwards [eventMask_coe Q (σ.active j)
      (D.filtration.le _ _ (σ.active_measurable j)) ((U r).ofLp i)] with ω hω
    rw [hω]
    by_cases hstop : (j : ℕ) < σ.index ω
    · have hle : r ≤ (τ (σ.index ω) : ℝ) :=
        hj.2.trans (by exact_mod_cast hτ (Nat.succ_le_of_lt hstop))
      simp [Set.indicator, GridStoppingIndex.active, hstop, hr, hle]
    · have hlt : (τ (σ.index ω) : ℝ) < r :=
        lt_of_le_of_lt (by exact_mod_cast hτ (Nat.le_of_not_gt hstop)) hj.1
      simp [Set.indicator, GridStoppingIndex.active, hstop, hr, not_le_of_gt hlt]
  · have heq : σ.maskInput U r = 0 := by
      rw [hmask]
      apply Finset.sum_eq_zero
      intro j _
      apply ite_eq_right
      intro hj
      apply hr
      exact ⟨lt_of_le_of_lt (by exact_mod_cast hτ (Nat.zero_le j)) hj.1,
        hj.2.trans (by exact_mod_cast hτ (Nat.succ_le_of_lt j.isLt))⟩
    rw [heq]
    filter_upwards [Lp.coeFn_zero Z 2 Q] with ω hω
    simpa only [hr, false_and, ite_false, PiLp.zero_apply, Pi.zero_apply] using hω

end PBGSO.FilteredBrownian
