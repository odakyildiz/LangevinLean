import PBGSO.PredictableCurveIntegral
import Mathlib.Probability.Martingale.OptionalSampling

/-! # Actual finite predictable Brownian sums stopped on a finite grid -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Literal event restriction in the actual L² space. -/
def eventMaskValue (E : Set Ω) (hE : MeasurableSet E) (U : Lp Z 2 Q) : Lp Z 2 Q :=
  ((Lp.memLp U).indicator hE).toLp (E.indicator U)

theorem eventMaskValue_coe (E : Set Ω) (hE : MeasurableSet E) (U : Lp Z 2 Q) :
    eventMaskValue Q E hE U =ᵐ[Q] E.indicator U :=
  ((Lp.memLp U).indicator hE).coeFn_toLp

theorem eventMaskValue_norm (E : Set Ω) (hE : MeasurableSet E) (U : Lp Z 2 Q) :
    ‖eventMaskValue Q E hE U‖ ≤ ‖U‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [eventMaskValue_coe Q E hE U] with ω hω
  rw [hω]
  by_cases h : ω ∈ E
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- Event restriction is a bounded linear map; this lets actual stochastic
limits pass through finite stopping choices without new limit assumptions. -/
def eventMask (E : Set Ω) (hE : MeasurableSet E) : Lp Z 2 Q →L[ℝ] Lp Z 2 Q :=
  LinearMap.mkContinuous
    { toFun := eventMaskValue Q E hE
      map_add' := by
        intro U V
        apply Lp.ext
        filter_upwards [eventMaskValue_coe Q E hE (U + V),
          eventMaskValue_coe Q E hE U, eventMaskValue_coe Q E hE V,
          Lp.coeFn_add U V,
          Lp.coeFn_add (eventMaskValue Q E hE U) (eventMaskValue Q E hE V)]
          with ω huv hu hv hsum hsum'
        simp only [Pi.add_apply] at hsum hsum'
        rw [hsum', huv, hu, hv]
        by_cases h : ω ∈ E
        · simpa only [Set.indicator_of_mem h] using hsum
        · simp only [Set.indicator_of_notMem h, add_zero]
      map_smul' := by
        intro c U
        apply Lp.ext
        filter_upwards [eventMaskValue_coe Q E hE (c • U),
          eventMaskValue_coe Q E hE U, Lp.coeFn_smul c U,
          Lp.coeFn_smul c (eventMaskValue Q E hE U)] with ω hc hu hsm hsm'
        simp only [RingHom.id_apply]
        simp only [Pi.smul_apply] at hsm hsm'
        rw [hsm', hc, hu]
        by_cases h : ω ∈ E <;> simp [Set.indicator, h, hsm] }
    1 (fun U => by simpa using eventMaskValue_norm Q E hE U)

@[simp] theorem eventMask_coe (E : Set Ω) (hE : MeasurableSet E) (U : Lp Z 2 Q) :
    eventMask Q E hE U =ᵐ[Q] E.indicator U := eventMaskValue_coe Q E hE U

/-- A stopping index on a deterministic grid is specified by its primitive
stopping events, not by any stopped-integral conclusion. -/
structure GridStoppingIndex (τ : ℕ → ℝ≥0) (n : ℕ) where
  index : Ω → ℕ
  bound : ∀ ω, index ω ≤ n
  stopping : ∀ k, MeasurableSet[D.filtration (τ k)] {ω | index ω ≤ k}

variable {Q D}

def GridStoppingIndex.active {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (k : ℕ) : Set Ω := {ω | k < σ.index ω}

theorem GridStoppingIndex.active_measurable {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (k : ℕ) :
    MeasurableSet[D.filtration (τ k)] (σ.active k) := by
  convert (σ.stopping k).compl using 1
  ext ω
  simp [GridStoppingIndex.active]

/-- The stopped finite integrand uses the original coefficient before the
actual stopping index and zero afterwards. Adaptation is proved from the
original stopping events. -/
def GridStoppingIndex.coefficients {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (A : Coefficients (Z := Z) Q D τ) :
    Coefficients (Z := Z) Q D τ := fun k =>
  { value := fun i => (σ.active k).indicator ((A k).value i)
    adapted := fun i => ((A k).adapted i).indicator (σ.active_measurable k)
    square := fun i => ((A k).square i).indicator
      (D.filtration.le _ _ (σ.active_measurable k)) }

theorem sum_prefix {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n m : ℕ) (hm : m ≤ n) :
    (∑ k : Fin n, if (k : ℕ) < m then f k else 0) = ∑ k : Fin m, f k := by
  induction n generalizing m with
  | zero => have : m = 0 := by omega
            subst m
            simp
  | succ n ih =>
    by_cases hmn : m ≤ n
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, ite_eq_right (by omega : ¬ n < m), add_zero]
      exact ih m hmn
    · have hme : m = n + 1 := by omega
      subst m
      exact Finset.sum_congr rfl fun k _ => ite_eq_left k.isLt

theorem GridStoppingIndex.noiseStep_stopped {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (A : Coefficients (Z := Z) Q D τ) (k : ℕ) (ω : Ω) :
    noiseStep Q D (τ k) (τ (k + 1)) (σ.coefficients A k) ω =
      if k < σ.index ω then noiseStep Q D (τ k) (τ (k + 1)) (A k) ω else 0 := by
  by_cases h : k < σ.index ω
  · simp [FilteredBrownian.noiseStep, PredictableIsometry.stepSum, GridStoppingIndex.coefficients,
      GridStoppingIndex.active, Set.indicator, h]
  · simp [FilteredBrownian.noiseStep, PredictableIsometry.stepSum, GridStoppingIndex.coefficients,
      GridStoppingIndex.active, Set.indicator, h]

/-- Exact pathwise stopping identity for the actual finite predictable
Brownian sums, before taking any stochastic completion. -/
theorem GridStoppingIndex.gridSum_stopped {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (A : Coefficients (Z := Z) Q D τ) (ω : Ω) :
    gridSum Q D τ (σ.coefficients A) n ω = gridSum Q D τ A (σ.index ω) ω := by
  simp only [FilteredBrownian.gridSum, σ.noiseStep_stopped A]
  exact sum_prefix (fun k : ℕ => FilteredBrownian.noiseStep Q D (τ k) (τ (k + 1)) (A k) ω)
    n (σ.index ω) (σ.bound ω)

/-- The stopped finite integral's weighted variance is computed from the
actual original diffusion columns, restricted by its stopping events. -/
theorem GridStoppingIndex.stopped_isometry {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ) :
    (∫ ω, ⟪gridSum Q D τ A (σ.index ω) ω,
      W (gridSum Q D τ A (σ.index ω) ω)⟫_ℝ ∂Q) =
      ∑ k : Fin n, ((τ (k + 1) : ℝ) - τ k) * ∑ i,
        ∫ ω in σ.active k, ⟪(A k).value i ω, W ((A k).value i ω)⟫_ℝ ∂Q := by
  have he := gridSum_isometry Q D W hW τ hτ (σ.coefficients A) n
  simp_rw [σ.gridSum_stopped A] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_indicator (D.filtration.le _ _ (σ.active_measurable k))]
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  by_cases h : ω ∈ σ.active k <;>
    simp [GridStoppingIndex.coefficients, Set.indicator, h]

/-- The finite stopping index is actually measurable in the ambient source. -/
theorem GridStoppingIndex.index_measurable {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) : Measurable σ.index := by
  apply measurable_of_Iic
  intro k
  exact D.filtration.le _ _ (σ.stopping k)

/-- Stopping the original finite Brownian process at the random grid knot
is exactly the process formed from its actual masked coefficients. -/
theorem GridStoppingIndex.stoppedStep {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (k : ℕ) (t : ℝ≥0) (ω : Ω) :
    FilteredBrownian.stoppedStep Q D (τ k) (τ (k + 1)) (σ.coefficients A k) t ω =
      FilteredBrownian.stoppedStep Q D (τ k) (τ (k + 1)) (A k)
        (min t (τ (σ.index ω))) ω := by
  rw [stoppedStep_clamp Q D _ _ t (hτ (Nat.le_succ k)),
    stoppedStep_clamp Q D _ _ (min t (τ (σ.index ω))) (hτ (Nat.le_succ k))]
  by_cases hk : k < σ.index ω
  · have ha := hτ (Nat.le_of_lt hk)
    have hb := hτ (Nat.succ_le_of_lt hk)
    simp [GridStoppingIndex.coefficients, GridStoppingIndex.active, Set.indicator, hk,
      min_assoc, min_eq_right ha, min_eq_right hb]
  · have ha := hτ (Nat.le_of_not_gt hk)
    have hb := ha.trans (hτ (Nat.le_succ k))
    simp [GridStoppingIndex.coefficients, GridStoppingIndex.active, Set.indicator, hk,
      min_assoc, min_eq_left ha, min_eq_left hb]

theorem GridStoppingIndex.stoppedGridSum {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (t : ℝ≥0) (ω : Ω) :
    FilteredBrownian.stoppedGridSum Q D τ (σ.coefficients A) n t ω =
      FilteredBrownian.stoppedGridSum Q D τ A n (min t (τ (σ.index ω))) ω := by
  simp only [FilteredBrownian.stoppedGridSum, σ.stoppedStep hτ A]

/-- The actual finite-grid stopped Brownian sum is a martingale in real
continuous observation time. No optional-stopping hypothesis is supplied. -/
theorem GridStoppingIndex.stoppedGridSum_martingale {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) :
    Martingale (fun t ω => FilteredBrownian.stoppedGridSum Q D τ A n
      (min t (τ (σ.index ω))) ω) D.filtration Q := by
  have he : (fun t ω => FilteredBrownian.stoppedGridSum Q D τ A n
      (min t (τ (σ.index ω))) ω) =
      FilteredBrownian.stoppedGridSum Q D τ (σ.coefficients A) n := by
    funext t ω
    exact (σ.stoppedGridSum hτ A t ω).symm
  rw [he]
  exact FilteredBrownian.stoppedGridSum_martingale Q D τ hτ (σ.coefficients A) n

/-- The bounded natural stopping index is represented by its actual finite type. -/
def GridStoppingIndex.finIndex {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (ω : Ω) : Fin (n + 1) :=
  ⟨σ.index ω, Nat.lt_succ_of_le (σ.bound ω)⟩

theorem GridStoppingIndex.fiber_measurable {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (j : Fin (n + 1)) :
    MeasurableSet {ω | σ.index ω = j} :=
  σ.index_measurable (measurableSet_singleton (j : ℕ))

/-- Actual L² selection at a finite stopping index. Its bounded linear
pieces preserve stochastic limits without an assumed stopped-limit law. -/
def GridStoppingIndex.select {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (U : Fin (n + 1) → Lp Z 2 Q) : Lp Z 2 Q :=
  ∑ j : Fin (n + 1), eventMask Q {ω | σ.index ω = (j : ℕ)} (σ.fiber_measurable j) (U j)

theorem GridStoppingIndex.select_coe {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (U : Fin (n + 1) → Lp Z 2 Q) :
    σ.select U =ᵐ[Q] fun ω => U (σ.finIndex ω) ω := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun j : Fin (n + 1) => eventMask Q {ω | σ.index ω = (j : ℕ)} (σ.fiber_measurable j) (U j)),
    ae_all_iff.mpr (fun j : Fin (n + 1) => eventMask_coe Q {ω | σ.index ω = (j : ℕ)} (σ.fiber_measurable j) (U j))]
    with ω hsum hmask
  change (σ.select U) ω = _
  rw [GridStoppingIndex.select, hsum]
  simp only [Finset.sum_apply]
  simp_rw [hmask]
  rw [Finset.sum_eq_single (σ.finIndex ω)]
  · simp [Set.indicator, GridStoppingIndex.finIndex]
  · intro j _ hj
    apply Set.indicator_of_notMem
    intro he
    exact hj (Fin.ext he.symm)
  · simp

theorem GridStoppingIndex.select_tendsto {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (U : ℕ → Fin (n + 1) → Lp Z 2 Q)
    (V : Fin (n + 1) → Lp Z 2 Q)
    (hU : ∀ j, Tendsto (fun k => U k j) atTop (𝓝 (V j))) :
    Tendsto (fun k => σ.select (U k)) atTop (𝓝 (σ.select V)) := by
  unfold GridStoppingIndex.select
  apply tendsto_finsetSum
  intro j _
  exact ((eventMask Q {ω | σ.index ω = j} (σ.fiber_measurable j)).continuous.tendsto _).comp (hU j)

theorem GridStoppingIndex.select_memLp {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (f : Fin (n + 1) → Ω → Z)
    (hf : ∀ j, MemLp (f j) 2 Q) :
    MemLp (fun ω => f (σ.finIndex ω) ω) 2 Q := by
  apply (Lp.memLp (σ.select (fun j => (hf j).toLp (f j)))).ae_eq
  filter_upwards [σ.select_coe (fun j => (hf j).toLp (f j)),
    ae_all_iff.mpr (fun j => (hf j).coeFn_toLp)] with ω hselect hj
  exact hselect.trans (hj (σ.finIndex ω))

theorem GridStoppingIndex.select_toLp {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (f : Fin (n + 1) → Ω → Z)
    (hf : ∀ j, MemLp (f j) 2 Q) :
    (σ.select_memLp f hf).toLp (fun ω => f (σ.finIndex ω) ω) =
      σ.select (fun j => (hf j).toLp (f j)) := by
  apply Lp.ext
  filter_upwards [(σ.select_memLp f hf).coeFn_toLp,
    σ.select_coe (fun j => (hf j).toLp (f j)),
    ae_all_iff.mpr (fun j => (hf j).coeFn_toLp)] with ω hfun hselect hj
  rw [hfun, hselect, hj (σ.finIndex ω)]

/-- A genuine stopping index transfers to every compatible finer grid.
The new stopping events are proved measurable at their actual fine knots. -/
def GridStoppingIndex.refine {τ : ℕ → ℝ≥0} {n : ℕ}
    (σ : GridStoppingIndex Q D τ n) (υ : ℕ → ℝ≥0) (hυ : Monotone υ)
    (d : ℕ) (hd : 0 < d) (hgrid : ∀ k, υ (d * k) = τ k)
    (m : ℕ) (hm : m = d * n) : GridStoppingIndex Q D υ m where
  index ω := d * σ.index ω
  bound ω := by rw [hm]; exact Nat.mul_le_mul_left d (σ.bound ω)
  stopping k := by
    have htime : τ (k / d) ≤ υ k := by
      rw [← hgrid]
      exact hυ (Nat.mul_div_le k d)
    have he : {ω | d * σ.index ω ≤ k} = {ω | σ.index ω ≤ k / d} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Nat.le_div_iff_mul_le hd, Nat.mul_comm]
    rw [he]
    exact D.filtration.mono htime _ (σ.stopping (k / d))

/-- The actual finite choice of the completed integral at a random grid stop. -/
def GridStoppingIndex.stoppedIntegral (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) : Lp Z 2 Q :=
  σ.select (fun j => closedIntegral Q D T U (min t ((dyadicGrids T).time m j)))

/-- Actual finite Brownian processes give the stopped completed integral's
martingale approximations. Both the refinements and stochastic limits are
derived from the literal closure domain. -/
theorem GridStoppingIndex.stoppedIntegral_approximations (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    ∃ F : ℕ → ℝ≥0 → Ω → Z, (∀ k, Martingale (F k) D.filtration Q) ∧
      ∃ hF : ∀ k t, MemLp (F k t) 2 Q,
        ∀ t, Tendsto (fun k => (hF k t).toLp (F k t)) atTop
          (𝓝 (σ.stoppedIntegral T m U t)) := by
  let G := dyadicGrids T
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G U
  choose B hB hBout using fun k =>
    finiteStep_refine_exists Q D G (A k) (max m (A k).1) (le_max_right _ _)
  let C : ℕ → FiniteStepData (Z := Z) Q D G :=
    fun k => ⟨max m (A k).1, B k⟩
  have hC : Tendsto (fun k => finiteStepInput Q D G (C k)) atTop (𝓝 U.val) := by
    convert hA using 1
    funext k
    exact hB k
  choose d hd hcount hgrid using fun k => G.compatible m (C k).1 (le_max_left _ _)
  let σ' k : GridStoppingIndex Q D (G.time (C k).1) (G.count (C k).1) :=
    σ.refine (G.time (C k).1) (G.monotone (C k).1) (d k) (hd k) (hgrid k)
      (G.count (C k).1) (hcount k)
  let F : ℕ → ℝ≥0 → Ω → Z := fun k t ω =>
    FilteredBrownian.stoppedGridSum Q D (G.time (C k).1) (C k).2 (G.count (C k).1)
      (min t (G.time m (σ.index ω))) ω
  have hFM : ∀ k, Martingale (F k) D.filtration Q := by
    intro k
    have he : F k = (fun t ω => FilteredBrownian.stoppedGridSum Q D (G.time (C k).1) (C k).2
        (G.count (C k).1) (min t (G.time (C k).1 ((σ' k).index ω))) ω) := by
      funext t ω
      dsimp only [F, σ', GridStoppingIndex.refine]
      rw [hgrid k]
    rw [he]
    exact (σ' k).stoppedGridSum_martingale (G.monotone (C k).1) (C k).2
  have hFM2 : ∀ k t, MemLp (F k t) 2 Q := by
    intro k t
    exact σ.select_memLp (fun j => FilteredBrownian.stoppedGridSum Q D (G.time (C k).1) (C k).2
      (G.count (C k).1) (min t (G.time m j)))
      (fun j => stoppedGridSum_memLp Q D _ (G.monotone (C k).1) _ _ _)
  refine ⟨F, hFM, hFM2, ?_⟩
  intro t
  have hl := σ.select_tendsto
    (fun k j => stoppedIntegralLp Q D (G.time (C k).1) (G.monotone (C k).1)
      (C k).2 (G.count (C k).1) (min t (G.time m j)))
    (fun j => closedIntegral Q D T U (min t (G.time m j)))
    (fun j => closedIntegral_stopped_tendsto Q D T U C hC (min t (G.time m j)))
  convert hl using 1
  funext k
  exact σ.select_toLp
    (fun j => FilteredBrownian.stoppedGridSum Q D (G.time (C k).1) (C k).2
      (G.count (C k).1) (min t (G.time m j)))
    (fun j => stoppedGridSum_memLp Q D _ (G.monotone (C k).1) _ _ _)
  rfl

/-- The finite-grid stopped completed Brownian integral is an actual
martingale. No optional-stopping identity is assumed. -/
theorem GridStoppingIndex.stoppedIntegral_martingale (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) :
    Martingale (MartingaleL2Limit.representative Q D.filtration (σ.stoppedIntegral T m U))
      D.filtration Q := by
  obtain ⟨F, hF, h2, hlim⟩ := σ.stoppedIntegral_approximations T m U
  exact MartingaleL2Limit.martingale_representative Q D.filtration F hF h2 _ hlim

theorem GridStoppingIndex.stoppedIntegral_representative_ae (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    MartingaleL2Limit.representative Q D.filtration (σ.stoppedIntegral T m U) t =ᵐ[Q]
      σ.stoppedIntegral T m U t := by
  obtain ⟨F, hF, h2, hlim⟩ := σ.stoppedIntegral_approximations T m U
  exact MartingaleL2Limit.representative_ae Q D.filtration F hF h2 _ hlim t

/-- The actual stopped L² class is literally the original computed noise
at the random grid time, up to the proved finite union of null sets. -/
theorem GridStoppingIndex.stoppedIntegral_coe (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    σ.stoppedIntegral T m U t =ᵐ[Q] fun ω =>
      MartingaleL2Limit.representative Q D.filtration (closedIntegral Q D T U)
        (min t ((dyadicGrids T).time m (σ.index ω))) ω := by
  filter_upwards [σ.select_coe (fun j => closedIntegral Q D T U
      (min t ((dyadicGrids T).time m j))),
    ae_all_iff.mpr (fun j : Fin ((dyadicGrids T).count m + 1) =>
      closedIntegral_representative_ae Q D T U (min t ((dyadicGrids T).time m j)))]
    with ω hselect hj
  exact hselect.trans (hj (σ.finIndex ω)).symm

/-- An actual adapted martingale representative of the stopped completed
integral agrees with the original computed process at its actual random time. -/
theorem GridStoppingIndex.stoppedIntegral_realizes (T : ℝ≥0) (m : ℕ)
    (σ : GridStoppingIndex Q D ((dyadicGrids T).time m) ((dyadicGrids T).count m))
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    MartingaleL2Limit.representative Q D.filtration (σ.stoppedIntegral T m U) t =ᵐ[Q]
      fun ω => MartingaleL2Limit.representative Q D.filtration (closedIntegral Q D T U)
        (min t ((dyadicGrids T).time m (σ.index ω))) ω :=
  (σ.stoppedIntegral_representative_ae T m U t).trans (σ.stoppedIntegral_coe T m U t)

end PBGSO.FilteredBrownian
