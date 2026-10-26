import PBGSO.ContinuousMartingaleCompletion
import PBGSO.ClosedIntegralEnergy
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Simultaneously continuous versions of the computed Brownian integral
The actual coordinate-continuity premise is Brownian path regularity, not a
continuity or modification conclusion for the integral being constructed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
open ContinuousMartingaleCompletion
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- A finite-window version of the actual computed integral. Its paths are
simultaneously continuous and each literal time variable is actually adapted. -/
structure ContinuousWindowVersion (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) where
  process : Window T → Ω → Z
  continuous_paths : ∀ᵐ ω ∂Q, Continuous (fun t => process t ω)
  adapted : ∀ t, StronglyMeasurable[D.filtration t.val] (process t)
  realizes : ∀ t, process t =ᵐ[Q] closedIntegral Q D T U t.val

/-- Actual stopped finite martingales have a continuous uniform subsequential
limit, which is proved to be a modification of the constructed integral. -/
theorem exists_continuousWindowVersion (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (hB : ∀ᵐ ω ∂Q, ∀ i, Continuous (fun t => D.process i t ω)) :
    Nonempty (ContinuousWindowVersion Q D T U) := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D (dyadicGrids T) U
  let f (n : ℕ) := stoppedGridSum Q D ((dyadicGrids T).time (A n).1) (A n).2
    ((dyadicGrids T).count (A n).1)
  have hf (n : ℕ) : Martingale (f n) D.filtration Q :=
    stoppedGridSum_martingale Q D _ ((dyadicGrids T).monotone (A n).1) _ _
  have h2 (n : ℕ) (t : ℝ≥0) : MemLp (f n t) 2 Q :=
    stoppedGridSum_memLp Q D _ ((dyadicGrids T).monotone (A n).1) _ _ t
  have hlim (t : ℝ≥0) : Tendsto (fun n => (h2 n t).toLp (f n t)) atTop
      (𝓝 (closedIntegral Q D T U t)) := closedIntegral_stopped_tendsto Q D T U A hA t
  have hc : ∀ᵐ ω ∂Q, ∀ n, Continuous (fun t => f n t ω) := by
    apply ae_all_iff.mpr
    intro n
    exact stoppedGridSum_continuous_paths Q D _ ((dyadicGrids T).monotone (A n).1) _ _ hB
  obtain ⟨φ, hφ, hφlim⟩ := exists_uniform_subsequence Q D.filtration f hf h2 T (hlim T).cauchySeq hc
  let M : Window T → Ω → Z :=
    fun t ω => MartingaleUniformLimit.seriesLimit (fun n (t : Window T) => f (φ n) t.val) t ω
  have hM (t : Window T) : M t =ᵐ[Q] closedIntegral Q D T U t.val := by
    have hpoint : ∀ᵐ ω ∂Q, Tendsto (fun n => f (φ n) t.val ω) atTop (𝓝 (M t ω)) :=
      hφlim.mono (fun ω hω => hω.1.tendsto_at t)
    have hprob := tendstoInMeasure_of_tendsto_ae (fun n => (h2 (φ n) t.val).aestronglyMeasurable) hpoint
    have hLp := tendstoInMeasure_of_tendsto_Lp ((hlim t.val).comp hφ.tendsto_atTop)
    have hraw := TendstoInMeasure.congr_left (fun n => (h2 (φ n) t.val).coeFn_toLp) hLp
    exact tendstoInMeasure_ae_unique hprob hraw
  refine ⟨⟨M, hφlim.mono (fun _ hω => hω.2), ?_, hM⟩⟩
  intro t
  letI : MeasurableSpace Ω := D.filtration t.val
  exact (StronglyMeasurable.tsum (fun n =>
    ((hf (φ (n + 1))).stronglyAdapted t.val).sub ((hf (φ n)).stronglyAdapted t.val))).add
      ((hf (φ 0)).stronglyAdapted t.val)

/-- The original filtration sampled at literal finite-window times. -/
def windowFiltration (T : ℝ≥0) : Filtration (Window T) mΩ where
  seq t := D.filtration t.val
  mono' _ _ h := D.filtration.mono h
  le' t := D.filtration.le t.val

theorem ContinuousWindowVersion.memLp (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (V : ContinuousWindowVersion Q D T U) (t : Window T) : MemLp (V.process t) 2 Q :=
  (memLp_congr_ae (V.realizes t)).mpr (Lp.memLp _)

/-- The constructed continuous version is a genuine martingale in the
actual sampled filtration, without completing or changing that filtration. -/
theorem ContinuousWindowVersion.martingale (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (V : ContinuousWindowVersion Q D T U) :
    Martingale V.process (windowFiltration Q D T) Q := by
  refine ⟨V.adapted, ?_⟩
  intro s t hst
  have ht := (V.realizes t).trans (closedIntegral_representative_ae Q D T U t.val).symm
  have hs := (V.realizes s).trans (closedIntegral_representative_ae Q D T U s.val).symm
  exact (condExp_congr_ae ht).trans
    (((closedIntegral_martingale Q D T U).condExp_ae_eq hst).trans hs.symm)

/-- Literal L² values of the simultaneous version are the computed integral. -/
theorem ContinuousWindowVersion.toLp_eq (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (V : ContinuousWindowVersion Q D T U) (t : Window T) :
    (ContinuousWindowVersion.memLp Q D T U V t).toLp (V.process t) = closedIntegral Q D T U t.val := by
  apply Lp.ext
  exact (ContinuousWindowVersion.memLp Q D T U V t).coeFn_toLp.trans (V.realizes t)

/-- A single null-set correction gives an actual joint realization with
continuous paths everywhere, while preserving the entire original path on
one full-measure event. No joint measurability is assumed. -/
theorem ContinuousWindowVersion.exists_joint_realization (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (V : ContinuousWindowVersion Q D T U) :
    ∃ g : Window T → Ω → Z, StronglyMeasurable (Function.uncurry g) ∧
      (∀ ω, Continuous (fun t => g t ω)) ∧
      ∀ᵐ ω ∂Q, ∀ t, g t ω = V.process t ω := by
  classical
  obtain ⟨B, hsub, hBm, hB0⟩ := exists_measurable_superset_of_null (ae_iff.mp V.continuous_paths)
  let g : Window T → Ω → Z := fun t ω => if ω ∈ B then 0 else V.process t ω
  have hc (ω : Ω) : Continuous (fun t => g t ω) := by
    by_cases hω : ω ∈ B
    · simpa only [g, hω, ite_true] using (continuous_const : Continuous (fun _ : Window T => (0 : Z)))
    · have hv : Continuous (fun t => V.process t ω) := by
        by_contra hbad
        exact hω (hsub hbad)
      simpa only [g, hω, ite_false] using hv
  have hg (t : Window T) : StronglyMeasurable (g t) := by
    change StronglyMeasurable (B.piecewise (fun _ => (0 : Z)) (V.process t))
    exact stronglyMeasurable_const.piecewise hBm ((V.adapted t).mono (D.filtration.le t.val))
  refine ⟨g, stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc hg, hc, ?_⟩
  filter_upwards [compl_mem_ae_iff.mpr hB0] with ω hω t
  change ω ∉ B at hω
  simp only [g, hω, ite_false]

/-- A measurable random observation time can be evaluated on the simultaneous
continuous version. The single null set is independent of the random time. -/
theorem ContinuousWindowVersion.stopped_aestronglyMeasurable (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (V : ContinuousWindowVersion Q D T U) (τ : Ω → Window T) (hτ : Measurable τ) :
    AEStronglyMeasurable (fun ω => V.process (τ ω) ω) Q := by
  obtain ⟨g, hg, _, he⟩ := ContinuousWindowVersion.exists_joint_realization Q D T U V
  have hs : StronglyMeasurable (fun ω => g (τ ω) ω) := hg.comp_measurable (hτ.prodMk measurable_id)
  apply hs.aestronglyMeasurable.congr
  exact he.mono (fun ω hω => hω (τ ω))

/-- The entire literal closed integrand is supported in its original horizon. -/
theorem closedStep_horizon (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) : timeCut Q U.val 0 T = U.val := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D (dyadicGrids T) U
  have hcut := ((timeCut_lipschitz (I := I) (Z := Z) Q 0 T).continuous.tendsto U.val).comp hA
  have he (n : ℕ) : timeCut Q (finiteStepInput Q D (dyadicGrids T) (A n)) 0 T =
      finiteStepInput Q D (dyadicGrids T) (A n) := coefficientStep_horizon Q D T (A n).1 (A n).2
  apply tendsto_nhds_unique hcut
  simpa only [Function.comp_def, he] using hA

theorem timeCut_horizon_intersection
    (U : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (T t : ℝ) :
    timeCut Q (timeCut Q U 0 T) 0 t = timeCut Q U 0 (min t T) := by
  apply Lp.ext
  filter_upwards [timeCut_coe Q (timeCut Q U 0 T) 0 t, timeCut_coe Q U 0 T,
    timeCut_coe Q U 0 (min t T)] with r houter hinner hmin
  rw [houter, hmin]
  have he := congrArg (fun s : Set ℝ => s.indicator U r)
    (show Ioc 0 t ∩ Ioc 0 T = Ioc 0 (min t T) by rw [Ioc_inter_Ioc, max_self])
  rw [← Set.indicator_indicator] at he
  by_cases hr : r ∈ Ioc 0 t
  · rw [Set.indicator_of_mem hr, hinner]
    simpa only [Set.indicator_of_mem hr] using he
  · rw [Set.indicator_of_notMem hr]
    simpa only [Set.indicator_of_notMem hr] using he

/-- The actual computed integral remains stopped after its finite horizon. -/
theorem closedIntegral_stopped (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    closedIntegral Q D T U (min t T) = closedIntegral Q D T U t := by
  unfold closedIntegral
  congr 1
  apply Subtype.ext
  change timeCut Q U.val 0 (min t T : ℝ≥0) = timeCut Q U.val 0 t
  rw [NNReal.coe_min, ← timeCut_horizon_intersection, closedStep_horizon]

/-- A clipped window observation, always in the actual finite horizon. -/
def windowClip (T t : ℝ≥0) : Window T := ⟨min t T, by change min t T ≤ T; exact min_le_right _ _⟩

theorem windowClip_continuous (T : ℝ≥0) : Continuous (windowClip T) := by
  unfold windowClip
  exact (continuous_id.min continuous_const).subtype_mk _

/-- Extend the actual simultaneous version to all times by stopping at T. -/
def ContinuousWindowVersion.extend (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (V : ContinuousWindowVersion Q D T U) (t : ℝ≥0) : Ω → Z := V.process (windowClip T t)

theorem ContinuousWindowVersion.extend_realizes (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (V : ContinuousWindowVersion Q D T U) (t : ℝ≥0) :
    ContinuousWindowVersion.extend Q D T U V t =ᵐ[Q] closedIntegral Q D T U t := by
  exact (V.realizes (windowClip T t)).trans (by rw [windowClip, closedIntegral_stopped])

theorem ContinuousWindowVersion.extend_martingale (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (V : ContinuousWindowVersion Q D T U) :
    Martingale (ContinuousWindowVersion.extend Q D T U V) D.filtration Q := by
  refine ⟨fun t => (V.adapted (windowClip T t)).mono (D.filtration.mono (min_le_left t T)), ?_⟩
  intro s t hst
  have ht := (ContinuousWindowVersion.extend_realizes Q D T U V t).trans
    (closedIntegral_representative_ae Q D T U t).symm
  have hs := (ContinuousWindowVersion.extend_realizes Q D T U V s).trans
    (closedIntegral_representative_ae Q D T U s).symm
  exact (condExp_congr_ae ht).trans
    (((closedIntegral_martingale Q D T U).condExp_ae_eq hst).trans hs.symm)

/-- Every actual completed integral has a simultaneous continuous martingale
modification on all nonnegative times, when its Brownian coordinates have
actual continuous paths. The process is stopped past its original horizon. -/
theorem exists_continuous_martingale_version (T : ℝ≥0)
    (U : ClosedStepDomain (Z := Z) Q D (dyadicGrids T))
    (hB : ∀ᵐ ω ∂Q, ∀ i, Continuous (fun t => D.process i t ω)) :
    ∃ M : ℝ≥0 → Ω → Z, Martingale M D.filtration Q ∧
      (∀ᵐ ω ∂Q, Continuous (fun t => M t ω)) ∧ ∀ t, M t =ᵐ[Q] closedIntegral Q D T U t := by
  obtain ⟨V⟩ := exists_continuousWindowVersion Q D T U hB
  refine ⟨ContinuousWindowVersion.extend Q D T U V,
    ContinuousWindowVersion.extend_martingale Q D T U V, ?_,
    ContinuousWindowVersion.extend_realizes Q D T U V⟩
  exact V.continuous_paths.mono (fun ω hω => hω.comp (windowClip_continuous T))

end PBGSO.FilteredBrownian
