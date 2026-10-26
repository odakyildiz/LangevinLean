import PBGSO.ClosedIntegralEnergy
import PBGSO.FilteredIntegralEnlargement

/-! # Actual closed-domain Brownian integration under pullback and enlargement -/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace PBGSO.FilteredBrownian
variable {Ω Ω' I Z : Type*} [mΩ : MeasurableSpace Ω] [mΩ' : MeasurableSpace Ω']
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

section Pullback
variable {Q : Measure Ω} [IsProbabilityMeasure Q] {R : Measure Ω'} [IsProbabilityMeasure R]
  {f : Ω → Ω'} (hf : MeasurePreserving f Q R) (D : Driver (I := I) R)

/-- Actual finite-step data transport through the same source map. -/
def pullbackFiniteStep (G : RefiningGrids) (A : FiniteStepData (Z := Z) R D G) :
    FiniteStepData (Z := Z) Q (pullbackDriver hf D) G :=
  ⟨A.1, pullbackCoefficients hf D (G.time A.1) A.2⟩

@[simp] theorem finiteStepInput_pullback (G : RefiningGrids)
    (A : FiniteStepData (Z := Z) R D G) :
    finiteStepInput Q (pullbackDriver hf D) G (pullbackFiniteStep hf D G A) =
      timePullbackCLM (I := I) hf (finiteStepInput R D G A) :=
  coefficientStep_pullback hf D (G.time A.1) A.2 (G.count A.1)

@[simp] theorem finiteStepOutput_pullback (G : RefiningGrids)
    (A : FiniteStepData (Z := Z) R D G) :
    finiteStepOutput Q (pullbackDriver hf D) G (pullbackFiniteStep hf D G A) =
      lpPullbackCLM hf (finiteStepOutput R D G A) :=
  stochasticStep_pullback hf D (G.time A.1) (G.monotone A.1) A.2 (G.count A.1)

/-- Pullback preserves the literal closed predictable-step domain; the actual
finite-step approximants are derived from closure membership. -/
def pullbackClosedDomain (G : RefiningGrids) (u : ClosedStepDomain (Z := Z) R D G) :
    ClosedStepDomain (Z := Z) Q (pullbackDriver hf D) G := by
  refine ⟨timePullbackCLM (I := I) hf u.val, ?_⟩
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation R D G u
  have hlim := ((timePullbackCLM (I := I) hf).continuous.tendsto u.val).comp hA
  apply isClosed_closure.mem_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  change timePullbackCLM (I := I) hf (finiteStepInput R D G (A n)) ∈ _
  rw [← finiteStepInput_pullback hf D G (A n)]
  exact subset_closure (Set.mem_range_self _)

/-- Computed closed-domain stochastic integration commutes with actual
probability-space pullback, rather than assuming matching stochastic outputs. -/
theorem closedStepIntegral_pullback (G : RefiningGrids)
    (u : ClosedStepDomain (Z := Z) R D G) :
    closedStepIntegral Q (pullbackDriver hf D) G (pullbackClosedDomain hf D G u) =
      lpPullbackCLM hf (closedStepIntegral R D G u) := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation R D G u
  have hB : Tendsto (fun n => finiteStepInput Q (pullbackDriver hf D) G
      (pullbackFiniteStep hf D G (A n))) atTop (𝓝 (pullbackClosedDomain hf D G u).val) := by
    simpa only [finiteStepInput_pullback, Function.comp_def, pullbackClosedDomain] using
      ((timePullbackCLM (I := I) hf).continuous.tendsto u.val).comp hA
  have h1 := closedStepIntegral_tendsto Q (pullbackDriver hf D) G
    (fun n => pullbackFiniteStep hf D G (A n)) (pullbackClosedDomain hf D G u) hB
  have h2 := ((lpPullbackCLM hf).continuous.tendsto (closedStepIntegral R D G u)).comp
    (closedStepIntegral_tendsto R D G A u hA)
  apply tendsto_nhds_unique h1
  simpa only [finiteStepOutput_pullback, Function.comp_def] using h2

/-- Literal coefficient-time interval masks commute with the actual pullback. -/
theorem timeCut_pullback
    (U : Lp (ColumnHilbert (I := I) (Z := Z) R) 2 (volume : Measure ℝ)) (s t : ℝ) :
    timeCut Q (timePullbackCLM (I := I) hf U) s t =
      timePullbackCLM (I := I) hf (timeCut R U s t) := by
  apply Lp.ext
  filter_upwards [timeCut_coe Q (timePullbackCLM (I := I) hf U) s t,
    (columnPullbackCLM (I := I) hf).coeFn_compLpL U,
    (columnPullbackCLM (I := I) hf).coeFn_compLpL (timeCut R U s t),
    timeCut_coe R U s t] with r hcut hU hT hmask
  change (timePullbackCLM (I := I) hf U) r = columnPullbackCLM hf (U r) at hU
  change (timePullbackCLM (I := I) hf (timeCut R U s t)) r = _ at hT
  rw [hcut, hT, hmask]
  by_cases hr : r ∈ Ioc s t
  · simp only [Set.indicator_of_mem hr, hU]
  · simp only [Set.indicator_of_notMem hr, map_zero]

/-- The entire computed noise process transports through an actual
measure-preserving source map, including every observation-time cut. -/
theorem closedIntegral_pullback (T : ℝ≥0)
    (u : ClosedStepDomain (Z := Z) R D (dyadicGrids T)) (t : ℝ≥0) :
    closedIntegral Q (pullbackDriver hf D) T (pullbackClosedDomain hf D (dyadicGrids T) u) t =
      lpPullbackCLM hf (closedIntegral R D T u t) := by
  have he : closedCutDomain Q (pullbackDriver hf D) T
      (pullbackClosedDomain hf D (dyadicGrids T) u) 0 t =
      pullbackClosedDomain hf D (dyadicGrids T) (closedCutDomain R D T u 0 t) := by
    apply Subtype.ext
    exact timeCut_pullback hf u.val 0 t
  rw [closedIntegral, he, closedStepIntegral_pullback]
  rfl
end Pullback

section Enlargement
variable (Q : Measure Ω) [IsProbabilityMeasure Q]
  (D E : Driver (I := I) Q) (hprocess : D.process = E.process)
  (henlarge : ∀ t, D.filtration t ≤ E.filtration t)

/-- The literal closed domain embeds in an enlarged valid driver filtration.
No completion-density assumption is required. -/
def enlargeClosedDomain (G : RefiningGrids) (u : ClosedStepDomain (Z := Z) Q D G) :
    ClosedStepDomain (Z := Z) Q E G := by
  refine ⟨u.val, ?_⟩
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G u
  apply isClosed_closure.mem_of_tendsto hA
  exact Eventually.of_forall (fun n => subset_closure (show finiteStepInput Q D G (A n) ∈
    Set.range (finiteStepInput (Z := Z) Q E G) from
    ⟨⟨(A n).1, enlargeCoefficients Q D E henlarge (G.time (A n).1) (A n).2⟩, rfl⟩))

include hprocess henlarge

/-- Actual stochastic integrals are unchanged by valid filtration enlargement. -/
theorem closedStepIntegral_enlarge (G : RefiningGrids)
    (u : ClosedStepDomain (Z := Z) Q D G) :
    closedStepIntegral Q E G (enlargeClosedDomain Q D E henlarge G u) =
      closedStepIntegral Q D G u := by
  obtain ⟨A, hA⟩ := exists_finiteStep_approximation Q D G u
  let B (n : ℕ) : FiniteStepData (Z := Z) Q E G :=
    ⟨(A n).1, enlargeCoefficients Q D E henlarge (G.time (A n).1) (A n).2⟩
  have h1 := closedStepIntegral_tendsto Q E G B (enlargeClosedDomain Q D E henlarge G u) hA
  have h2 := closedStepIntegral_tendsto Q D G A u hA
  apply tendsto_nhds_unique h1
  simpa only [B, finiteStepOutput, stochasticStep_enlarge Q D E hprocess henlarge] using h2

/-- Arbitrary closed domain entries representing the same actual time
coefficients give the same integral under a valid larger filtration. -/
theorem closedStepIntegral_eq_of_enlargement (G : RefiningGrids)
    (u : ClosedStepDomain (Z := Z) Q D G) (v : ClosedStepDomain (Z := Z) Q E G)
    (hval : v.val = u.val) : closedStepIntegral Q E G v = closedStepIntegral Q D G u := by
  have hv : v = enlargeClosedDomain Q D E henlarge G u := Subtype.ext hval
  rw [hv]
  exact closedStepIntegral_enlarge Q D E hprocess henlarge G u

theorem closedIntegral_enlarge (T : ℝ≥0)
    (u : ClosedStepDomain (Z := Z) Q D (dyadicGrids T)) (t : ℝ≥0) :
    closedIntegral Q E T (enlargeClosedDomain Q D E henlarge (dyadicGrids T) u) t =
      closedIntegral Q D T u t := by
  exact closedStepIntegral_eq_of_enlargement Q D E hprocess henlarge (dyadicGrids T)
    (closedCutDomain Q D T u 0 t)
    (closedCutDomain Q E T (enlargeClosedDomain Q D E henlarge (dyadicGrids T) u) 0 t) rfl
end Enlargement
end PBGSO.FilteredBrownian
