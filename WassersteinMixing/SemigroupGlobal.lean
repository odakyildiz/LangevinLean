import WassersteinMixing.SemigroupActual

/-! # A global canonical Gibbs Langevin path and its strongly continuous operators

Finite-horizon Picard solutions are identified by uniqueness. Selecting their
endpoints therefore gives a consistent global path, with the actual Gibbs law
at all nonnegative times. The observable transition is constructed from that
path, rather than supplied as an abstract semigroup.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace WassersteinMixing.CanonicalSemigroup

/-- The actual independent coordinate Brownian source on the common extension. -/
def brownian (P : Parameters) (i : Fin P.dimension) (t : ℝ≥0) (ω : ActualSpace P) : ℝ :=
  ULA.CanonicalBrownian.coordinate i t ω.2

theorem brownian_preBrownian (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) :
    ∀ i, IsPreBrownianReal (brownian P i) (actualProbability P V) := by
  let := actualTarget_isProbability P V hV
  exact ULA.Hilbert.productPreBrownian
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) (diagonalGibbsCoupling P V)
    ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian

/-- The actual Gibbs initialization on that same sample space. -/
def initial (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V) :
    Lp (E P.dimension) 2 (actualProbability P V) := by
  let := actualTarget_isProbability P V hV
  exact ULA.initialExtension_lpReference (diagonalGibbsCoupling P V)
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) (actualTarget_memLp P V hV)

theorem initial_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) :
    (actualProbability P V).map (initial P V hV) = ULA.gibbsMeasure V := by
  let := actualTarget_isProbability P V hV
  exact ULA.initialExtension_lpReference_law (diagonalGibbsCoupling P V)
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) (actualTarget_memLp P V hV)

/-- Finite-horizon solutions constructed by Picard from the actual Brownian source. -/
def solutionOn (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (T : ℝ) (hT : 0 ≤ T) : ℝ → Lp (E P.dimension) 2 (actualProbability P V) := by
  let := actualProbability_isProbability P V hV
  exact Classical.choose (ULA.exists_lp_langevin_integral_of_brownian (actualProbability P V)
    V ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (initial P V hV)
    (brownian P) (brownian_preBrownian P V hV) 0 T le_rfl hT)

theorem solutionOn_spec (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (T : ℝ) (hT : 0 ≤ T) :
    letI := actualProbability_isProbability P V hV
    Continuous (solutionOn P V hV T hT) ∧ solutionOn P V hV T hT 0 = initial P V hV ∧
    (∀ t ∈ Icc 0 T, solutionOn P V hV T hT t - initial P V hV =
      -(∫ s in 0..t, ULA.lpDrift (actualProbability P V) (gradient V)
        hV.gradientLipschitz (solutionOn P V hV T hT s)) +
      ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) 0 t) := by
  let := actualProbability_isProbability P V hV
  have hs := Classical.choose_spec (ULA.exists_lp_langevin_integral_of_brownian
    (actualProbability P V) V ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz
    (initial P V hV) (brownian P) (brownian_preBrownian P V hV) 0 T le_rfl hT)
  exact ⟨hs.1, hs.2.1, hs.2.2.1⟩

/-- The global path is selected from consistent finite-horizon endpoints.
Negative times are presented as the initial state. -/
def state (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (t : ℝ) : Lp (E P.dimension) 2 (actualProbability P V) :=
  solutionOn P V hV (max t 0) (le_max_right _ _) (max t 0)

/-- Uniqueness removes all dependence on the chosen finite horizon. -/
theorem state_eq_solutionOn (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (T : ℝ) (hT : 0 ≤ T)
    (t : ℝ) (ht : 0 ≤ t) (htT : t ≤ T) :
    state P V hV t = solutionOn P V hV T hT t := by
  let := actualProbability_isProbability P V hV
  have hs := solutionOn_spec P V hV t ht
  have hbig := solutionOn_spec P V hV T hT
  have hu := ULA.lp_langevin_integral_unique (actualProbability P V) V
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (initial P V hV)
    (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
      (brownian_preBrownian P V hV) 0)
    (solutionOn P V hV t ht) (solutionOn P V hV T hT) hs.1 hbig.1 t ht hs.2.2
    (fun s hs ↦ hbig.2.2 s ⟨hs.1, hs.2.trans htT⟩)
  simpa only [state, max_eq_left ht] using hu ⟨ht, le_rfl⟩

@[simp] theorem state_zero (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : state P V hV 0 = initial P V hV := by
  simpa only [state, max_self] using (solutionOn_spec P V hV 0 le_rfl).2.1

theorem state_eq_solutionOn_max (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (T : ℝ) (hT : 0 ≤ T)
    (t : ℝ) (htT : max t 0 ≤ T) :
    state P V hV t = solutionOn P V hV T hT (max t 0) := by
  have hx := state_eq_solutionOn P V hV T hT (max t 0) (le_max_right _ _) htT
  simpa only [state, max_eq_left (le_max_right t 0)] using hx

/-- The presentation is constant before time zero and genuinely continuous
on the whole real line, as follows from local finite-horizon uniqueness. -/
theorem continuous_state (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : Continuous (state P V hV) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let T := max t 0 + 1
  have hT : 0 ≤ T := by dsimp [T]; nlinarith [le_max_right t 0]
  have htT : t < T := by dsimp [T]; linarith [le_max_left t 0]
  have heq : state P V hV =ᶠ[𝓝 t] fun s ↦ solutionOn P V hV T hT (max s 0) := by
    have hs : ∀ᶠ s : ℝ in 𝓝 t, s < T := Iio_mem_nhds htT
    filter_upwards [hs] with s hs
    exact state_eq_solutionOn_max P V hV T hT s (max_le hs.le hT)
  exact (((solutionOn_spec P V hV T hT).1).comp
    (continuous_id.max continuous_const)).continuousAt.congr_of_eventuallyEq heq

/-- Actual global state continuity is proved locally using a longer fixed horizon. -/
theorem continuousOn_state (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : ContinuousOn (state P V hV) (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  have hT : 0 ≤ t + 1 := by linarith [ht]
  have heq : state P V hV =ᶠ[𝓝[Ici 0] t] solutionOn P V hV (t + 1) hT := by
    have hlt0 : ∀ᶠ s : ℝ in 𝓝 t, s < t + 1 := Iio_mem_nhds (by linarith)
    have hlt : ∀ᶠ s : ℝ in 𝓝[Ici 0] t, s < t + 1 :=
      hlt0.filter_mono nhdsWithin_le_nhds
    filter_upwards [hlt, self_mem_nhdsWithin] with s hs hs0
    exact state_eq_solutionOn P V hV (t + 1) hT s hs0 hs.le
  exact (solutionOn_spec P V hV (t + 1) hT).1.continuousAt.continuousWithinAt
    |>.congr_of_eventuallyEq_of_mem heq ht

/-- The global selected path satisfies the actual Langevin integral equation. -/
theorem state_integral (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) (ht : 0 ≤ t) :
    letI := actualProbability_isProbability P V hV
    state P V hV t - initial P V hV =
      -(∫ s in 0..t, ULA.lpDrift (actualProbability P V) (gradient V)
        hV.gradientLipschitz (state P V hV s)) +
      ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) 0 t := by
  let := actualProbability_isProbability P V hV
  have he := (solutionOn_spec P V hV t ht).2.2 t ⟨ht, le_rfl⟩
  rw [state_eq_solutionOn P V hV t ht t ht le_rfl]
  rw [he]
  congr 2
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  exact congrArg (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz)
    (state_eq_solutionOn P V hV t ht s hs.1 hs.2).symm

/-- The global selected state agrees with the actual comparison segment. -/
theorem state_eq_actualSegment (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 P.step) :
    state P V hV ((n : ℝ) * P.step + s) = actualSegment P V hV n s := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  let T := ((n : ℝ) + 1) * P.step
  have hT : 0 ≤ T := mul_nonneg (by positivity) P.step_pos.le
  have hnonneg : 0 ≤ (n : ℝ) * P.step + s :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) P.step_pos.le) hs.1
  have hle : (n : ℝ) * P.step + s ≤ T := by dsimp [T]; nlinarith [hs.2]
  rw [state_eq_solutionOn P V hV T hT _ hnonneg hle]
  have hspec := solutionOn_spec P V hV T hT
  have heq := ULA.Hilbert.brownianSegments_eq_global (actualProbability P V) V
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz (initial P V hV)
    (brownian P) (brownian_preBrownian P V hV)
    (solutionOn P V hV T hT) hspec.1 T hT hspec.2.2 P.step P.step_pos.le n le_rfl
  exact (heq hs).symm

/-- Grid-time identification with the genuine synchronous comparison reference. -/
theorem state_grid (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (n : ℕ) :
    state P V hV ((n : ℝ) * P.step) = actualReference P V hV n := by
  simpa only [add_zero, actualReference] using
    state_eq_actualSegment P V hV n 0 ⟨le_rfl, P.step_pos.le⟩

private theorem scalar_independent (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) :
    iIndepFun (fun p : ℕ × Fin P.dimension ↦ fun ω ↦
      ULA.Hilbert.brownianEulerNoise (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) r p.1 ω p.2) (actualProbability P V) := by
  let := actualTarget_isProbability P V hV
  have hs := ULA.Hilbert.productEulerNoise_independent
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) (diagonalGibbsCoupling P V)
    ULA.CanonicalBrownian.coordinate ULA.CanonicalBrownian.coordinate_isPreBrownian r hr
    (ULA.CanonicalBrownian.coordinate_grid_paths_independent (Fin P.dimension) r.toNNReal)
  simp only [ULA.Hilbert.productNoise_eq_brownianEulerNoise] at hs
  convert hs using 1 <;> rfl

private theorem initial_independent (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (_hr : 0 < r) :
    IndepFun (initial P V hV) (fun ω k ↦
      ULA.Hilbert.brownianEulerNoise (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) r k ω) (actualProbability P V) := by
  let := actualTarget_isProbability P V hV
  have hs := ULA.Hilbert.productEulerNoise_independentReference
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)) (diagonalGibbsCoupling P V)
    (actualTarget_memLp P V hV) ULA.CanonicalBrownian.coordinate
    ULA.CanonicalBrownian.coordinate_isPreBrownian r
  simp only [ULA.Hilbert.productNoise_eq_brownianEulerNoise] at hs
  convert hs using 1 <;> rfl

/-- Every actual global time has the Gibbs law, by the proved canonical
Brownian stationarity theorem. -/
theorem state_law (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) :
    (actualProbability P V).map (state P V hV t) = ULA.gibbsMeasure V := by
  let := actualProbability_isProbability P V hV
  let T := max t 0
  have hT : 0 ≤ T := le_max_right _ _
  have hs := solutionOn_spec P V hV T hT
  exact ULA.lp_langevin_gibbs_stationary (actualProbability P V) V P.alpha
    ⟨P.beta, P.beta_pos.le⟩ P.alpha_pos (hV.regularity.differentiable (by norm_num))
    hV.strongConvexity hV.gradientLipschitz (initial P V hV) (initial_law P V hV)
    (brownian P) (brownian_preBrownian P V hV) (scalar_independent P V hV)
    (initial_independent P V hV) (solutionOn P V hV T hT) hs.1 T hT hs.2.2

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Actual global stationary observable evaluations, over real or complex Hilbert targets. -/
def evaluation (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (t : ℝ) : Lp F 2 (ULA.gibbsMeasure V) →ₗᵢ[𝕜] Lp F 2 (actualProbability P V) :=
  StationaryObservables.evaluation (ULA.gibbsMeasure V) (actualProbability P V)
    (state P V hV t) (state_law P V hV t)

/-- The actual global observable transition, before proving its Markov composition law. -/
def op (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V) (t : ℝ) :
    Lp F 2 (ULA.gibbsMeasure V) →L[𝕜] Lp F 2 (ULA.gibbsMeasure V) :=
  ObservableTransition.compression (evaluation P V hV 0) (evaluation P V hV t)

@[simp] theorem op_zero (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) : op (𝕜 := 𝕜) (F := F) P V hV 0 = 1 :=
  ObservableTransition.compression_self _

theorem op_norm_le (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) (f : Lp F 2 (ULA.gibbsMeasure V)) :
    ‖op (𝕜 := 𝕜) P V hV t f‖ ≤ ‖f‖ :=
  ObservableTransition.compression_norm_le _ _ _

/-- Strong continuity of the actual global transition is a theorem about the
constructed Brownian path and stationary observable composition. -/
theorem continuousOn_op [NormedSpace ℝ F] (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (f : Lp F 2 (ULA.gibbsMeasure V)) :
    ContinuousOn (fun t ↦ op (𝕜 := 𝕜) P V hV t f) (Ici 0) := by
  let := actualTarget_isProbability P V hV
  let := actualProbability_isProbability P V hV
  intro t ht
  have hev := StationaryObservables.evaluation_tendsto (𝕜 := 𝕜)
    (ULA.gibbsMeasure V) (actualProbability P V) (state P V hV) (state P V hV t)
    (state_law P V hV) (state_law P V hV t) ((continuousOn_state P V hV) t ht) f
  exact (evaluation (𝕜 := 𝕜) (F := F) P V hV 0).toContinuousLinearMap.adjoint.continuous.tendsto
    (evaluation (𝕜 := 𝕜) P V hV t f) |>.comp hev

end WassersteinMixing.CanonicalSemigroup
