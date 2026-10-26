import PBGSO.FilteredBrownian
import PBGSO.GridIntegralCompletion

/-! # Completion for filtered finite-column Brownian integration -/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

abbrev ColumnHilbert := PiLp 2 (fun _ : I => Lp Z 2 Q)

def Coefficient.toLp {t : ℝ≥0} (A : Coefficient (Z := Z) Q D t) : ColumnHilbert (I := I) (Z := Z) Q :=
  WithLp.toLp 2 (fun i => (A.square i).toLp (A.value i))

def coefficientStep (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) :=
  TimeGridEnergy.grid τ (fun k => (A k).toLp) n

def stochasticStep (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) : Lp Z 2 Q :=
  (gridSum_memLp Q D τ hτ A n).toLp (gridSum Q D τ A n)

theorem stochasticStep_norm_sq (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    ‖stochasticStep Q D τ hτ A n‖ ^ 2 = ‖coefficientStep Q D τ A n‖ ^ 2 := by
  have he : ‖stochasticStep Q D τ hτ A n‖ ^ 2 =
      ∫ ω, ‖gridSum Q D τ A n ω‖ ^ 2 ∂Q := by
    rw [ProximalLangevin.lp_norm_sq_eq_integral]
    exact integral_congr_ae ((gridSum_memLp Q D τ hτ A n).coeFn_toLp.fun_comp
      (fun z : Z => ‖z‖ ^ 2))
  rw [he, coefficientStep, TimeGridEnergy.grid_norm_sq τ hτ]
  have hi := gridSum_isometry Q D (ContinuousLinearMap.id ℝ Z) (fun _ _ => rfl) τ hτ A n
  simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] at hi
  rw [hi]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [ProximalLangevin.lp_norm_sq_eq_integral]
  exact integral_congr_ae (((A k).square i).coeFn_toLp.fun_comp (fun z : Z => ‖z‖ ^ 2)) |>.symm

theorem subtract_toLp (τ : ℕ → ℝ≥0) (A C : Coefficients (Z := Z) Q D τ) (k : ℕ) :
    (subtract Q D τ A C k).toLp = (A k).toLp - (C k).toLp := by
  apply PiLp.ext
  intro i
  change ((subtract Q D τ A C k).square i).toLp _ =
    ((A k).square i).toLp _ - ((C k).square i).toLp _
  apply Lp.ext
  filter_upwards [((subtract Q D τ A C k).square i).coeFn_toLp,
    ((A k).square i).coeFn_toLp, ((C k).square i).coeFn_toLp,
    Lp.coeFn_sub (((A k).square i).toLp ((A k).value i))
      (((C k).square i).toLp ((C k).value i))] with ω hs ha hc hsub
  rw [hsub, Pi.sub_apply, hs, ha, hc]
  rfl

theorem coefficientStep_sub (τ : ℕ → ℝ≥0) (A C : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    coefficientStep Q D τ (subtract Q D τ A C) n =
      coefficientStep Q D τ A n - coefficientStep Q D τ C n := by
  simp only [coefficientStep, subtract_toLp]
  exact TimeGridEnergy.grid_sub τ (fun k => (A k).toLp) (fun k => (C k).toLp) n

theorem stochasticStep_sub (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A C : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    stochasticStep Q D τ hτ (subtract Q D τ A C) n =
      stochasticStep Q D τ hτ A n - stochasticStep Q D τ hτ C n := by
  apply Lp.ext
  filter_upwards [(gridSum_memLp Q D τ hτ A n).coeFn_toLp,
    (gridSum_memLp Q D τ hτ C n).coeFn_toLp,
    (gridSum_memLp Q D τ hτ (subtract Q D τ A C) n).coeFn_toLp,
    Lp.coeFn_sub (stochasticStep Q D τ hτ A n) (stochasticStep Q D τ hτ C n)]
    with ω ha hc hs hsub
  rw [hsub, Pi.sub_apply]
  simp only [stochasticStep]
  rw [hs, ha, hc]
  exact gridSum_sub Q D τ A C n ω

theorem stochasticStep_dist (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A C : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    dist (stochasticStep Q D τ hτ A n) (stochasticStep Q D τ hτ C n) =
      dist (coefficientStep Q D τ A n) (coefficientStep Q D τ C n) := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← stochasticStep_sub, ← coefficientStep_sub]
  exact stochasticStep_norm_sq Q D τ hτ _ n

theorem coefficientStep_refine (τ υ : ℕ → ℝ≥0) (hυmono : Monotone υ) (d : ℕ) (hd : 0 < d)
    (hυ : ∀ k, υ (d * k) = τ k) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    coefficientStep Q D υ (refine Q D τ υ hυmono d hd hυ A) (d * n) =
      coefficientStep Q D τ A n :=
  TimeGridEnergy.grid_refine_mul τ υ hυmono d hd hυ (fun k => (A k).toLp) n

theorem stochasticStep_refine (τ υ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hυmono : Monotone υ) (d : ℕ) (hd : 0 < d) (hυ : ∀ k, υ (d * k) = τ k)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    stochasticStep Q D υ hυmono (refine Q D τ υ hυmono d hd hυ A) (d * n) =
      stochasticStep Q D τ hτ A n := by
  apply Lp.ext
  filter_upwards [(gridSum_memLp Q D υ hυmono (refine Q D τ υ hυmono d hd hυ A) (d * n)).coeFn_toLp,
    (gridSum_memLp Q D τ hτ A n).coeFn_toLp] with ω hc ha
  simp only [stochasticStep]
  rw [hc, ha]
  exact gridSum_refine Q D τ υ hυmono d hd hυ A n ω

abbrev RefiningGrids := PBGSO.GridIntegralCompletion.RefiningGrids
abbrev dyadicGrids := PBGSO.GridIntegralCompletion.dyadicGrids
/-- The same distance identity holds across different compatible grids. -/
theorem stochasticStep_dist_cross (G : RefiningGrids) (m n : ℕ)
    (A : Coefficients (Z := Z) Q D (G.time m))
    (C : Coefficients (Z := Z) Q D (G.time n)) :
    dist (stochasticStep Q D (G.time m) (G.monotone m) A (G.count m))
      (stochasticStep Q D (G.time n) (G.monotone n) C (G.count n)) =
    dist (coefficientStep Q D (G.time m) A (G.count m))
      (coefficientStep Q D (G.time n) C (G.count n)) := by
  wlog hmn : m ≤ n generalizing m n A C
  · rw [dist_comm, dist_comm (coefficientStep Q D (G.time m) A (G.count m))]
    exact this n m C A (by omega)
  obtain ⟨d, hd, hcount, htime⟩ := G.compatible m n hmn
  let R := refine Q D (G.time m) (G.time n) (G.monotone n) d hd htime A
  have hS := stochasticStep_refine Q D (G.time m) (G.time n)
    (G.monotone m) (G.monotone n) d hd htime A (G.count m)
  have hU := coefficientStep_refine Q D (G.time m) (G.time n)
    (G.monotone n) d hd htime A (G.count m)
  rw [← hS, ← hU, ← hcount]
  exact stochasticStep_dist Q D (G.time n) (G.monotone n) R C (G.count n)

/-- Completion is derived from coefficient-time-L² convergence. No
Cauchy or isometry assumption is imposed on the stochastic sums. -/
theorem stochasticStep_cauchy (G : RefiningGrids)
    (A : ∀ n, Coefficients (Z := Z) Q D (G.time n))
    (hA : CauchySeq (fun n => coefficientStep Q D (G.time n) (A n) (G.count n))) :
    CauchySeq (fun n => stochasticStep Q D (G.time n) (G.monotone n) (A n) (G.count n)) := by
  rw [Metric.cauchySeq_iff] at hA ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hA ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [stochasticStep_dist_cross]
  exact hN m hm n hn

/-- Every convergent sequence of actual adapted step integrands defines a
unique L² Brownian-integral limit and its norm equals the integrand norm. -/
theorem exists_stochasticIntegral_limit (G : RefiningGrids)
    (A : ∀ n, Coefficients (Z := Z) Q D (G.time n))
    (u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ))
    (hu : Tendsto (fun n => coefficientStep Q D (G.time n) (A n) (G.count n)) atTop (𝓝 u)) :
    ∃ I : Lp Z 2 Q,
      Tendsto (fun n => stochasticStep Q D (G.time n) (G.monotone n) (A n) (G.count n))
        atTop (𝓝 I) ∧ ‖I‖ = ‖u‖ := by
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete
    (stochasticStep_cauchy Q D G A hu.cauchySeq)
  refine ⟨I, hI, ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hIl := ((continuous_norm.tendsto I).comp hI).pow 2
  have hul := ((continuous_norm.tendsto u).comp hu).pow 2
  exact tendsto_nhds_unique hIl (hul.congr' (Eventually.of_forall (fun n =>
    (stochasticStep_norm_sq Q D (G.time n) (G.monotone n) (A n) (G.count n)).symm)))

/-- The completed integral is independent of the approximating adapted
step functions. More generally it preserves their exact L² distance. -/
theorem stochasticIntegral_limit_dist (G : RefiningGrids)
    (A C : ∀ n, Coefficients (Z := Z) Q D (G.time n))
    (u v : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ)) (I J : Lp Z 2 Q)
    (hu : Tendsto (fun n => coefficientStep Q D (G.time n) (A n) (G.count n)) atTop (𝓝 u))
    (hv : Tendsto (fun n => coefficientStep Q D (G.time n) (C n) (G.count n)) atTop (𝓝 v))
    (hI : Tendsto (fun n => stochasticStep Q D (G.time n) (G.monotone n) (A n) (G.count n))
      atTop (𝓝 I))
    (hJ : Tendsto (fun n => stochasticStep Q D (G.time n) (G.monotone n) (C n) (G.count n))
      atTop (𝓝 J)) : dist I J = dist u v := by
  exact tendsto_nhds_unique (hI.dist hJ) ((hu.dist hv).congr'
    (Eventually.of_forall (fun n => (stochasticStep_dist Q D (G.time n)
      (G.monotone n) (A n) (C n) (G.count n)).symm)))



/-- The domain consists of actual time-L² limits of adapted finite-step
functions on the refining grids. Thus stochastic integration is constructed
on the closure represented by such approximations. -/
abbrev IntegralDomain (G : RefiningGrids) :=
  {u : Lp (ColumnHilbert (I := I) (Z := Z) Q) 2 (volume : Measure ℝ) //
    ∃ A : ∀ n, Coefficients (Z := Z) Q D (G.time n),
      Tendsto (fun n => coefficientStep Q D (G.time n) (A n) (G.count n)) atTop (𝓝 u)}

theorem integralDomain_exists_limit (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q D G) :
    ∃ I : Lp Z 2 Q, ∃ A : ∀ n, Coefficients (Z := Z) Q D (G.time n),
      Tendsto (fun n => coefficientStep Q D (G.time n) (A n) (G.count n)) atTop (𝓝 u.val) ∧
      Tendsto (fun n => stochasticStep Q D (G.time n) (G.monotone n) (A n) (G.count n))
        atTop (𝓝 I) ∧ ‖I‖ = ‖u.val‖ := by
  obtain ⟨A, hA⟩ := u.property
  obtain ⟨I, hI, hnorm⟩ := exists_stochasticIntegral_limit Q D G A u.val hA
  exact ⟨I, A, hA, hI, hnorm⟩

/-- The actual L² Brownian integral, constructed by completion. -/
def stochasticIntegral (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q D G) : Lp Z 2 Q :=
  Classical.choose (integralDomain_exists_limit Q D G u)

theorem stochasticIntegral_norm (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q D G) :
    ‖stochasticIntegral Q D G u‖ = ‖u.val‖ := by
  obtain ⟨A, hA, hI, hnorm⟩ := Classical.choose_spec (integralDomain_exists_limit Q D G u)
  exact hnorm

/-- Every qualifying adapted step approximation converges to the
constructed integral, independently of all classical choices. -/
theorem stochasticIntegral_tendsto (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q D G)
    (A : ∀ n, Coefficients (Z := Z) Q D (G.time n))
    (hA : Tendsto (fun n => coefficientStep Q D (G.time n) (A n) (G.count n)) atTop (𝓝 u.val)) :
    Tendsto (fun n => stochasticStep Q D (G.time n) (G.monotone n) (A n) (G.count n))
      atTop (𝓝 (stochasticIntegral Q D G u)) := by
  obtain ⟨J, hJ, _⟩ := exists_stochasticIntegral_limit Q D G A u.val hA
  obtain ⟨C, hC, hI, _⟩ := Classical.choose_spec (integralDomain_exists_limit Q D G u)
  have hd := stochasticIntegral_limit_dist Q D G A C u.val u.val J
    (stochasticIntegral Q D G u) hA hC hJ hI
  rw [dist_self, dist_eq_zero] at hd
  simpa only [hd] using hJ

/-- Brownian integration is an actual isometry on the constructed
predictable step-closure domain. -/
theorem stochasticIntegral_isometry (G : RefiningGrids) :
    Isometry (stochasticIntegral (Z := Z) Q D G) := by
  apply Isometry.of_dist_eq
  intro u v
  obtain ⟨A, hA⟩ := u.property
  obtain ⟨C, hC⟩ := v.property
  exact stochasticIntegral_limit_dist Q D G A C u.val v.val _ _ hA hC
    (stochasticIntegral_tendsto Q D G u A hA)
    (stochasticIntegral_tendsto Q D G v C hC)


end PBGSO.FilteredBrownian
