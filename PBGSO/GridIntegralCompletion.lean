import PBGSO.BrownianGridIsometry
import PBGSO.TimeGridEnergy

/-! # L² completion of actual predictable Brownian sums

Coefficient step functions are literal elements of L²(time;L²(Ω)).
Refinement uses the same Brownian path. The stochastic-limit isometry is
derived from the finite formulas; it is not a supplied stochastic-integral
property.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.GridIntegralCompletion
open PBGSO.BrownianGridIsometry
variable {Ω Z : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q)
  (hBm : ∀ t, Measurable (B t))

/-- A primitive adapted square-integrable random coefficient. -/
structure Coefficient (t : ℝ≥0) where
  value : Ω → Z
  adapted : StronglyMeasurable[brownianFiltration B hBm t] value
  square : MemLp value 2 Q

abbrev Coefficients (τ : ℕ → ℝ≥0) := ∀ k, Coefficient (Z := Z) Q B hBm (τ k)

def Coefficient.toLp {t : ℝ≥0} (A : Coefficient (Z := Z) Q B hBm t) : Lp Z 2 Q :=
  A.square.toLp A.value

def coefficientStep (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q B hBm τ) (n : ℕ) :
    Lp (Lp Z 2 Q) 2 (volume : Measure ℝ) :=
  TimeGridEnergy.grid τ (fun k => (A k).toLp) n

include hB in
def stochasticStep (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q B hBm τ) (n : ℕ) : Lp Z 2 Q :=
  (gridSum_memLp Q B hB hBm τ hτ (fun k => (A k).value)
    (fun k => (A k).adapted) (fun k => (A k).square) n).toLp
      (gridSum B τ (fun k => (A k).value) n)

include hB in
theorem stochasticStep_norm_sq (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q B hBm τ) (n : ℕ) :
    ‖stochasticStep Q B hB hBm τ hτ A n‖ ^ 2 = ‖coefficientStep Q B hBm τ A n‖ ^ 2 := by
  rw [stochasticStep, gridSum_norm_sq Q B hB hBm τ hτ (fun k => (A k).value)
    (fun k => (A k).adapted) (fun k => (A k).square) n, coefficientStep,
    TimeGridEnergy.grid_norm_sq τ hτ]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [ProximalLangevin.lp_norm_sq_eq_integral]
  apply integral_congr_ae
  exact (A k).square.coeFn_toLp.fun_comp (fun z : Z => ‖z‖ ^ 2) |>.symm

def subtract (τ : ℕ → ℝ≥0) (A C : Coefficients (Z := Z) Q B hBm τ) :
    Coefficients (Z := Z) Q B hBm τ := fun k =>
  ⟨fun ω => (A k).value ω - (C k).value ω,
    (A k).adapted.sub (C k).adapted, (A k).square.sub (C k).square⟩

theorem subtract_toLp (τ : ℕ → ℝ≥0) (A C : Coefficients (Z := Z) Q B hBm τ) (k : ℕ) :
    (subtract Q B hBm τ A C k).toLp = (A k).toLp - (C k).toLp := by
  apply Lp.ext
  filter_upwards [(subtract Q B hBm τ A C k).square.coeFn_toLp,
    (A k).square.coeFn_toLp, (C k).square.coeFn_toLp,
    Lp.coeFn_sub (A k).toLp (C k).toLp] with ω hs ha hc hsub
  rw [hsub, Pi.sub_apply]
  simp only [Coefficient.toLp]
  rw [hs, ha, hc]
  rfl

theorem coefficientStep_sub (τ : ℕ → ℝ≥0) (A C : Coefficients (Z := Z) Q B hBm τ) (n : ℕ) :
    coefficientStep Q B hBm τ (subtract Q B hBm τ A C) n =
      coefficientStep Q B hBm τ A n - coefficientStep Q B hBm τ C n := by
  simp only [coefficientStep, subtract_toLp]
  exact TimeGridEnergy.grid_sub τ (fun k => (A k).toLp) (fun k => (C k).toLp) n

include hB in
theorem stochasticStep_sub (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A C : Coefficients (Z := Z) Q B hBm τ) (n : ℕ) :
    stochasticStep Q B hB hBm τ hτ (subtract Q B hBm τ A C) n =
      stochasticStep Q B hB hBm τ hτ A n - stochasticStep Q B hB hBm τ hτ C n := by
  let hA := gridSum_memLp Q B hB hBm τ hτ (fun k => (A k).value)
    (fun k => (A k).adapted) (fun k => (A k).square) n
  let hC := gridSum_memLp Q B hB hBm τ hτ (fun k => (C k).value)
    (fun k => (C k).adapted) (fun k => (C k).square) n
  let hS := gridSum_memLp Q B hB hBm τ hτ
    (fun k => (subtract Q B hBm τ A C k).value)
    (fun k => (subtract Q B hBm τ A C k).adapted)
    (fun k => (subtract Q B hBm τ A C k).square) n
  apply Lp.ext
  filter_upwards [hA.coeFn_toLp, hC.coeFn_toLp, hS.coeFn_toLp,
    Lp.coeFn_sub (stochasticStep Q B hB hBm τ hτ A n)
      (stochasticStep Q B hB hBm τ hτ C n)] with ω ha hc hs hsub
  rw [hsub, Pi.sub_apply]
  simp only [stochasticStep]
  rw [hs, ha, hc]
  exact gridSum_sub B τ (fun k => (A k).value) (fun k => (C k).value) n ω

include hB in
/-- Finite Brownian integration preserves the actual L² distance of its
coefficient time-step functions. -/
theorem stochasticStep_dist (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A C : Coefficients (Z := Z) Q B hBm τ) (n : ℕ) :
    dist (stochasticStep Q B hB hBm τ hτ A n) (stochasticStep Q B hB hBm τ hτ C n) =
      dist (coefficientStep Q B hBm τ A n) (coefficientStep Q B hBm τ C n) := by
  rw [dist_eq_norm, dist_eq_norm]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← stochasticStep_sub, ← coefficientStep_sub]
  exact stochasticStep_norm_sq Q B hB hBm τ hτ _ n



/-- Actual coefficient refinement, measurable at the new left endpoint. -/
def refine (τ υ : ℕ → ℝ≥0) (hυmono : Monotone υ) (d : ℕ) (_hd : 0 < d)
    (hυ : ∀ k, υ (d * k) = τ k) (A : Coefficients (Z := Z) Q B hBm τ) :
    Coefficients (Z := Z) Q B hBm υ := fun j =>
  ⟨(A (j / d)).value,
    (A (j / d)).adapted.mono ((brownianFiltration B hBm).mono (by
      rw [← hυ (j / d)]
      exact hυmono (Nat.mul_div_le j d))), (A (j / d)).square⟩

theorem refine_toLp (τ υ : ℕ → ℝ≥0) (hυmono : Monotone υ) (d : ℕ) (hd : 0 < d)
    (hυ : ∀ k, υ (d * k) = τ k) (A : Coefficients (Z := Z) Q B hBm τ) (j : ℕ) :
    (refine Q B hBm τ υ hυmono d hd hυ A j).toLp = (A (j / d)).toLp := rfl

theorem coefficientStep_refine (τ υ : ℕ → ℝ≥0) (hυmono : Monotone υ) (d : ℕ) (hd : 0 < d)
    (hυ : ∀ k, υ (d * k) = τ k) (A : Coefficients (Z := Z) Q B hBm τ) (n : ℕ) :
    coefficientStep Q B hBm υ (refine Q B hBm τ υ hυmono d hd hυ A) (d * n) =
      coefficientStep Q B hBm τ A n := by
  simp only [coefficientStep, refine_toLp]
  exact TimeGridEnergy.grid_refine_mul τ υ hυmono d hd hυ (fun k => (A k).toLp) n

include hB in
theorem stochasticStep_refine (τ υ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hυmono : Monotone υ) (d : ℕ) (hd : 0 < d) (hυ : ∀ k, υ (d * k) = τ k)
    (A : Coefficients (Z := Z) Q B hBm τ) (n : ℕ) :
    stochasticStep Q B hB hBm υ hυmono (refine Q B hBm τ υ hυmono d hd hυ A) (d * n) =
      stochasticStep Q B hB hBm τ hτ A n := by
  let C := refine Q B hBm τ υ hυmono d hd hυ A
  let hc := gridSum_memLp Q B hB hBm υ hυmono (fun k => (C k).value)
    (fun k => (C k).adapted) (fun k => (C k).square) (d * n)
  let ha := gridSum_memLp Q B hB hBm τ hτ (fun k => (A k).value)
    (fun k => (A k).adapted) (fun k => (A k).square) n
  apply Lp.ext
  filter_upwards [hc.coeFn_toLp, ha.coeFn_toLp] with ω hc ha
  simp only [stochasticStep]
  rw [hc, ha]
  exact gridSum_refine_mul B τ υ d hd hυ (fun k => (A k).value) n ω

/-- The primitive grid compatibility needed for completion. This contains
only deterministic time-grid relations. -/
structure RefiningGrids where
  time : ℕ → ℕ → ℝ≥0
  monotone : ∀ n, Monotone (time n)
  count : ℕ → ℕ
  compatible : ∀ m n, m ≤ n → ∃ d : ℕ, 0 < d ∧ count n = d * count m ∧
    ∀ k, time n (d * k) = time m k

include hB in
/-- The same distance identity holds across different compatible grids. -/
theorem stochasticStep_dist_cross (G : RefiningGrids) (m n : ℕ)
    (A : Coefficients (Z := Z) Q B hBm (G.time m))
    (C : Coefficients (Z := Z) Q B hBm (G.time n)) :
    dist (stochasticStep Q B hB hBm (G.time m) (G.monotone m) A (G.count m))
      (stochasticStep Q B hB hBm (G.time n) (G.monotone n) C (G.count n)) =
    dist (coefficientStep Q B hBm (G.time m) A (G.count m))
      (coefficientStep Q B hBm (G.time n) C (G.count n)) := by
  wlog hmn : m ≤ n generalizing m n A C
  · rw [dist_comm, dist_comm (coefficientStep Q B hBm (G.time m) A (G.count m))]
    exact this n m C A (by omega)
  obtain ⟨d, hd, hcount, htime⟩ := G.compatible m n hmn
  let R := refine Q B hBm (G.time m) (G.time n) (G.monotone n) d hd htime A
  have hS := stochasticStep_refine Q B hB hBm (G.time m) (G.time n)
    (G.monotone m) (G.monotone n) d hd htime A (G.count m)
  have hU := coefficientStep_refine Q B hBm (G.time m) (G.time n)
    (G.monotone n) d hd htime A (G.count m)
  rw [← hS, ← hU, ← hcount]
  exact stochasticStep_dist Q B hB hBm (G.time n) (G.monotone n) R C (G.count n)

include hB in
/-- Completion is derived from coefficient-time-L² convergence. No
Cauchy or isometry assumption is imposed on the stochastic sums. -/
theorem stochasticStep_cauchy (G : RefiningGrids)
    (A : ∀ n, Coefficients (Z := Z) Q B hBm (G.time n))
    (hA : CauchySeq (fun n => coefficientStep Q B hBm (G.time n) (A n) (G.count n))) :
    CauchySeq (fun n => stochasticStep Q B hB hBm (G.time n) (G.monotone n) (A n) (G.count n)) := by
  rw [Metric.cauchySeq_iff] at hA ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hA ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [stochasticStep_dist_cross]
  exact hN m hm n hn

include hB in
/-- Every convergent sequence of actual adapted step integrands defines a
unique L² Brownian-integral limit and its norm equals the integrand norm. -/
theorem exists_stochasticIntegral_limit (G : RefiningGrids)
    (A : ∀ n, Coefficients (Z := Z) Q B hBm (G.time n))
    (u : Lp (Lp Z 2 Q) 2 (volume : Measure ℝ))
    (hu : Tendsto (fun n => coefficientStep Q B hBm (G.time n) (A n) (G.count n)) atTop (𝓝 u)) :
    ∃ I : Lp Z 2 Q,
      Tendsto (fun n => stochasticStep Q B hB hBm (G.time n) (G.monotone n) (A n) (G.count n))
        atTop (𝓝 I) ∧ ‖I‖ = ‖u‖ := by
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete
    (stochasticStep_cauchy Q B hB hBm G A hu.cauchySeq)
  refine ⟨I, hI, ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hIl := ((continuous_norm.tendsto I).comp hI).pow 2
  have hul := ((continuous_norm.tendsto u).comp hu).pow 2
  exact tendsto_nhds_unique hIl (hul.congr' (Eventually.of_forall (fun n =>
    (stochasticStep_norm_sq Q B hB hBm (G.time n) (G.monotone n) (A n) (G.count n)).symm)))

include hB in
/-- The completed integral is independent of the approximating adapted
step functions. More generally it preserves their exact L² distance. -/
theorem stochasticIntegral_limit_dist (G : RefiningGrids)
    (A C : ∀ n, Coefficients (Z := Z) Q B hBm (G.time n))
    (u v : Lp (Lp Z 2 Q) 2 (volume : Measure ℝ)) (I J : Lp Z 2 Q)
    (hu : Tendsto (fun n => coefficientStep Q B hBm (G.time n) (A n) (G.count n)) atTop (𝓝 u))
    (hv : Tendsto (fun n => coefficientStep Q B hBm (G.time n) (C n) (G.count n)) atTop (𝓝 v))
    (hI : Tendsto (fun n => stochasticStep Q B hB hBm (G.time n) (G.monotone n) (A n) (G.count n))
      atTop (𝓝 I))
    (hJ : Tendsto (fun n => stochasticStep Q B hB hBm (G.time n) (G.monotone n) (C n) (G.count n))
      atTop (𝓝 J)) : dist I J = dist u v := by
  exact tendsto_nhds_unique (hI.dist hJ) ((hu.dist hv).congr'
    (Eventually.of_forall (fun n => (stochasticStep_dist Q B hB hBm (G.time n)
      (G.monotone n) (A n) (C n) (G.count n)).symm)))



/-- A concrete compatible sequence of dyadic grids. -/
def dyadicGrids (T : ℝ≥0) : RefiningGrids where
  time n k := (k : ℝ≥0) * (T / (2 : ℝ≥0) ^ n)
  monotone n := fun a b hab => mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (by positivity)
  count n := 2 ^ n
  compatible m n hmn := by
    refine ⟨2 ^ (n - m), by positivity, ?_, ?_⟩
    · calc
        2 ^ n = 2 ^ ((n - m) + m) := congrArg (fun j : ℕ => 2 ^ j) (by omega)
        _ = _ := pow_add 2 (n - m) m
    · intro k
      have hp : (2 : ℝ≥0) ^ n = (2 : ℝ≥0) ^ (n - m) * (2 : ℝ≥0) ^ m := by
        rw [← pow_add, show n - m + m = n by omega]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [hp]
      have h1 : (2 : ℝ≥0) ^ (n - m) ≠ 0 := by positivity
      have h2 : (2 : ℝ≥0) ^ m ≠ 0 := by positivity
      field_simp

/-- The domain consists of actual time-L² limits of adapted finite-step
functions on the refining grids. Thus stochastic integration is constructed
on the closure represented by such approximations. -/
abbrev IntegralDomain (G : RefiningGrids) :=
  {u : Lp (Lp Z 2 Q) 2 (volume : Measure ℝ) //
    ∃ A : ∀ n, Coefficients (Z := Z) Q B hBm (G.time n),
      Tendsto (fun n => coefficientStep Q B hBm (G.time n) (A n) (G.count n)) atTop (𝓝 u)}

include hB in
theorem integralDomain_exists_limit (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q B hBm G) :
    ∃ I : Lp Z 2 Q, ∃ A : ∀ n, Coefficients (Z := Z) Q B hBm (G.time n),
      Tendsto (fun n => coefficientStep Q B hBm (G.time n) (A n) (G.count n)) atTop (𝓝 u.val) ∧
      Tendsto (fun n => stochasticStep Q B hB hBm (G.time n) (G.monotone n) (A n) (G.count n))
        atTop (𝓝 I) ∧ ‖I‖ = ‖u.val‖ := by
  obtain ⟨A, hA⟩ := u.property
  obtain ⟨I, hI, hnorm⟩ := exists_stochasticIntegral_limit Q B hB hBm G A u.val hA
  exact ⟨I, A, hA, hI, hnorm⟩

include hB in
/-- The actual L² Brownian integral, constructed by completion. -/
def stochasticIntegral (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q B hBm G) : Lp Z 2 Q :=
  Classical.choose (integralDomain_exists_limit Q B hB hBm G u)

include hB in
theorem stochasticIntegral_norm (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q B hBm G) :
    ‖stochasticIntegral Q B hB hBm G u‖ = ‖u.val‖ := by
  obtain ⟨A, hA, hI, hnorm⟩ := Classical.choose_spec (integralDomain_exists_limit Q B hB hBm G u)
  exact hnorm

include hB in
/-- Every qualifying adapted step approximation converges to the
constructed integral, independently of all classical choices. -/
theorem stochasticIntegral_tendsto (G : RefiningGrids) (u : IntegralDomain (Z := Z) Q B hBm G)
    (A : ∀ n, Coefficients (Z := Z) Q B hBm (G.time n))
    (hA : Tendsto (fun n => coefficientStep Q B hBm (G.time n) (A n) (G.count n)) atTop (𝓝 u.val)) :
    Tendsto (fun n => stochasticStep Q B hB hBm (G.time n) (G.monotone n) (A n) (G.count n))
      atTop (𝓝 (stochasticIntegral Q B hB hBm G u)) := by
  obtain ⟨J, hJ, _⟩ := exists_stochasticIntegral_limit Q B hB hBm G A u.val hA
  obtain ⟨C, hC, hI, _⟩ := Classical.choose_spec (integralDomain_exists_limit Q B hB hBm G u)
  have hd := stochasticIntegral_limit_dist Q B hB hBm G A C u.val u.val J
    (stochasticIntegral Q B hB hBm G u) hA hC hJ hI
  rw [dist_self, dist_eq_zero] at hd
  simpa only [hd] using hJ

include hB in
/-- Brownian integration is an actual isometry on the constructed
predictable step-closure domain. -/
theorem stochasticIntegral_isometry (G : RefiningGrids) :
    Isometry (stochasticIntegral (Z := Z) Q B hB hBm G) := by
  apply Isometry.of_dist_eq
  intro u v
  obtain ⟨A, hA⟩ := u.property
  obtain ⟨C, hC⟩ := v.property
  exact stochasticIntegral_limit_dist Q B hB hBm G A C u.val v.val _ _ hA hC
    (stochasticIntegral_tendsto Q B hB hBm G u A hA)
    (stochasticIntegral_tendsto Q B hB hBm G v C hC)

end PBGSO.GridIntegralCompletion
