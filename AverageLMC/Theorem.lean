import AverageLMC.GaussianLMC
import AverageLMC.Complexity
import AverageLMC.ExtendedTransport

set_option linter.style.header false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace AverageLMC
open ULA ULA.Hilbert

/-- The actual LMC marginal laws with an arbitrary deterministic step schedule. -/
def lmcLaws {p : ℕ} (f : State p → ℝ) (steps : ℕ → ℝ)
    (μ : Measure (State p)) : ℕ → Measure (State p)
  | 0 => μ
  | k + 1 => ulaLawStep f (steps k) (lmcLaws f steps μ k)

@[simp] theorem lmcLaws_zero {p : ℕ} (f : State p → ℝ) (steps : ℕ → ℝ)
    (μ : Measure (State p)) : lmcLaws f steps μ 0 = μ := rfl

@[simp] theorem lmcLaws_succ {p : ℕ} (f : State p → ℝ) (steps : ℕ → ℝ)
    (μ : Measure (State p)) (k : ℕ) :
    lmcLaws f steps μ (k + 1) = ulaLawStep f (steps k) (lmcLaws f steps μ k) := rfl

instance lmcLaws_isProbability {p : ℕ} (f : State p → ℝ) (steps : ℕ → ℝ)
    (μ : Measure (State p)) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (lmcLaws f steps μ k) := by
  induction k with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ k ih =>
    change IsProbabilityMeasure ((lmcLaws f steps μ k).prod (stdGaussian (State p)) |>.map _)
    infer_instance

/-- Finite second moments propagate for every nonnegative LMC step. -/
theorem lmc_step_finite {p : ℕ} (f : State p → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 ≤ h) (hf : Differentiable ℝ f)
    (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith L (gradient f))
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤) :
    wasserstein2 (ulaLawStep f h μ) (gibbsMeasure f) ≠ ⊤ := by
  rcases eq_or_lt_of_le hh with rfl | hhpos
  · simpa using hfinite
  · simpa using dalalyan_output_finite f m h L hm hf hsc hLip hhpos μ hfinite 1

/-- Finite transport and moments are derived along the actual varying-step chain. -/
theorem lmcLaws_finite {p : ℕ} (f : State p → ℝ) (m : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f)) (steps : ℕ → ℝ) (hsteps : ∀ k, 0 ≤ steps k)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤) (k : ℕ) :
    wasserstein2 (lmcLaws f steps μ k) (gibbsMeasure f) ≠ ⊤ := by
  induction k with
  | zero => exact hfinite
  | succ k ih => exact lmc_step_finite f m (steps k) L hm (hsteps k) hf hsc hLip _ ih

/-- On the paper's stable step range the score correction is nonpositive. -/
theorem lmc_one_step_stable {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hm : 0 < m) (hh : 0 ≤ h)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f)) (hstep : h * (L : ℝ) ≤ 1)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤) :
    wasserstein2Real (ulaLawStep f h μ) (gibbsMeasure f) ^ 2 ≤
      (1 - m * h) / (1 + m * h) * wasserstein2Real μ (gibbsMeasure f) ^ 2 +
      ((averageSmoothness f + m) * h ^ 2 * p) / (1 + m * h) := by
  have hb := lmc_one_step hp f m h L hm hh hf hsc hLip μ hfinite
  have hn : h ^ 2 * (h * (L : ℝ) - 1) / (1 + m * h) *
      (∫ x, ‖gradient f x‖ ^ 2 ∂μ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)) (by positivity))
      (integral_nonneg fun _ ↦ sq_nonneg _)
  linarith

/-- Constant schedules agree with iteration of the actual Gaussian Markov step. -/
theorem lmcLaws_const {p : ℕ} (f : State p → ℝ) (h : ℝ)
    (μ : Measure (State p)) (k : ℕ) :
    lmcLaws f (fun _ ↦ h) μ k = (ulaLawStep f h)^[k] μ := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [lmcLaws_succ, Function.iterate_succ_apply', ih]

/-- Theorem 1, claim 3: the exact exponential constant-step LMC bound. -/
theorem lmc_constant_step {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hm : 0 < m) (hh : 0 ≤ h)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f)) (hstep : h * (L : ℝ) ≤ 1)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤) (k : ℕ) :
    wasserstein2Real ((ulaLawStep f h)^[k] μ) (gibbsMeasure f) ^ 2 ≤
      Real.exp (-2 * m * (k : ℝ) * h) * wasserstein2Real μ (gibbsMeasure f) ^ 2 +
        (averageSmoothness f + m) * h * p / (2 * m) := by
  let r := fun j ↦ wasserstein2Real (lmcLaws f (fun _ ↦ h) μ j) (gibbsMeasure f) ^ 2
  have hM : m ≤ averageSmoothness f := strongConvex_le_averageSmoothness hp f m L hf hsc hLip
  have hmL : m ≤ (L : ℝ) := hM.trans (averageSmoothness_le_global_bound hp f L hf hLip)
  have hmh : m * h ≤ 1 := by nlinarith
  have hMa : 0 ≤ averageSmoothness f + m := by linarith
  have ha : 0 ≤ (averageSmoothness f + m) * (p : ℝ) / m ^ 2 := by positivity
  have hs (j : ℕ) : r (j + 1) ≤
      (1 - m * h) / (1 + m * h) * r j +
        ((averageSmoothness f + m) * (p : ℝ) / m ^ 2) * (m * h) ^ 2 / (1 + m * h) := by
    have hj := lmc_one_step_stable hp f m h L hm hh hf hsc hLip hstep
      (lmcLaws f (fun _ ↦ h) μ j)
      (lmcLaws_finite f m L hm hf hsc hLip (fun _ ↦ h) (fun _ ↦ hh) μ hfinite j)
    convert hj using 1 <;> dsimp [r] <;> field_simp [hm.ne'] <;> ring
  have hb := constant_step_normalized r ((averageSmoothness f + m) * (p : ℝ) / m ^ 2)
    (m * h) ha (mul_nonneg hm.le hh) hmh (sq_nonneg _) hs k
  dsimp [r] at hb
  rw [lmcLaws_const] at hb
  rw [show -2 * m * (k : ℝ) * h = -2 * (m * h) * (k : ℝ) by ring]
  convert hb using 1 <;> simp only [lmcLaws_zero] <;> field_simp [hm.ne'] <;> ring

/-- The paper's dimensionless one-step inequality, derived for the actual marginal laws. -/
theorem lmc_normalized_step {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hm : 0 < m) (hh : 0 ≤ h)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f)) (hstep : h * (L : ℝ) ≤ 1)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤) :
    m / p * wasserstein2Real (ulaLawStep f h μ) (gibbsMeasure f) ^ 2 ≤
      (1 - m * h) / (1 + m * h) *
        (m / p * wasserstein2Real μ (gibbsMeasure f) ^ 2) +
      (averageSmoothness f / m + 1) * (m * h) ^ 2 / (1 + m * h) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hb := mul_le_mul_of_nonneg_left
    (lmc_one_step_stable hp f m h L hm hh hf hsc hLip hstep μ hfinite)
    (show 0 ≤ m / (p : ℝ) by positivity)
  convert hb using 1 <;> field_simp [hm.ne', hp'.ne'] <;> ring

/-- The exact step schedule of Proposition 1, written dimensionlessly. -/
def lmcVariableSchedule (M m : ℝ) (k₀ k : ℕ) : ℝ :=
  variableStep (M / m) k₀ k / m

/-- The dimensionless presentation is exactly `1/(M+m(k-k₀)₊)` from the paper. -/
theorem lmcVariableSchedule_eq {M m : ℝ} (hm : 0 < m) (hM : 0 < M)
    (k₀ k : ℕ) :
    lmcVariableSchedule M m k₀ k = 1 / (M + m * ((k - k₀ : ℕ) : ℝ)) := by
  have hn := Nat.cast_nonneg (α := ℝ) (k - k₀)
  have hd : 0 < M + m * ((k - k₀ : ℕ) : ℝ) := by positivity
  unfold lmcVariableSchedule variableStep
  field_simp [hm.ne', hd.ne']

/-- Proposition 1's scalar warmup conclusion also covers zero initial error. -/
private theorem variable_step_normalized_all (r : ℕ → ℝ) (a κ ε₀ : ℝ)
    (ha : 0 < a) (hκ : 1 ≤ κ) (hr0 : 0 ≤ r 0) (hinit : r 0 ≤ ε₀ ^ 2)
    (hstep : ∀ k, r (k + 1) ≤
      (1 - variableStep κ (warmup κ a ε₀) k) /
        (1 + variableStep κ (warmup κ a ε₀) k) * r k +
      a * variableStep κ (warmup κ a ε₀) k ^ 2 /
        (1 + variableStep κ (warmup κ a ε₀) k))
    (k : ℕ) (hk : warmup κ a ε₀ ≤ k) :
    r k ≤ a / (κ + ((k - warmup κ a ε₀ : ℕ) : ℝ)) := by
  by_cases hε : ε₀ = 0
  · subst ε₀
    have hw : warmup κ a 0 = 0 := by simp [warmup, positiveLog]
    rw [hw] at hstep hk ⊢
    have hi : r 0 ≤ a / κ := (by simpa using hinit : r 0 ≤ 0).trans (by positivity)
    simpa only [Nat.sub_zero] using variable_step_tail r a κ ha.le hκ hi
      (by simpa only [variableStep, Nat.sub_zero] using hstep) k
  · have hw : warmup κ a |ε₀| = warmup κ a ε₀ := by simp [warmup, sq_abs]
    have hb := variable_step_normalized r a κ |ε₀| ha hκ (abs_pos.mpr hε) hr0
      (by simpa only [sq_abs] using hinit) (by simpa only [hw] using hstep) k
      (by simpa only [hw] using hk)
    simpa only [hw] using hb

/-- Proposition 1: the actual varying-step LMC law obeys the paper's envelope,
with its exact maximal and average condition numbers and exact warmup ceiling. -/
theorem lmc_variable_step {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m ε₀ : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f))
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤)
    (hinit : wasserstein2Real μ (gibbsMeasure f) ^ 2 ≤ ε₀ ^ 2 * p / m)
    (k : ℕ) (hk : warmup ((L : ℝ) / m) (averageSmoothness f / m + 1) ε₀ ≤ k) :
    let κ := (L : ℝ) / m
    let a := averageSmoothness f / m + 1
    let k₀ := warmup κ a ε₀
    wasserstein2Real (lmcLaws f (lmcVariableSchedule (L : ℝ) m k₀) μ k)
      (gibbsMeasure f) ^ 2 ≤
      a / (κ + ((k - k₀ : ℕ) : ℝ)) * p / m := by
  let κ := (L : ℝ) / m
  let a := averageSmoothness f / m + 1
  let k₀ := warmup κ a ε₀
  let steps := lmcVariableSchedule (L : ℝ) m k₀
  let r := fun j ↦ m / p * wasserstein2Real (lmcLaws f steps μ j) (gibbsMeasure f) ^ 2
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hM := strongConvex_le_averageSmoothness hp f m L hf hsc hLip
  have hmL := hM.trans (averageSmoothness_le_global_bound hp f L hf hLip)
  have hκ : 1 ≤ κ := (one_le_div hm).mpr hmL
  have hκ0 : 0 < κ := by linarith
  have hMpos : 0 < averageSmoothness f := lt_of_lt_of_le hm hM
  have ha : 0 < a := by dsimp [a]; positivity
  have hs (j : ℕ) : 0 ≤ steps j ∧ steps j * (L : ℝ) ≤ 1 := by
    have hv := variableStep_le hκ0 k₀ j
    have he : steps j * (L : ℝ) = variableStep κ k₀ j * κ := by
      dsimp [steps, lmcVariableSchedule, κ]
      ring
    refine ⟨?_, ?_⟩
    · dsimp [steps, lmcVariableSchedule]
      exact div_nonneg hv.1.le hm.le
    · rw [he]
      exact (mul_le_mul_of_nonneg_right hv.2 hκ0.le).trans_eq (one_div_mul_cancel hκ0.ne')
  have hr0 : 0 ≤ r 0 := mul_nonneg (by positivity) (sq_nonneg _)
  have hi : r 0 ≤ ε₀ ^ 2 := by
    have hi := mul_le_mul_of_nonneg_left hinit (show 0 ≤ m / (p : ℝ) by positivity)
    dsimp [r]
    simp only [lmcLaws_zero]
    convert hi using 1 <;> field_simp [hm.ne', hp'.ne'] <;> ring
  have hrec (j : ℕ) : r (j + 1) ≤
      (1 - variableStep κ k₀ j) / (1 + variableStep κ k₀ j) * r j +
      a * variableStep κ k₀ j ^ 2 / (1 + variableStep κ k₀ j) := by
    have hj := lmc_normalized_step hp f m (steps j) L hm (hs j).1 hf hsc hLip (hs j).2
      (lmcLaws f steps μ j)
      (lmcLaws_finite f m L hm hf hsc hLip steps (fun j ↦ (hs j).1) μ hfinite j)
    have ht : m * steps j = variableStep κ k₀ j := by
      dsimp [steps, lmcVariableSchedule, κ]
      field_simp [hm.ne']
    simpa only [r, a, lmcLaws_succ, ht] using hj
  have hb := variable_step_normalized_all r a κ ε₀ ha hκ hr0 hi hrec k hk
  change wasserstein2Real (lmcLaws f steps μ k) (gibbsMeasure f) ^ 2 ≤
    a / (κ + ((k - k₀ : ℕ) : ℝ)) * p / m
  change m / p * wasserstein2Real (lmcLaws f steps μ k) (gibbsMeasure f) ^ 2 ≤
    a / (κ + ((k - k₀ : ℕ) : ℝ)) at hb
  have hd : 0 < κ + ((k - k₀ : ℕ) : ℝ) := by positivity
  apply (mul_le_mul_iff_of_pos_left (show 0 < m / (p : ℝ) by positivity)).mp
  convert hb using 1 <;> field_simp [hm.ne', hp'.ne', hd.ne'] <;> ring

/-- The exact iteration ceiling in Proposition 1 gives the requested accuracy
for the actual Gaussian varying-step algorithm. -/
theorem lmc_variable_step_accuracy {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m ε₀ ε : ℝ) (L : ℝ≥0) (hm : 0 < m) (hε : 0 < ε)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f))
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤)
    (hinit : wasserstein2Real μ (gibbsMeasure f) ^ 2 ≤ ε₀ ^ 2 * p / m)
    (k : ℕ) (hk : variableIterations ((L : ℝ) / m) (averageSmoothness f / m + 1) ε₀ ε ≤ k) :
    let κ := (L : ℝ) / m
    let a := averageSmoothness f / m + 1
    let k₀ := warmup κ a ε₀
    wasserstein2Real (lmcLaws f (lmcVariableSchedule (L : ℝ) m k₀) μ k)
      (gibbsMeasure f) ^ 2 ≤ ε ^ 2 * p / m := by
  have hM := strongConvex_le_averageSmoothness hp f m L hf hsc hLip
  have hmL := hM.trans (averageSmoothness_le_global_bound hp f L hf hLip)
  have hκ : 0 < (L : ℝ) / m := div_pos (lt_of_lt_of_le hm hmL) hm
  have hMpos : 0 < averageSmoothness f := lt_of_lt_of_le hm hM
  have ha : 0 < averageSmoothness f / m + 1 := by positivity
  have he := variable_iterations_envelope hκ ha hε hk
  have hb := lmc_variable_step hp f m ε₀ L hm hf hsc hLip μ hfinite hinit k he.1
  exact hb.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right he.2 (Nat.cast_nonneg p)) hm.le)

/-- Theorem 1's global bound in extended nonnegative transport, for every
initial probability law, including infinite initial second moment. -/
theorem lmc_constant_step_extended {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hm : 0 < m) (hh : 0 ≤ h)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f)) (hstep : h * (L : ℝ) ≤ 1)
    (μ : Measure (State p)) [IsProbabilityMeasure μ] (k : ℕ) :
    wasserstein2 ((ulaLawStep f h)^[k] μ) (gibbsMeasure f) ^ 2 ≤
      ENNReal.ofReal (Real.exp (-2 * m * (k : ℝ) * h)) *
        wasserstein2 μ (gibbsMeasure f) ^ 2 +
      ENNReal.ofReal ((averageSmoothness f + m) * h * p / (2 * m)) := by
  have hM := strongConvex_le_averageSmoothness hp f m L hf hsc hLip
  have hMa : 0 ≤ averageSmoothness f + m := by linarith
  apply squared_transport_extended μ (gibbsMeasure f)
    ((ulaLawStep f h)^[k] μ) (gibbsMeasure f)
    (Real.exp (-2 * m * (k : ℝ) * h))
    ((averageSmoothness f + m) * h * p / (2 * m)) (Real.exp_pos _) (by positivity)
  · intro hi
    have ho := lmcLaws_finite f m L hm hf hsc hLip (fun _ ↦ h) (fun _ ↦ hh) μ hi k
    rwa [lmcLaws_const] at ho
  · intro hi
    exact lmc_constant_step hp f m h L hm hh hf hsc hLip hstep μ hi k

/-- A finite extended squared-transport bound implies precisely the finite
real initial-error hypothesis used in Proposition 1. -/
theorem finite_initial_error_of_extended {p : ℕ} (μ π : Measure (State p))
    (m ε₀ : ℝ) (hm : 0 < m)
    (hinit : wasserstein2 μ π ^ 2 ≤ ENNReal.ofReal (ε₀ ^ 2 * p / m)) :
    wasserstein2 μ π ≠ ⊤ ∧ wasserstein2Real μ π ^ 2 ≤ ε₀ ^ 2 * p / m := by
  have hi : wasserstein2 μ π ≠ ⊤ := by
    intro h
    simp [h] at hinit
  refine ⟨hi, ?_⟩
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hinit
  simpa only [wasserstein2Real, ENNReal.toReal_pow, ENNReal.toReal_ofReal (show 0 ≤ ε₀ ^ 2 * (p : ℝ) / m by positivity)]
    using hr

/-- Proposition 1 with exactly a bounded initial squared-transport assumption;
no separate finite-moment premise is required. -/
theorem lmc_variable_step_extended_initial {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m ε₀ : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f))
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hinit : wasserstein2 μ (gibbsMeasure f) ^ 2 ≤ ENNReal.ofReal (ε₀ ^ 2 * p / m))
    (k : ℕ) (hk : warmup ((L : ℝ) / m) (averageSmoothness f / m + 1) ε₀ ≤ k) :
    let κ := (L : ℝ) / m
    let a := averageSmoothness f / m + 1
    let k₀ := warmup κ a ε₀
    wasserstein2Real (lmcLaws f (lmcVariableSchedule (L : ℝ) m k₀) μ k)
      (gibbsMeasure f) ^ 2 ≤ a / (κ + ((k - k₀ : ℕ) : ℝ)) * p / m := by
  obtain ⟨hi, hr⟩ := finite_initial_error_of_extended μ (gibbsMeasure f) m ε₀ hm hinit
  exact lmc_variable_step hp f m ε₀ L hm hf hsc hLip μ hi hr k hk

/-- The iteration threshold of Proposition 1 under its bounded extended
initial squared-transport assumption. -/
theorem lmc_variable_step_accuracy_extended_initial {p : ℕ} (hp : 0 < p) (f : State p → ℝ)
    (m ε₀ ε : ℝ) (L : ℝ≥0) (hm : 0 < m) (hε : 0 < ε)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f))
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hinit : wasserstein2 μ (gibbsMeasure f) ^ 2 ≤ ENNReal.ofReal (ε₀ ^ 2 * p / m))
    (k : ℕ) (hk : variableIterations ((L : ℝ) / m) (averageSmoothness f / m + 1) ε₀ ε ≤ k) :
    let κ := (L : ℝ) / m
    let a := averageSmoothness f / m + 1
    let k₀ := warmup κ a ε₀
    wasserstein2Real (lmcLaws f (lmcVariableSchedule (L : ℝ) m k₀) μ k)
      (gibbsMeasure f) ^ 2 ≤ ε ^ 2 * p / m := by
  obtain ⟨hi, hr⟩ := finite_initial_error_of_extended μ (gibbsMeasure f) m ε₀ hm hinit
  exact lmc_variable_step_accuracy hp f m ε₀ ε L hm hε hf hsc hLip μ hi hr k hk

end AverageLMC
