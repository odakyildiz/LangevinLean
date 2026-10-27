import AverageLMC.ScoreMoment
import AverageLMC.Smoothing
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Normed.Group.Bounded

set_option linter.style.header false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AverageLMC

/-- The actual finite sum potential in equation (eq:fsum). -/
def componentPotential {p n : ℕ} (f : Fin n → State p → ℝ) (x : State p) : ℝ :=
  ∑ i, f i x

/-- The uniform probability on the `n` finite component indices (`n>0`). -/
def uniformIndexLaw (n : ℕ) : Measure (Fin n) :=
  (n : ℝ≥0∞)⁻¹ • Measure.count

theorem uniformIndexLaw_probability (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (uniformIndexLaw n) := by
  constructor
  simp [uniformIndexLaw, Measure.smul_apply, hn.ne', ENNReal.inv_mul_cancel]

instance uniformIndexLaw_isFiniteMeasure (n : ℕ) : IsFiniteMeasure (uniformIndexLaw n) := by
  by_cases hn : 0 < n
  · have := uniformIndexLaw_probability n hn
    infer_instance
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    constructor
    simp [uniformIndexLaw]

theorem integral_uniformIndexLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (n : ℕ) (g : Fin n → E) :
    (∫ i, g i ∂uniformIndexLaw n) = (n : ℝ)⁻¹ • ∑ i, g i := by
  simp [uniformIndexLaw, integral_smul_measure, ENNReal.toReal_inv]

theorem gradient_componentPotential {p n : ℕ} (f : Fin n → State p → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (x : State p) :
    gradient (componentPotential f) x = ∑ i, gradient (f i) x := by
  apply (InnerProductSpace.toDual ℝ (State p)).injective
  simp only [map_sum, toDual_gradient]
  exact fderiv_fun_sum (fun i _ ↦ hf i x)

/-- The paper's fixed-point control-variate gradient estimator. -/
def controlVariateEstimator {p n : ℕ} (f : Fin n → State p → ℝ)
    (xstar x : State p) (i : Fin n) : State p :=
  (n : ℝ) • (gradient (f i) x - gradient (f i) xstar)

theorem controlVariateEstimator_at_anchor {p n : ℕ} (f : Fin n → State p → ℝ)
    (xstar : State p) (i : Fin n) : controlVariateEstimator f xstar xstar i = 0 := by
  simp [controlVariateEstimator]

theorem controlVariateEstimator_unbiased {p n : ℕ} (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (xstar : State p) (hstar : gradient (componentPotential f) xstar = 0)
    (x : State p) :
    (∫ i, controlVariateEstimator f xstar x i ∂uniformIndexLaw n) =
      gradient (componentPotential f) x := by
  rw [integral_uniformIndexLaw]
  simp_rw [controlVariateEstimator]
  rw [← Finset.smul_sum, Finset.sum_sub_distrib, smul_smul,
    inv_mul_cancel₀ (show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne'), one_smul,
    ← gradient_componentPotential f hf, ← gradient_componentPotential f hf, hstar, sub_zero]

/-- The exact squared RMS component seminorm, with no replacement constant. -/
theorem rmsComponentSmoothness_sq {p n : ℕ} (f : Fin n → State p → ℝ) :
    rmsComponentSmoothness f ^ 2 = (∑ i, globalSmoothness (f i) ^ 2) / (n : ℝ) := by
  apply Real.sq_sqrt
  exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)

theorem componentPotential_gradient_lipschitz {p n : ℕ} (f : Fin n → State p → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (L : Fin n → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (gradient (f i))) :
    LipschitzWith (∑ i, L i) (gradient (componentPotential f)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm, gradient_componentPotential f hf, NNReal.coe_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖gradient (f i) x - gradient (f i) y‖ := norm_sum_le _ _
    _ ≤ ∑ i, (L i : ℝ) * ‖x - y‖ := Finset.sum_le_sum fun i _ ↦ (hLip i).norm_sub_le x y
    _ = _ := (Finset.sum_mul ..).symm

theorem sum_globalSmoothness_le_n_mul_rms {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (L : Fin n → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (gradient (f i))) :
    (∑ i, globalSmoothness (f i)) ≤ (n : ℝ) * rmsComponentSmoothness f := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n ↦ globalSmoothness (f i)) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hc
  have heq : ((n : ℝ) * rmsComponentSmoothness f) ^ 2 =
      (∑ i, globalSmoothness (f i) ^ 2) * (n : ℝ) := by
    rw [mul_pow, rmsComponentSmoothness_sq]
    field_simp
  apply (sq_le_sq₀ (Finset.sum_nonneg fun i _ ↦ globalSmoothness_nonneg hp (f i) (L i) (hLip i))
    (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))).mp
  change (∑ i, globalSmoothness (f i)) ^ 2 ≤ ((n : ℝ) * rmsComponentSmoothness f) ^ 2
  rw [heq]
  exact hc

/-- The full finite sum is Lipschitz with exactly `n M_rms`. -/
theorem componentPotential_gradient_lipschitz_rms {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i))) :
    LipschitzWith ⟨(n : ℝ) * rmsComponentSmoothness f,
      mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)⟩
      (gradient (componentPotential f)) := by
  let C : Fin n → ℝ≥0 := fun i ↦
    ⟨globalSmoothness (f i), globalSmoothness_nonneg hp (f i) (L i) (hLip i)⟩
  have hc (i : Fin n) : LipschitzWith (C i) (gradient (f i)) :=
    gradient_lipschitz_globalSmoothness hp (f i) (L i) (hLip i)
  apply (componentPotential_gradient_lipschitz f hf C hc).weaken
  apply NNReal.coe_le_coe.mp
  change ((∑ i, C i : ℝ≥0) : ℝ) ≤ (n : ℝ) * rmsComponentSmoothness f
  rw [NNReal.coe_sum]
  exact sum_globalSmoothness_le_n_mul_rms hp hn f L hLip

theorem strongConvex_le_n_mul_rms {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (m : ℝ) (hsc : StrongConvexOn Set.univ m (componentPotential f)) :
    m ≤ (n : ℝ) * rmsComponentSmoothness f := by
  have hd : Differentiable ℝ (componentPotential f) :=
    Differentiable.fun_sum (fun i _ ↦ hf i)
  let C : ℝ≥0 := ⟨(n : ℝ) * rmsComponentSmoothness f,
    mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)⟩
  have hc : LipschitzWith C (gradient (componentPotential f)) :=
    componentPotential_gradient_lipschitz_rms hp hn f hf L hLip
  exact (strongConvex_le_coordinateSmoothness (componentPotential f) m C hd hsc hc
    ⟨0, hp⟩).trans (coordinateSmoothness_le_global_bound (componentPotential f) C hd hc ⟨0, hp⟩)

/-- Exact finite-index second moment of the actual control-variate estimator. -/
theorem controlVariateEstimator_second_moment {p n : ℕ} (hn : 0 < n)
    (f : Fin n → State p → ℝ) (xstar x : State p) :
    (∫ i, ‖controlVariateEstimator f xstar x i‖ ^ 2 ∂uniformIndexLaw n) =
      (n : ℝ) * ∑ i, ‖gradient (f i) x - gradient (f i) xstar‖ ^ 2 := by
  rw [integral_uniformIndexLaw]
  simp_rw [controlVariateEstimator, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n), mul_pow]
  rw [← Finset.mul_sum]
  simp only [smul_eq_mul]
  field_simp

/-- The estimator's second moment is controlled by distance to its anchor,
using exactly the RMS seminorm in (eq:Mtwo). -/
theorem controlVariateEstimator_second_moment_le {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (L : Fin n → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (gradient (f i))) (xstar x : State p) :
    (∫ i, ‖controlVariateEstimator f xstar x i‖ ^ 2 ∂uniformIndexLaw n) ≤
      (n : ℝ) ^ 2 * rmsComponentSmoothness f ^ 2 * ‖x - xstar‖ ^ 2 := by
  rw [controlVariateEstimator_second_moment hn]
  have hi (i : Fin n) : ‖gradient (f i) x - gradient (f i) xstar‖ ^ 2 ≤
      globalSmoothness (f i) ^ 2 * ‖x - xstar‖ ^ 2 := by
    have h := (gradient_lipschitz_globalSmoothness hp (f i) (L i) (hLip i)).norm_sub_le x xstar
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (globalSmoothness_nonneg hp (f i) (L i) (hLip i)) (norm_nonneg _))).mpr h
  have hs := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i)) (Nat.cast_nonneg n)
  rw [← Finset.sum_mul] at hs
  rw [rmsComponentSmoothness_sq]
  convert hs using 1 <;> field_simp <;> ring

/-- The actual centered stochastic-gradient error. -/
def controlVariateError {p n : ℕ} (f : Fin n → State p → ℝ)
    (xstar x : State p) (i : Fin n) : State p :=
  controlVariateEstimator f xstar x i - gradient (componentPotential f) x

theorem controlVariateError_centered {p n : ℕ} (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (xstar : State p) (hstar : gradient (componentPotential f) xstar = 0)
    (x : State p) : (∫ i, controlVariateError f xstar x i ∂uniformIndexLaw n) = 0 := by
  letI := uniformIndexLaw_probability n hn
  change (∫ i, controlVariateEstimator f xstar x i - gradient (componentPotential f) x
    ∂uniformIndexLaw n) = 0
  rw [integral_sub Integrable.of_finite (integrable_const _),
    controlVariateEstimator_unbiased hn f hf xstar hstar, integral_const,
    probReal_univ, one_smul, sub_self]

/-- The exact centered variance identity, retaining the negative full-gradient
energy term needed for the paper's larger-step one-step estimates. -/
theorem controlVariateError_second_moment {p n : ℕ} (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (xstar : State p) (hstar : gradient (componentPotential f) xstar = 0)
    (x : State p) :
    (∫ i, ‖controlVariateError f xstar x i‖ ^ 2 ∂uniformIndexLaw n) =
      (∫ i, ‖controlVariateEstimator f xstar x i‖ ^ 2 ∂uniformIndexLaw n) -
        ‖gradient (componentPotential f) x‖ ^ 2 := by
  letI := uniformIndexLaw_probability n hn
  have hmean := controlVariateEstimator_unbiased hn f hf xstar hstar x
  have hcross : (∫ i, inner ℝ (controlVariateEstimator f xstar x i)
      (gradient (componentPotential f) x) ∂uniformIndexLaw n) =
      ‖gradient (componentPotential f) x‖ ^ 2 := by
    calc
      _ = ∫ i, inner ℝ (gradient (componentPotential f) x)
          (controlVariateEstimator f xstar x i) ∂uniformIndexLaw n :=
        integral_congr_ae (ae_of_all _ fun i ↦ real_inner_comm _ _)
      _ = inner ℝ (gradient (componentPotential f) x)
          (∫ i, controlVariateEstimator f xstar x i ∂uniformIndexLaw n) :=
        integral_inner Integrable.of_finite _
      _ = _ := by rw [hmean, real_inner_self_eq_norm_sq]
  simp_rw [controlVariateError, norm_sub_sq_real]
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const_mul, hcross, integral_const, probReal_univ, one_smul]
  ring

theorem controlVariateError_second_moment_le {p n : ℕ} (hp : 0 < p) (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (xstar : State p) (hstar : gradient (componentPotential f) xstar = 0)
    (x : State p) :
    (∫ i, ‖controlVariateError f xstar x i‖ ^ 2 ∂uniformIndexLaw n) ≤
      (n : ℝ) ^ 2 * rmsComponentSmoothness f ^ 2 * ‖x - xstar‖ ^ 2 := by
  letI := uniformIndexLaw_probability n hn
  have hmean := controlVariateEstimator_unbiased hn f hf xstar hstar x
  have hcross : (∫ i, inner ℝ (controlVariateEstimator f xstar x i)
      (gradient (componentPotential f) x) ∂uniformIndexLaw n) =
      ‖gradient (componentPotential f) x‖ ^ 2 := by
    calc
      _ = ∫ i, inner ℝ (gradient (componentPotential f) x)
          (controlVariateEstimator f xstar x i) ∂uniformIndexLaw n :=
        integral_congr_ae (ae_of_all _ fun i ↦ real_inner_comm _ _)
      _ = inner ℝ (gradient (componentPotential f) x)
          (∫ i, controlVariateEstimator f xstar x i ∂uniformIndexLaw n) :=
        integral_inner Integrable.of_finite _
      _ = _ := by rw [hmean, real_inner_self_eq_norm_sq]
  have hvar : (∫ i, ‖controlVariateError f xstar x i‖ ^ 2 ∂uniformIndexLaw n) =
      (∫ i, ‖controlVariateEstimator f xstar x i‖ ^ 2 ∂uniformIndexLaw n) -
        ‖gradient (componentPotential f) x‖ ^ 2 := by
    simp_rw [controlVariateError, norm_sub_sq_real]
    rw [integral_add Integrable.of_finite Integrable.of_finite,
      integral_sub Integrable.of_finite Integrable.of_finite,
      integral_const_mul, hcross, integral_const, probReal_univ, one_smul]
    ring
  rw [hvar]
  exact (sub_le_self _ (sq_nonneg _)).trans
    (controlVariateEstimator_second_moment_le hp hn f L hLip xstar x)

/-- Finite independent index selection preserves every available L² moment. -/
theorem memLp_finite_index_selector {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) (n : ℕ)
    (g : Fin n → Ω → E) (hg : ∀ i, MemLp (g i) 2 P) :
    MemLp (fun q : Ω × Fin n ↦ g q.2 q.1) 2 (P.prod (uniformIndexLaw n)) := by
  classical
  have hset (i : Fin n) : MeasurableSet {q : Ω × Fin n | q.2 = i} :=
    measurable_snd (measurableSet_singleton i)
  have hsum := memLp_finsetSum Finset.univ (fun i _ ↦
    MemLp.indicator (hset i) ((hg i).comp_fst (uniformIndexLaw n)))
  convert hsum using 1
  funext q
  simp [Set.indicator_apply, eq_comm]

theorem controlVariateEstimator_product_memLp {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → State p → ℝ) (L : Fin n → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (xstar : State p) (X : Ω → State p) (hX : MemLp X 2 P) :
    MemLp (fun q : Ω × Fin n ↦ controlVariateEstimator f xstar (X q.1) q.2)
      2 (P.prod (uniformIndexLaw n)) := by
  apply memLp_finite_index_selector P n
    (fun i ω ↦ controlVariateEstimator f xstar (X ω) i)
  intro i
  have hg := ULA.lpDrift_memLp P (gradient (f i)) (hLip i) (hX.toLp X)
  have hg' : MemLp (fun ω ↦ gradient (f i) (X ω)) 2 P := by
    apply hg.ae_eq
    filter_upwards [hX.coeFn_toLp] with ω hω
    rw [hω]
  exact (hg'.sub (memLp_const (gradient (f i) xstar))).const_smul (n : ℝ)

theorem controlVariateError_product_memLp {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (xstar : State p) (X : Ω → State p) (hX : MemLp X 2 P) :
    MemLp (fun q : Ω × Fin n ↦ controlVariateError f xstar (X q.1) q.2)
      2 (P.prod (uniformIndexLaw n)) := by
  have hg (i : Fin n) : MemLp (fun ω ↦ gradient (f i) (X ω)) 2 P := by
    have h := ULA.lpDrift_memLp P (gradient (f i)) (hLip i) (hX.toLp X)
    apply h.ae_eq
    filter_upwards [hX.coeFn_toLp] with ω hω
    rw [hω]
  have hsum : MemLp (fun ω ↦ gradient (componentPotential f) (X ω)) 2 P := by
    simp_rw [gradient_componentPotential f hf]
    exact memLp_finsetSum Finset.univ (fun i _ ↦ hg i)
  exact (controlVariateEstimator_product_memLp P f L hLip xstar X hX).sub
    (hsum.comp_fst (uniformIndexLaw n))

theorem controlVariateError_product_measurable {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (xstar : State p) (X : Ω → State p) (hX : Measurable X) :
    Measurable (fun q : Ω × Fin n ↦ controlVariateError f xstar (X q.1) q.2) := by
  apply measurable_from_prod_countable_left
  intro i
  simp only [controlVariateError, controlVariateEstimator, gradient_componentPotential f hf]
  exact (((hLip i).continuous.measurable.comp hX).sub measurable_const).const_smul (n : ℝ)
    |>.sub (Finset.measurable_sum _ fun j _ ↦ (hLip j).continuous.measurable.comp hX)

theorem controlVariateError_product_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (hp : 0 < p) (hn : 0 < n) (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (xstar : State p) (hstar : gradient (componentPotential f) xstar = 0)
    (X : Ω → State p) (hX : MemLp X 2 P) :
    (∫ q : Ω × Fin n, ‖controlVariateError f xstar (X q.1) q.2‖ ^ 2
      ∂P.prod (uniformIndexLaw n)) ≤
      (n : ℝ) ^ 2 * rmsComponentSmoothness f ^ 2 *
        ∫ ω, ‖X ω - xstar‖ ^ 2 ∂P := by
  have hi := (controlVariateError_product_memLp P f hf L hLip xstar X hX).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have hdist := (hX.sub (memLp_const xstar)).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  rw [integral_prod _ hi]
  calc
    _ ≤ ∫ ω, (n : ℝ) ^ 2 * rmsComponentSmoothness f ^ 2 * ‖X ω - xstar‖ ^ 2 ∂P :=
      integral_mono hi.integral_prod_left
        (hdist.const_mul ((n : ℝ) ^ 2 * rmsComponentSmoothness f ^ 2))
        (fun ω ↦ controlVariateError_second_moment_le hp hn f hf L hLip xstar hstar (X ω))
    _ = _ := integral_const_mul _ _

/-- Positive strong convexity and differentiability provide the unique
minimizer used by the fixed-point control variate, including its zero score. -/
theorem exists_unique_minimizer {p : ℕ} (f : State p → ℝ) (m : ℝ) (hm : 0 < m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f) :
    ∃! xstar, (∀ x, f xstar ≤ f x) ∧ gradient f xstar = 0 := by
  have hb : Bornology.IsBounded {x : State p | f x ≤ f 0} := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨2 * ‖gradient f 0‖ / m, ?_⟩
    intro x hx
    change f x ≤ f 0 at hx
    have hl := ULA.strongConvex_quadratic_lower_bound f m hm hf hsc x
    have hd : ‖gradient f 0‖ ^ 2 / m * m = ‖gradient f 0‖ ^ 2 :=
      div_mul_cancel₀ _ hm.ne'
    have hs := mul_le_mul_of_nonneg_left (show m / 4 * ‖x‖ ^ 2 ≤
      ‖gradient f 0‖ ^ 2 / m by linarith) hm.le
    have hsq : (m * ‖x‖) ^ 2 ≤ (2 * ‖gradient f 0‖) ^ 2 := by nlinarith
    have hn : m * ‖x‖ ≤ 2 * ‖gradient f 0‖ :=
      (sq_le_sq₀ (mul_nonneg hm.le (norm_nonneg _)) (by positivity)).mp hsq
    exact (le_div_iff₀ hm).mpr (by simpa only [mul_comm] using hn)
  obtain ⟨xstar, hmin⟩ := hf.continuous.exists_forall_le_of_isBounded (0 : State p) hb
  have hz : gradient f xstar = 0 := by
    have hlocal : IsLocalMin f xstar := Filter.Eventually.of_forall hmin
    simp [gradient, hlocal.fderiv_eq_zero]
  refine ⟨xstar, ⟨hmin, hz⟩, ?_⟩
  intro y hy
  have hmono := ULA.strong_gradient_monotone hf hsc y xstar
  rw [hy.2, hz, sub_self, inner_zero_left] at hmono
  have hsq : ‖y - xstar‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖y - xstar‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

end AverageLMC
