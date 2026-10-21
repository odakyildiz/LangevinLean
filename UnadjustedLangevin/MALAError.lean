import UnadjustedLangevin.Gibbs
import UnadjustedLangevin.LpDrift
import GradientDescent.Smooth
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique

set_option linter.style.header false

/-! # The local rejection error of Metropolis-adjusted Langevin

The log acceptance ratio and its rejection displacement are estimated using
only a differentiable potential and its Lipschitz gradient. Gaussian tail
domination supplies the Gibbs moments used by the integrated estimate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The ULA proposal used by MALA. -/
def malaProposal (U : H → ℝ) (h : ℝ) (x ξ : H) : H :=
  x - h • gradient U x + Real.sqrt (2 * h) • ξ

/-- Logarithm of the target-density ratio times the reverse/forward Gaussian
proposal-density ratio. The common Gaussian normalization cancels. -/
def malaLogRatio (U : H → ℝ) (h : ℝ) (x y : H) : ℝ :=
  U x - U y -
    (‖x - y + h • gradient U y‖ ^ 2 - ‖y - x + h • gradient U x‖ ^ 2) / (4 * h)

/-- Exact acceptance-ratio algebra, valid for every pair of states. -/
theorem malaLogRatio_expansion (U : H → ℝ) (h : ℝ) (hh : h ≠ 0) (x y : H) :
    malaLogRatio U h x y = U x - U y +
      (1 / 2 : ℝ) * inner ℝ (gradient U x + gradient U y) (y - x) -
        h / 4 * (‖gradient U y‖ ^ 2 - ‖gradient U x‖ ^ 2) := by
  have hsub : x - y = -(y - x) := by abel
  simp only [malaLogRatio, hsub, norm_add_sq_real, norm_neg, norm_smul,
    real_inner_smul_right, inner_neg_left, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_add_left]
  rw [real_inner_comm (y - x) (gradient U x), real_inner_comm (y - x) (gradient U y)]
  field_simp
  ring

/-- The difference of gradient squared norms is controlled by gradient
Lipschitzness and the two endpoint score norms. -/
theorem gradient_norm_sq_difference_bound (U : H → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) (x y : H) :
    |‖gradient U y‖ ^ 2 - ‖gradient U x‖ ^ 2| ≤
      (L : ℝ) * ‖y - x‖ * (‖gradient U x‖ + ‖gradient U y‖) := by
  have hn : |‖gradient U y‖ - ‖gradient U x‖| ≤ (L : ℝ) * ‖y - x‖ :=
    (abs_norm_sub_norm_le _ _).trans (by simpa only [dist_eq_norm] using hLip.dist_le_mul y x)
  rw [show ‖gradient U y‖ ^ 2 - ‖gradient U x‖ ^ 2 =
    (‖gradient U y‖ - ‖gradient U x‖) * (‖gradient U x‖ + ‖gradient U y‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right hn (by positivity)

/-- The trapezoidal potential increment has a quadratic Lipschitz bound.
No Hessian or derivative of the gradient is assumed. -/
theorem potential_trapezoid_bound (U : H → ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) (x y : H) :
    |U x - U y + (1 / 2 : ℝ) * inner ℝ (gradient U x + gradient U y) (y - x)| ≤
      (L : ℝ) * ‖y - x‖ ^ 2 := by
  have hxy := GradientDescent.smooth_upper_bound U L hdiff hLip x y
  have hyx := GradientDescent.smooth_upper_bound U L hdiff hLip y x
  have hsub : x - y = -(y - x) := by abel
  rw [hsub, inner_neg_right, norm_neg] at hyx
  have hgrad : |inner ℝ (gradient U y - gradient U x) (y - x)| ≤
      (L : ℝ) * ‖y - x‖ ^ 2 := by
    have hl : ‖gradient U y - gradient U x‖ ≤ (L : ℝ) * ‖y - x‖ := by
      simpa only [dist_eq_norm] using hLip.dist_le_mul y x
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (y - x)])
  rw [inner_sub_left, abs_le] at hgrad
  rw [inner_add_left, abs_le]
  constructor <;> nlinarith [hgrad.1, hgrad.2]

/-- The complete local log-ratio bound under the stated C¹/smoothness
assumptions. -/
theorem malaLogRatio_abs_bound (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hh : 0 < h) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (x y : H) :
    |malaLogRatio U h x y| ≤ (L : ℝ) * ‖y - x‖ ^ 2 +
      h * (L : ℝ) / 4 * ‖y - x‖ * (‖gradient U x‖ + ‖gradient U y‖) := by
  rw [malaLogRatio_expansion U h hh.ne']
  have ht := potential_trapezoid_bound U L hdiff hLip x y
  have hg := mul_le_mul_of_nonneg_left (gradient_norm_sq_difference_bound U L hLip x y)
    (by positivity : 0 ≤ h / 4)
  have hb := abs_sub (U x - U y + (1 / 2 : ℝ) *
    inner ℝ (gradient U x + gradient U y) (y - x))
      (h / 4 * (‖gradient U y‖ ^ 2 - ‖gradient U x‖ ^ 2))
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ h / 4)] at hb
  nlinarith

/-- The Metropolis rejection probability is bounded by the absolute log ratio. -/
theorem metropolis_rejection_le_abs (r : ℝ) :
    0 ≤ 1 - min 1 (Real.exp r) ∧ 1 - min 1 (Real.exp r) ≤ |r| := by
  have hlo : 1 - |r| ≤ min 1 (Real.exp r) :=
    le_min (by linarith [abs_nonneg r]) (by linarith [Real.add_one_le_exp r, neg_abs_le r])
  exact ⟨sub_nonneg.mpr (min_le_left _ _), by linarith⟩

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A rejected move contributes at most displacement times absolute log ratio
to the expected coupling error. -/
theorem rejected_displacement_le (r : ℝ) (x y : H) :
    ‖y - x‖ * (1 - min 1 (Real.exp r)) ≤ ‖y - x‖ * |r| :=
  mul_le_mul_of_nonneg_left (metropolis_rejection_le_abs r).2 (norm_nonneg _)

/-- A step-size-independent envelope for the proposal displacement. -/
def malaAmplitude (U : H → ℝ) (x ξ : H) : ℝ :=
  ‖gradient U x‖ + Real.sqrt 2 * ‖ξ‖

/-- The conditional expected displacement lost when the proposal is rejected. -/
def malaRejectionDisplacement (U : H → ℝ) (h : ℝ) (x ξ : H) : ℝ :=
  let y := malaProposal U h x ξ
  ‖y - x‖ * (1 - min 1 (Real.exp (malaLogRatio U h x y)))

theorem malaAmplitude_nonneg (U : H → ℝ) (x ξ : H) : 0 ≤ malaAmplitude U x ξ := by
  unfold malaAmplitude
  positivity

theorem malaRejectionDisplacement_nonneg (U : H → ℝ) (h : ℝ) (x ξ : H) :
    0 ≤ malaRejectionDisplacement U h x ξ :=
  mul_nonneg (norm_nonneg _) (metropolis_rejection_le_abs _).1

/-- On a step of length at most one, the proposal displacement is bounded by
the square root of the step length times the fixed amplitude. -/
theorem malaProposal_displacement_le (U : H → ℝ) (h : ℝ) (hh : 0 ≤ h) (h1 : h ≤ 1)
    (x ξ : H) :
    ‖malaProposal U h x ξ - x‖ ≤ Real.sqrt h * malaAmplitude U x ξ := by
  have hsq := Real.sq_sqrt hh
  have hs1 : Real.sqrt h ≤ 1 := Real.sqrt_le_one.mpr h1
  have hhs : h ≤ Real.sqrt h := by nlinarith [Real.sqrt_nonneg h]
  have heq : malaProposal U h x ξ - x =
      -(h • gradient U x) + Real.sqrt (2 * h) • ξ := by
    unfold malaProposal
    module
  rw [heq]
  calc
    _ ≤ ‖-(h • gradient U x)‖ + ‖Real.sqrt (2 * h) • ξ‖ := norm_add_le _ _
    _ = h * ‖gradient U x‖ + Real.sqrt 2 * Real.sqrt h * ‖ξ‖ := by
      simp only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh,
        Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)), abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg 2), abs_of_nonneg (Real.sqrt_nonneg h)]
    _ ≤ Real.sqrt h * malaAmplitude U x ξ := by
      unfold malaAmplitude
      nlinarith [mul_le_mul_of_nonneg_right hhs (norm_nonneg (gradient U x))]

/-- A Lipschitz gradient gives a local rejection error of order `h^(3/2)`.
The envelope is cubic and contains no step size. -/
theorem malaRejectionDisplacement_pointwise (U : H → ℝ) (h : ℝ) (L : ℝ≥0)
    (hh : 0 < h) (h1 : h ≤ 1) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (x ξ : H) :
    malaRejectionDisplacement U h x ξ ≤ h * Real.sqrt h *
      ((L : ℝ) * (2 + (L : ℝ)) * malaAmplitude U x ξ ^ 3) := by
  let y := malaProposal U h x ξ
  let r := ‖y - x‖
  let a := malaAmplitude U x ξ
  let s := Real.sqrt h
  have hr : 0 ≤ r := norm_nonneg _
  have ha : 0 ≤ a := malaAmplitude_nonneg U x ξ
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr h1
  have hs2 : s ^ 2 = h := Real.sq_sqrt hh.le
  have hhs : h ≤ s := by nlinarith
  have hstep : r ≤ s * a := malaProposal_displacement_le U h hh.le h1 x ξ
  have hra : r ≤ a := hstep.trans (by nlinarith)
  have hgxa : ‖gradient U x‖ ≤ a := by
    dsimp [a, malaAmplitude]
    exact le_add_of_nonneg_right (by positivity)
  have hgy : ‖gradient U y‖ ≤ ‖gradient U x‖ + (L : ℝ) * r := by
    have ht := norm_sub_le (gradient U y) (gradient U x)
    have hl : ‖gradient U y - gradient U x‖ ≤ (L : ℝ) * r := by
      simpa only [dist_eq_norm] using hLip.dist_le_mul y x
    have ht' := norm_add_le (gradient U y - gradient U x) (gradient U x)
    simpa only [sub_add_cancel] using ht'.trans (by nlinarith)
  have hscore : ‖gradient U x‖ + ‖gradient U y‖ ≤ (2 + (L : ℝ)) * a := by
    nlinarith [mul_le_mul_of_nonneg_left hra L.coe_nonneg]
  have hlog := malaLogRatio_abs_bound U h L hh hdiff hLip x y
  have hrej : malaRejectionDisplacement U h x ξ ≤
      (L : ℝ) * r ^ 3 + h * (L : ℝ) / 4 * r ^ 2 *
        (‖gradient U x‖ + ‖gradient U y‖) := by
    have h := (rejected_displacement_le (malaLogRatio U h x y) x y).trans
      (mul_le_mul_of_nonneg_left hlog hr)
    dsimp [malaRejectionDisplacement, y, r] at *
    nlinarith [h]
  have hhh : h ^ 2 ≤ h * s := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hhs hh.le
  have hcoef : (L : ℝ) + (L : ℝ) / 4 * (2 + (L : ℝ)) ≤ (L : ℝ) * (2 + (L : ℝ)) := by
    nlinarith [L.coe_nonneg, sq_nonneg (L : ℝ)]
  calc
    malaRejectionDisplacement U h x ξ ≤
        (L : ℝ) * r ^ 3 + h * (L : ℝ) / 4 * r ^ 2 *
          (‖gradient U x‖ + ‖gradient U y‖) := hrej
    _ ≤ (L : ℝ) * (s * a) ^ 3 + h * (L : ℝ) / 4 * (s * a) ^ 2 *
        ((2 + (L : ℝ)) * a) := by gcongr
    _ = (L : ℝ) * h * s * a ^ 3 + (L : ℝ) / 4 * (2 + (L : ℝ)) * h ^ 2 * a ^ 3 := by
      rw [mul_pow, pow_succ s 2, hs2, mul_pow, hs2]
      ring
    _ ≤ (L : ℝ) * h * s * a ^ 3 + (L : ℝ) / 4 * (2 + (L : ℝ)) * (h * s) * a ^ 3 := by
      gcongr
    _ ≤ h * Real.sqrt h * ((L : ℝ) * (2 + (L : ℝ)) * malaAmplitude U x ξ ^ 3) := by
      have hc := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ h * s * a ^ 3)
      dsimp [s, a] at *
      nlinarith [hc]

section Moments

variable [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

omit [CompleteSpace H] in
/-- A fourth-degree polynomial is integrable against every radial Gaussian. -/
theorem integrable_norm_fourth_mul_exp_neg_mul_norm_sq (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : H ↦ ‖x‖ ^ 4 * Real.exp (-a * ‖x‖ ^ 2)) volume := by
  let b := a / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hi := (integrable_exp_neg_mul_norm_sq (H := H) b hb).const_mul (2 / b ^ 2)
  refine hi.mono' (by fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : (b * ‖x‖ ^ 2) ^ 2 / 2 ≤ Real.exp (b * ‖x‖ ^ 2) := by
    simpa using Real.pow_div_factorial_le_exp (b * ‖x‖ ^ 2)
      (by positivity : 0 ≤ b * ‖x‖ ^ 2) 2
  have he : Real.exp (b * ‖x‖ ^ 2) * Real.exp (-a * ‖x‖ ^ 2) =
      Real.exp (-b * ‖x‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [b]
    ring
  have hp' : b ^ 2 * ‖x‖ ^ 4 * Real.exp (-a * ‖x‖ ^ 2) ≤
      2 * Real.exp (-b * ‖x‖ ^ 2) := by
    calc
      _ = (2 * ((b * ‖x‖ ^ 2) ^ 2 / 2)) * Real.exp (-a * ‖x‖ ^ 2) := by ring
      _ ≤ (2 * Real.exp (b * ‖x‖ ^ 2)) * Real.exp (-a * ‖x‖ ^ 2) := by gcongr
      _ = _ := by rw [mul_assoc, he]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hb)).mp
  calc
    b ^ 2 * (‖x‖ ^ 4 * Real.exp (-a * ‖x‖ ^ 2)) =
        b ^ 2 * ‖x‖ ^ 4 * Real.exp (-a * ‖x‖ ^ 2) := by ring
    _ ≤ 2 * Real.exp (-b * ‖x‖ ^ 2) := hp'
    _ = b ^ 2 * (2 / b ^ 2 * Real.exp (-b * ‖x‖ ^ 2)) := by field_simp

/-- Strong convexity gives a finite fourth unnormalized Gibbs moment. -/
theorem integrable_norm_fourth_mul_exp_neg_of_strongConvex
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    Integrable (fun x : H ↦ ‖x‖ ^ 4 * Real.exp (-U x)) volume := by
  let C := ‖gradient U 0‖ ^ 2 / m - U 0
  have hi := (integrable_norm_fourth_mul_exp_neg_mul_norm_sq (H := H) (m / 4)
    (by positivity)).const_mul (Real.exp C)
  refine hi.mono'
    (((continuous_norm.pow 4).mul
      (Real.continuous_exp.comp hdiff.continuous.neg)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    ‖x‖ ^ 4 * Real.exp (-U x) ≤
        ‖x‖ ^ 4 * Real.exp (C + -(m / 4) * ‖x‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have hs := strongConvex_quadratic_lower_bound U m hm hdiff hsc x
      dsimp [C]
      linarith
    _ = Real.exp C * (‖x‖ ^ 4 * Real.exp (-(m / 4) * ‖x‖ ^ 2)) := by
      rw [Real.exp_add]
      ring

/-- The fourth Gibbs moment is derived, never assumed. -/
theorem integrable_norm_fourth_gibbsMeasure
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    Integrable (fun x : H ↦ ‖x‖ ^ 4) (gibbsMeasure U) := by
  have hi : Integrable (fun x : H ↦ ‖x‖ ^ 4) (volume.withDensity (gibbsWeight U)) := by
    change Integrable (fun x : H ↦ ‖x‖ ^ 4)
      (volume.withDensity (fun x ↦ ENNReal.ofReal (Real.exp (-U x))))
    apply (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure H))
      (f := fun x ↦ ENNReal.ofReal (Real.exp (-U x)))
      (Real.continuous_exp.comp hdiff.continuous.neg).measurable.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mpr
    simpa only [smul_eq_mul, mul_comm,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using
      integrable_norm_fourth_mul_exp_neg_of_strongConvex U m hm hdiff hsc
  exact hi.smul_measure (ENNReal.inv_ne_top.mpr (ne_of_gt (gibbsPartition_pos U hdiff)))

/-- The cubic moment required by the rejection envelope follows from the
proved fourth Gibbs moment. -/
theorem memLp_three_id_gibbsMeasure
    (U : H → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    MemLp (fun x : H ↦ x) 3 (gibbsMeasure U) := by
  have := isProbabilityMeasure_gibbsMeasure U m hm hdiff hsc
  have h3 := integrable_norm_pow_of_le (f := fun x : H ↦ x) (by fun_prop)
    (by norm_num : (3 : ℕ) ≤ 4) (integrable_norm_fourth_gibbsMeasure U m hm hdiff hsc)
  apply (integrable_norm_rpow_iff (p := 3) (by fun_prop) (by norm_num) (by norm_num)).mp
  simpa using h3

/-- The joint law used to average the local rejection error: a Gibbs state
and an independent standard Gaussian proposal innovation. -/
def malaPairMeasure (U : H → ℝ) : Measure (H × H) :=
  (gibbsMeasure U).prod (stdGaussian H)

/-- The cubic amplitude envelope is squarely a consequence of the original
potential assumptions and the standard Gaussian law. -/
theorem malaAmplitude_memLp_three (U : H → ℝ) (m : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) :
    MemLp (fun p : H × H ↦ malaAmplitude U p.1 p.2) 3 (malaPairMeasure U) := by
  have := isProbabilityMeasure_gibbsMeasure U m hm hdiff hsc
  have hx := memLp_three_id_gibbsMeasure U m hm hdiff hsc
  have hcenter : MemLp (fun x ↦ gradient U x - gradient U 0) 3 (gibbsMeasure U) :=
    (centered_lipschitz hLip).comp_memLp (by simp) hx
  have hg : MemLp (gradient U) 3 (gibbsMeasure U) := by
    simpa only [Pi.add_def, sub_add_cancel] using
      hcenter.add (memLp_const (gradient U 0))
  have hg' := hg.comp_measurePreserving
    (measurePreserving_fst (μ := gibbsMeasure U) (ν := stdGaussian H))
  have hz : MemLp (fun ξ : H ↦ ξ) 3 (stdGaussian H) :=
    IsGaussian.memLp_id (stdGaussian H) 3 (by norm_num)
  have hz' := hz.comp_measurePreserving
    (measurePreserving_snd (μ := gibbsMeasure U) (ν := stdGaussian H))
  exact hg'.norm.add (hz'.norm.const_mul (Real.sqrt 2))

/-- The cubic rejection envelope has a finite ordinary integral. -/
theorem malaAmplitude_cube_integrable (U : H → ℝ) (m : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) :
    Integrable (fun p : H × H ↦ malaAmplitude U p.1 p.2 ^ 3) (malaPairMeasure U) := by
  have hi := (malaAmplitude_memLp_three U m L hm hdiff hsc hLip).integrable_norm_pow
    (by norm_num : (3 : ℕ) ≠ 0)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (malaAmplitude_nonneg U _ _)] using hi

/-- An explicit finite local-error constant, independent of the step length.
Its integrability is established by `malaAmplitude_cube_integrable`. -/
def malaRejectionConstant (U : H → ℝ) (L : ℝ≥0) : ℝ :=
  (L : ℝ) * (2 + (L : ℝ)) *
    ∫ p : H × H, malaAmplitude U p.1 p.2 ^ 3 ∂malaPairMeasure U

theorem malaRejectionConstant_nonneg (U : H → ℝ) (L : ℝ≥0) :
    0 ≤ malaRejectionConstant U L := by
  unfold malaRejectionConstant
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun p ↦ pow_nonneg (malaAmplitude_nonneg U p.1 p.2) 3

/-- The actual expected rejected displacement is integrable for every
positive step of length at most one. -/
theorem malaRejectionDisplacement_integrable (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 < h) (h1 : h ≤ 1)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) :
    Integrable (fun p : H × H ↦ malaRejectionDisplacement U h p.1 p.2)
      (malaPairMeasure U) := by
  have henv := ((malaAmplitude_cube_integrable U m L hm hdiff hsc hLip).const_mul
    ((L : ℝ) * (2 + (L : ℝ)))).const_mul (h * Real.sqrt h)
  have hU : Continuous U := hdiff.continuous
  have hg : Continuous (gradient U) := hLip.continuous
  have hmeas : Continuous (fun p : H × H ↦ malaRejectionDisplacement U h p.1 p.2) := by
    unfold malaRejectionDisplacement malaLogRatio malaProposal
    fun_prop
  refine henv.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (malaRejectionDisplacement_nonneg U h p.1 p.2)]
  exact malaRejectionDisplacement_pointwise U h L hh h1 hdiff hLip p.1 p.2

/-- The integrated MALA rejection error is `O(h^(3/2))` from the original
strong-convexity and Lipschitz-gradient assumptions. The constant is finite
and independent of the positive step length `h ≤ 1`. -/
theorem malaRejectionDisplacement_integral_bound (U : H → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hh : 0 < h) (h1 : h ≤ 1)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) :
    (∫ p : H × H, malaRejectionDisplacement U h p.1 p.2 ∂malaPairMeasure U) ≤
      malaRejectionConstant U L * h * Real.sqrt h := by
  have henv := ((malaAmplitude_cube_integrable U m L hm hdiff hsc hLip).const_mul
    ((L : ℝ) * (2 + (L : ℝ)))).const_mul (h * Real.sqrt h)
  have hb := integral_mono
    (malaRejectionDisplacement_integrable U m h L hm hh h1 hdiff hsc hLip) henv
    (fun p ↦ malaRejectionDisplacement_pointwise U h L hh h1 hdiff hLip p.1 p.2)
  simp only [integral_const_mul] at hb
  unfold malaRejectionConstant
  nlinarith [hb]

/-- A step-independent finite real constant controls all sufficiently small
MALA rejection errors. No moment or differentiability-of-gradient premise is
introduced beyond the displayed potential assumptions. -/
theorem exists_malaRejectionConstant (U : H → ℝ) (m : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∫ p : H × H, malaRejectionDisplacement U h p.1 p.2 ∂malaPairMeasure U) ≤
        C * h * Real.sqrt h :=
  ⟨malaRejectionConstant U L, malaRejectionConstant_nonneg U L,
    fun h hh h1 ↦ malaRejectionDisplacement_integral_bound U m h L hm hh h1 hdiff hsc hLip⟩

end Moments

end ULA
