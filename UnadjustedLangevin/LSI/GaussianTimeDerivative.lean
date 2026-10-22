import UnadjustedLangevin.LSI.GaussianEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option linter.style.header false

/-! # Time differentiation of the actual frozen Gaussian mixture

The normalizer is the reciprocal of the Gaussian integral used to define the
actual Gaussian proposal. Differentiating that integral's closed formula and
expanding the frozen Gaussian exponent gives an exact time derivative.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
/-- The normalizer of the actual Gaussian proposal, in closed form. -/
theorem gaussianProposalNormalizer_eq_rpow (t : ℝ) (ht : 0 < t) :
    ULA.gaussianProposalNormalizer (H := E) t =
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
  unfold ULA.gaussianProposalNormalizer ULA.radialGaussianNormalizer ULA.radialGaussianIntegral
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity : 0 < 1 / (4 * t))]
  have heq : Real.pi / (1 / (4 * t)) = 4 * Real.pi * t := by field_simp
  rw [heq]
  rw [show -(Module.finrank ℝ E : ℝ) / 2 = -((Module.finrank ℝ E : ℝ) / 2) by ring,
    Real.rpow_neg (by positivity)]

omit [CompleteSpace E] in
/-- Differentiation of the normalizer retains the actual Gaussian integral
normalization; no independent scalar prefactor is introduced. -/
theorem hasDerivAt_gaussianProposalNormalizer (t : ℝ) (ht : 0 < t) :
    HasDerivAt (ULA.gaussianProposalNormalizer (H := E))
      (-(Module.finrank ℝ E : ℝ) / (2 * t) * ULA.gaussianProposalNormalizer (H := E) t) t := by
  let p := -(Module.finrank ℝ E : ℝ) / 2
  have hp : 0 < 4 * Real.pi * t := by positivity
  have hd := ((hasDerivAt_id t).const_mul (4 * Real.pi)).rpow_const
    (p := p) (Or.inl hp.ne')
  have heq : ULA.gaussianProposalNormalizer (H := E) =ᶠ[𝓝 t]
      (fun s ↦ (4 * Real.pi * s) ^ p) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact gaussianProposalNormalizer_eq_rpow s hs
  have he : (4 * Real.pi * t) ^ (p - 1) = (4 * Real.pi * t) ^ p / (4 * Real.pi * t) := by
    rw [Real.rpow_sub hp, Real.rpow_one]
  have hder : p * (4 * Real.pi * t) ^ (p - 1) * (4 * Real.pi) =
      -(Module.finrank ℝ E : ℝ) / (2 * t) * ULA.gaussianProposalNormalizer (H := E) t := by
    rw [he, gaussianProposalNormalizer_eq_rpow t ht]
    dsimp [p]
    field_simp
  have hd' : HasDerivAt (fun s ↦ (4 * Real.pi * s) ^ p)
      (p * (4 * Real.pi * t) ^ (p - 1) * (4 * Real.pi)) t := by
    convert hd using 1
    · ext s; rfl
    · simp only [id_eq, mul_one]
      ring
  rw [hder] at hd'
  exact hd'.congr_of_eventuallyEq heq

/-- The ordinary real density of a fixed-state frozen Gaussian update. -/
def frozenGaussianKernel (U : E → ℝ) (t : ℝ) (x y : E) : ℝ :=
  ULA.gaussianProposalNormalizer (H := E) t *
    Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t))

/-- The exact ordinary time derivative of the frozen Gaussian kernel. -/
def frozenGaussianKernelDot (U : E → ℝ) (t : ℝ) (x y : E) : ℝ :=
  frozenGaussianKernel U t x y *
    (-(Module.finrank ℝ E : ℝ) / (2 * t) + ‖y - x‖ ^ 2 / (4 * t ^ 2) -
      ‖gradient U x‖ ^ 2 / 4)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem frozen_exponent_eq (U : E → ℝ) (s : ℝ) (hs : s ≠ 0) (x y : E) :
    -‖y - (x - s • gradient U x)‖ ^ 2 / (4 * s) =
      -(‖y - x‖ ^ 2 / 4) / s - inner ℝ (y - x) (gradient U x) / 2 -
        s * ‖gradient U x‖ ^ 2 / 4 := by
  have he : y - (x - s • gradient U x) = (y - x) + s • gradient U x := by module
  rw [he, norm_add_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp
  ring

/-- Exact time differentiation of every fixed-state Gaussian component. The
potential is frozen at the initial state, so no Hessian of `U` is needed. -/
theorem hasDerivAt_frozenGaussianKernel (U : E → ℝ) (t : ℝ) (ht : 0 < t) (x y : E) :
    HasDerivAt (fun s ↦ frozenGaussianKernel U s x y)
      (frozenGaussianKernelDot U t x y) t := by
  let A := ‖y - x‖ ^ 2 / 4
  let B := inner ℝ (y - x) (gradient U x) / 2
  let C := ‖gradient U x‖ ^ 2 / 4
  have hd : HasDerivAt (fun s : ℝ ↦ -A / s - B - s * C)
      (A / t ^ 2 - C) t := by
    have h := (((hasDerivAt_id t).inv ht.ne').const_mul (-A)).sub_const B
    have h' := h.sub ((hasDerivAt_id t).mul_const C)
    convert h' using 1
    · ext s; simp only [div_eq_mul_inv, Pi.sub_apply, Pi.inv_apply, id_eq]
    · simp only [id_eq, one_mul]
      ring
  have heq : (fun s ↦ -‖y - (x - s • gradient U x)‖ ^ 2 / (4 * s)) =ᶠ[𝓝 t]
      (fun s ↦ -A / s - B - s * C) := by
    filter_upwards [eventually_ne_nhds ht.ne'] with s hs
    simpa only [A, B, C, div_eq_mul_inv, mul_assoc] using frozen_exponent_eq U s hs x y
  have hexp := (hd.congr_of_eventuallyEq heq).exp
  have h := (hasDerivAt_gaussianProposalNormalizer (E := E) t ht).mul hexp
  convert h using 1
  · ext s; rfl
  · dsimp [frozenGaussianKernelDot, frozenGaussianKernel, A, B, C]
    rw [frozen_exponent_eq U t ht.ne' x y]
    ring


/-- A pointwise derivative envelope in the initial state. The Gaussian factor
absorbs the displacement; only the initial squared gradient remains. -/
theorem norm_frozenGaussianKernelDot_le (U : E → ℝ) (t : ℝ) (ht : 0 < t) (x y : E) :
    ‖frozenGaussianKernelDot U t x y‖ ≤
      ULA.gaussianProposalNormalizer (H := E) t *
        (((Module.finrank ℝ E : ℝ) + 4) / t + ‖gradient U x‖ ^ 2) := by
  let r := y - (x - t • gradient U x)
  let e := Real.exp (-‖r‖ ^ 2 / (4 * t))
  let A := (Module.finrank ℝ E : ℝ) / (2 * t)
  let B := ‖y - x‖ ^ 2 / (4 * t ^ 2)
  let C := ‖gradient U x‖ ^ 2 / 4
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
  have hcoeff : |-A + B - C| ≤ A + B + C := by
    apply abs_le.mpr
    constructor <;> linarith
  have hres : ‖r‖ ^ 2 * e ≤ 4 * t := by
    have h := norm_sq_mul_exp_neg_norm_sq_le (1 / (4 * t)) (by positivity) r
    have heq : -(1 / (4 * t)) * ‖r‖ ^ 2 = -‖r‖ ^ 2 / (4 * t) := by ring
    rw [heq] at h
    simpa only [one_div, inv_inv] using h
  have hdist : ‖y - x‖ ^ 2 ≤ 2 * ‖r‖ ^ 2 + 2 * t ^ 2 * ‖gradient U x‖ ^ 2 := by
    have hvec : y - x = r - t • gradient U x := by dsimp [r]; module
    have hn := norm_sub_le r (t • gradient U x)
    rw [← hvec, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hn
    nlinarith [sq_nonneg (‖r‖ - t * ‖gradient U x‖), norm_nonneg (y - x), norm_nonneg r,
      norm_nonneg (gradient U x)]
  have hdistmul : ‖y - x‖ ^ 2 * e ≤ 8 * t + 2 * t ^ 2 * ‖gradient U x‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hdist he0
    have h' := mul_le_mul_of_nonneg_left he1
      (by positivity : 0 ≤ 2 * t ^ 2 * ‖gradient U x‖ ^ 2)
    nlinarith
  have hscaled : e * (A + B + C) ≤
      ((Module.finrank ℝ E : ℝ) + 4) / t + ‖gradient U x‖ ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left he1 hA
    have hc := mul_le_mul_of_nonneg_left he1 hC
    have hb : B * e ≤ (8 * t + 2 * t ^ 2 * ‖gradient U x‖ ^ 2) / (4 * t ^ 2) := by
      dsimp [B]
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hdistmul (by positivity)
    have hn : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
    dsimp [A, B, C] at *
    have ht2 : 0 < 4 * t ^ 2 := by positivity
    field_simp at *
    nlinarith [mul_nonneg hn ht.le]
  have hformula : frozenGaussianKernelDot U t x y =
      ULA.gaussianProposalNormalizer (H := E) t * e * (-A + B - C) := by
    dsimp [frozenGaussianKernelDot, frozenGaussianKernel, e, r, A, B, C]
    ring
  rw [hformula, Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (ULA.gaussianProposalNormalizer_pos t ht),
    abs_of_pos (Real.exp_pos _), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (ULA.gaussianProposalNormalizer_pos t ht).le
  exact (mul_le_mul_of_nonneg_left hcoeff he0).trans hscaled


omit [CompleteSpace E] in
/-- Measurability of the actual Gaussian normalization at all real times. -/
theorem gaussianProposalNormalizer_measurable :
    Measurable (ULA.gaussianProposalNormalizer (H := E)) := by
  have hm : StronglyMeasurable (Function.uncurry (fun (t : ℝ) (z : E) ↦
      Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2))) := by fun_prop
  exact hm.integral_prod_right.measurable.inv

/-- Joint measurability of the exact component time derivative. -/
theorem frozenGaussianKernelDot_measurable (U : E → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U)) :
    Measurable (fun p : (ℝ × E) × E ↦ frozenGaussianKernelDot U p.1.1 p.2 p.1.2) := by
  have hg := hLip.continuous.measurable
  have hn := gaussianProposalNormalizer_measurable (E := E)
  unfold frozenGaussianKernelDot frozenGaussianKernel
  fun_prop

/-- The ordinary mixture of the exact component time derivatives. -/
def interpolationLebesgueDensityTimeDerivative
    (U : E → ℝ) (μ : Measure E) (t : ℝ) (y : E) : ℝ :=
  ∫ x, frozenGaussianKernelDot U t x y ∂μ

/-- Joint time-space measurability of the mixture time derivative. -/
theorem interpolationLebesgueDensityTimeDerivative_measurable
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U)) :
    Measurable (fun p : ℝ × E ↦ interpolationLebesgueDensityTimeDerivative U μ p.1 p.2) := by
  exact (frozenGaussianKernelDot_measurable U L hLip).stronglyMeasurable
    |>.integral_prod_right.measurable

/-- The actual mixture can be differentiated in time at every positive time.
A local majorant depends only on the initial squared gradient, whose
integrability is retained explicitly for this reusable analytic lemma. -/
theorem hasDerivAt_interpolationLebesgueDensity_time
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ)
    (t : ℝ) (ht : 0 < t) (y : E) :
    Integrable (fun x ↦ frozenGaussianKernelDot U t x y) μ ∧
      HasDerivAt (fun s ↦ interpolationLebesgueDensity U μ s y)
        (interpolationLebesgueDensityTimeDerivative U μ t y) t := by
  let N := ULA.gaussianProposalNormalizer (H := E)
  let b : E → ℝ := fun x ↦ (N t + 1) *
    (2 * ((Module.finrank ℝ E : ℝ) + 4) / t + ‖gradient U x‖ ^ 2)
  let S : Set ℝ := {s | t / 2 < s ∧ N s < N t + 1}
  have hN : ∀ᶠ s in 𝓝 t, N s < N t + 1 :=
    (hasDerivAt_gaussianProposalNormalizer (E := E) t ht).continuousAt.eventually
      (Iio_mem_nhds (lt_add_one (N t)))
  have hS : S ∈ 𝓝 t := (eventually_gt_nhds (by linarith : t / 2 < t)).and hN
  have hmeas : ∀ s : ℝ, AEStronglyMeasurable (fun x ↦ frozenGaussianKernel U s x y) μ := by
    intro s
    have hg := hLip.continuous
    unfold frozenGaussianKernel
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  have hpos : 0 < N t := ULA.gaussianProposalNormalizer_pos t ht
  have hint : Integrable (fun x ↦ frozenGaussianKernel U t x y) μ := by
    apply (integrable_const (N t)).mono' (hmeas t)
    filter_upwards [] with x
    change |N t * Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t))| ≤ N t
    rw [abs_of_pos (by positivity)]
    have he : Real.exp (-‖y - (x - t • gradient U x)‖ ^ 2 / (4 * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by positivity))
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he hpos.le
  have hdotmeas : AEStronglyMeasurable (fun x ↦ frozenGaussianKernelDot U t x y) μ := by
    have hg := hLip.continuous
    unfold frozenGaussianKernelDot frozenGaussianKernel
    exact (by fun_prop : Continuous _).aestronglyMeasurable
  have hb : Integrable b μ := by
    simpa only [b, Pi.add_def] using
      ((integrable_const (2 * ((Module.finrank ℝ E : ℝ) + 4) / t)).add hG).const_mul (N t + 1)
  have hbound : ∀ x : E, ∀ s ∈ S, ‖frozenGaussianKernelDot U s x y‖ ≤ b x := by
    intro x s hs
    have hspos : 0 < s := lt_trans (by positivity : 0 < t / 2) hs.1
    have hdim : 0 ≤ (Module.finrank ℝ E : ℝ) + 4 := by positivity
    have htime : ((Module.finrank ℝ E : ℝ) + 4) / s ≤
        2 * ((Module.finrank ℝ E : ℝ) + 4) / t := by
      apply (div_le_div_iff₀ hspos ht).mpr
      have hh := mul_le_mul_of_nonneg_left hs.1.le hdim
      nlinarith
    calc
      _ ≤ N s * (((Module.finrank ℝ E : ℝ) + 4) / s + ‖gradient U x‖ ^ 2) :=
        norm_frozenGaussianKernelDot_le U s hspos x y
      _ ≤ b x := by
        change N s * _ ≤ (N t + 1) * _
        apply mul_le_mul hs.2.le (add_le_add htime le_rfl)
        · positivity
        · linarith [hpos]
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun s x ↦ frozenGaussianKernel U s x y)
    (F' := fun s x ↦ frozenGaussianKernelDot U s x y) (bound := b)
    hS (Eventually.of_forall hmeas) hint hdotmeas (ae_of_all _ hbound) hb
    (ae_of_all _ fun x s hs ↦ hasDerivAt_frozenGaussianKernel U s
      (lt_trans (by positivity : 0 < t / 2) hs.1) x y)
  have heq : (fun s ↦ interpolationLebesgueDensity U μ s y) =ᶠ[𝓝 t]
      (fun s ↦ ∫ x, frozenGaussianKernel U s x y ∂μ) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact interpolationLebesgueDensity_eq_integral U μ L hLip s hs y
  exact ⟨hresult.1, hresult.2.congr_of_eventuallyEq heq⟩


/-- Identification with the spatial Gaussian kernel used in the Fisher proof. -/
theorem frozenGaussianKernel_eq_realGaussianKernel (U : E → ℝ) (t : ℝ) (x y : E) :
    frozenGaussianKernel U t x y =
      realGaussianKernel (1 / (4 * t)) (x - t • gradient U x) y := by
  unfold frozenGaussianKernel realGaussianKernel ULA.gaussianProposalNormalizer
  congr 2
  ring

/-- A Gaussian-weighted envelope that remains integrable in both the initial
state and the output state. -/
theorem norm_frozenGaussianKernelDot_le_weighted
    (U : E → ℝ) (t : ℝ) (ht : 0 < t) (x y : E) :
    ‖frozenGaussianKernelDot U t x y‖ ≤ frozenGaussianKernel U t x y *
      ((Module.finrank ℝ E : ℝ) / (2 * t) +
        ‖y - (x - t • gradient U x)‖ ^ 2 / (2 * t ^ 2) + ‖gradient U x‖ ^ 2) := by
  let r := y - (x - t • gradient U x)
  have hvec : y - x = r - t • gradient U x := by dsimp [r]; module
  have hn := norm_sub_le r (t • gradient U x)
  rw [← hvec, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hn
  have hdist : ‖y - x‖ ^ 2 ≤ 2 * ‖r‖ ^ 2 + 2 * t ^ 2 * ‖gradient U x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖r‖ - t * ‖gradient U x‖), norm_nonneg (y - x), norm_nonneg r,
      norm_nonneg (gradient U x)]
  have hcoeff : |-(Module.finrank ℝ E : ℝ) / (2 * t) +
      ‖y - x‖ ^ 2 / (4 * t ^ 2) - ‖gradient U x‖ ^ 2 / 4| ≤
      (Module.finrank ℝ E : ℝ) / (2 * t) +
        ‖r‖ ^ 2 / (2 * t ^ 2) + ‖gradient U x‖ ^ 2 := by
    simp only [neg_div]
    apply abs_le.mpr
    have hdim : 0 ≤ (Module.finrank ℝ E : ℝ) / (2 * t) := by positivity
    have hdis : ‖y - x‖ ^ 2 / (4 * t ^ 2) ≤
        ‖r‖ ^ 2 / (2 * t ^ 2) + ‖gradient U x‖ ^ 2 / 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * t ^ 2)).mpr
      field_simp
      nlinarith [hdist]
    have hdis0 : 0 ≤ ‖y - x‖ ^ 2 / (4 * t ^ 2) := by positivity
    constructor <;> nlinarith [sq_nonneg ‖gradient U x‖,
      div_nonneg (sq_nonneg ‖r‖) (by positivity : 0 ≤ 2 * t ^ 2)]
  have hK : 0 ≤ frozenGaussianKernel U t x y := by
    exact mul_nonneg (ULA.gaussianProposalNormalizer_pos t ht).le (Real.exp_nonneg _)
  unfold frozenGaussianKernelDot
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hK, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hcoeff hK

/-- A common Gaussian-weighted energy envelope. -/
def frozenGaussianEnergy (U : E → ℝ) (t : ℝ) (x y : E) : ℝ :=
  frozenGaussianKernel U t x y *
    (1 + ‖gradient U x‖ ^ 2 + ‖y - (x - t • gradient U x)‖ ^ 2)

private theorem frozenGaussianEnergy_nonneg (U : E → ℝ) (t : ℝ) (ht : 0 < t) (x y : E) :
    0 ≤ frozenGaussianEnergy U t x y := by
  exact mul_nonneg (mul_nonneg (ULA.gaussianProposalNormalizer_pos t ht).le
    (Real.exp_nonneg _)) (by positivity)

/-- Integration over one component removes the Gaussian exactly. -/
theorem frozenGaussianEnergy_integral (U : E → ℝ) (t : ℝ) (ht : 0 < t) (x : E) :
    Integrable (frozenGaussianEnergy U t x) volume ∧
      (∫ y, frozenGaussianEnergy U t x y) =
        1 + ‖gradient U x‖ ^ 2 + 2 * t * (Module.finrank ℝ E : ℝ) := by
  have hK : Integrable (frozenGaussianKernel U t x) volume := by
    change Integrable (fun y ↦ frozenGaussianKernel U t x y) volume
    simp_rw [frozenGaussianKernel_eq_realGaussianKernel]
    unfold realGaussianKernel
    exact ULA.integrable_radialGaussianDensity_real _ (by positivity) _
  have hKi : (∫ y, frozenGaussianKernel U t x y) = 1 := by
    simp_rw [frozenGaussianKernel_eq_realGaussianKernel]
    unfold realGaussianKernel
    exact ULA.integral_radialGaussianDensity_real _ (by positivity) _
  have hmoment := realGaussianKernel_displacement_moment t ht (x - t • gradient U x)
  simp_rw [← frozenGaussianKernel_eq_realGaussianKernel] at hmoment
  have hfun : frozenGaussianEnergy U t x = (frozenGaussianKernel U t x) +
      (fun y ↦ frozenGaussianKernel U t x y * ‖gradient U x‖ ^ 2) +
      (fun y ↦ frozenGaussianKernel U t x y * ‖y - (x - t • gradient U x)‖ ^ 2) := by
    ext y
    dsimp [frozenGaussianEnergy]
    ring
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact (hK.add (hK.mul_const _)).add hmoment.1
  · rw [hfun]
    simp only [Pi.add_def]
    rw [integral_add (by simpa only [Pi.add_def] using hK.add (hK.mul_const _)) hmoment.1,
      integral_add hK (hK.mul_const _), integral_mul_const, hKi, one_mul, hmoment.2]

/-- Joint integrability in the initial state and the output state. Only the
initial squared gradient, rather than a position moment, is required. -/
theorem integrable_frozenGaussianEnergy
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun p : E × E ↦ frozenGaussianEnergy U t p.1 p.2) (μ.prod volume) := by
  have hg := hLip.continuous
  apply (integrable_prod_iff (by unfold frozenGaussianEnergy frozenGaussianKernel; fun_prop)).mpr
  refine ⟨ae_of_all _ fun x ↦ (frozenGaussianEnergy_integral U t ht x).1, ?_⟩
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (frozenGaussianEnergy_nonneg U t ht _ _),
    (frozenGaussianEnergy_integral U t ht _).2]
  simpa only [Pi.add_def] using ((integrable_const 1).add hG).add
    (integrable_const (2 * t * (Module.finrank ℝ E : ℝ)))

/-- The exact product integral of the common energy envelope. -/
theorem integral_frozenGaussianEnergy
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (t : ℝ) (ht : 0 < t) :
    (∫ p : E × E, frozenGaussianEnergy U t p.1 p.2 ∂μ.prod volume) =
      1 + (∫ x, ‖gradient U x‖ ^ 2 ∂μ) + 2 * t * (Module.finrank ℝ E : ℝ) := by
  rw [integral_prod _ (integrable_frozenGaussianEnergy U μ L hLip hG t ht)]
  simp_rw [(frozenGaussianEnergy_integral U t ht _).2]
  rw [integral_add (by simpa only [Pi.add_def] using (integrable_const 1).add hG)
    (integrable_const _), integral_add (integrable_const 1) hG]
  simp


/-- A positive scalar coefficient on every compact interval away from zero. -/
def gaussianTimeCoefficient (t : ℝ) : ℝ :=
  (Module.finrank ℝ E : ℝ) / (2 * t) + 1 / (2 * t ^ 2) + 1

/-- Domination of the exact time derivative by the common joint energy. -/
theorem norm_frozenGaussianKernelDot_le_energy (U : E → ℝ) (t : ℝ)
    (ht : 0 < t) (x y : E) :
    ‖frozenGaussianKernelDot U t x y‖ ≤
      gaussianTimeCoefficient (E := E) t * frozenGaussianEnergy U t x y := by
  have h := norm_frozenGaussianKernelDot_le_weighted U t ht x y
  let A := (Module.finrank ℝ E : ℝ) / (2 * t)
  let B := 1 / (2 * t ^ 2)
  let R := ‖y - (x - t • gradient U x)‖ ^ 2
  let G := ‖gradient U x‖ ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R := sq_nonneg _
  have hG : 0 ≤ G := sq_nonneg _
  have hc : A + B * R + G ≤ (A + B + 1) * (1 + G + R) := by
    have h₁ : A ≤ A + B + 1 := by linarith
    have h₂ : B ≤ A + B + 1 := by linarith
    have h₃ : 1 ≤ A + B + 1 := by linarith
    calc
      _ ≤ (A + B + 1) + (A + B + 1) * R + (A + B + 1) * G := by
        exact add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_right h₂ hR))
          (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h₃ hG)
      _ = _ := by ring
  calc
    _ ≤ frozenGaussianKernel U t x y * (A + B * R + G) := by
      convert h using 1
      dsimp [A, B, R, G]
      ring
    _ ≤ frozenGaussianKernel U t x y * ((A + B + 1) * (1 + G + R)) :=
      mul_le_mul_of_nonneg_left hc
        (mul_nonneg (ULA.gaussianProposalNormalizer_pos t ht).le (Real.exp_nonneg _))
    _ = _ := by dsimp [gaussianTimeCoefficient, frozenGaussianEnergy, A, B, R, G]; ring

/-- The exact component time derivative is jointly integrable in the initial
and proposed states. This is the Fubini input for the weak time equation. -/
theorem integrable_frozenGaussianKernelDot
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun p : E × E ↦ frozenGaussianKernelDot U t p.1 p.2) (μ.prod volume) := by
  apply ((integrable_frozenGaussianEnergy U μ L hLip hG t ht).const_mul
    (gaussianTimeCoefficient (E := E) t)).mono'
  · have hg := hLip.continuous
    unfold frozenGaussianKernelDot frozenGaussianKernel
    fun_prop
  · exact ae_of_all _ fun p ↦ norm_frozenGaussianKernelDot_le_energy U t ht p.1 p.2

/-- Spatial L¹ integrability of the actual density time derivative, with an
explicit finite Gaussian-moment bound. The coefficient is deliberately
nonsharp; the entropy argument only needs local integrability in time. -/
theorem integrable_interpolationLebesgueDensityTimeDerivative
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ) (t : ℝ) (ht : 0 < t) :
    Integrable (interpolationLebesgueDensityTimeDerivative U μ t) volume ∧
      (∫ y, ‖interpolationLebesgueDensityTimeDerivative U μ t y‖) ≤
        gaussianTimeCoefficient (E := E) t *
          (1 + (∫ x, ‖gradient U x‖ ^ 2 ∂μ) + 2 * t * (Module.finrank ℝ E : ℝ)) := by
  have hprod := integrable_frozenGaussianKernelDot U μ L hLip hG t ht
  have hi : Integrable (interpolationLebesgueDensityTimeDerivative U μ t) volume :=
    hprod.integral_prod_right
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y, ∫ x, ‖frozenGaussianKernelDot U t x y‖ ∂μ := by
      apply integral_mono hi.norm hprod.norm.integral_prod_right
      intro y
      exact norm_integral_le_integral_norm _
    _ = ∫ p : E × E, ‖frozenGaussianKernelDot U t p.1 p.2‖ ∂μ.prod volume := by
      rw [← integral_integral_swap (μ := μ) (ν := volume)
        (f := fun x y ↦ ‖frozenGaussianKernelDot U t x y‖) hprod.norm]
      exact (integral_prod _ hprod.norm).symm
    _ ≤ ∫ p : E × E, gaussianTimeCoefficient (E := E) t *
        frozenGaussianEnergy U t p.1 p.2 ∂μ.prod volume := by
      exact integral_mono hprod.norm
        ((integrable_frozenGaussianEnergy U μ L hLip hG t ht).const_mul _)
        (fun p ↦ norm_frozenGaussianKernelDot_le_energy U t ht p.1 p.2)
    _ = _ := by
      rw [integral_const_mul, integral_frozenGaussianEnergy U μ L hLip hG t ht]

/-- The mixture derivative is L¹ jointly in time and space on every closed
positive-time interval. This provides the spacetime Fubini input to the
entropy chain rule. -/
theorem integrable_interpolationLebesgueDensityTimeDerivative_spacetime
    (U : E → ℝ) (μ : Measure E) [IsProbabilityMeasure μ]
    (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (hG : Integrable (fun x ↦ ‖gradient U x‖ ^ 2) μ)
    (a b : ℝ) (ha : 0 < a) :
    Integrable (fun p : ℝ × E ↦ interpolationLebesgueDensityTimeDerivative U μ p.1 p.2)
      ((volume.restrict (Icc a b)).prod volume) := by
  let C := gaussianTimeCoefficient (E := E) a *
    (1 + (∫ x, ‖gradient U x‖ ^ 2 ∂μ) + 2 * b * (Module.finrank ℝ E : ℝ))
  have hm := (interpolationLebesgueDensityTimeDerivative_measurable U μ L hLip).stronglyMeasurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (integrable_interpolationLebesgueDensityTimeDerivative U μ L hLip hG t
      (lt_of_lt_of_le ha ht.1)).1
  · apply (integrable_const C).mono' hm.norm.integral_prod_right.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have htpos : 0 < t := lt_of_lt_of_le ha ht.1
    have hbound := (integrable_interpolationLebesgueDensityTimeDerivative U μ L hLip hG t htpos).2
    have hcoeff : gaussianTimeCoefficient (E := E) t ≤ gaussianTimeCoefficient (E := E) a := by
      unfold gaussianTimeCoefficient
      have hd : (0 : ℝ) ≤ Module.finrank ℝ E := Nat.cast_nonneg _
      gcongr <;> exact ht.1
    have hmom : 1 + (∫ x, ‖gradient U x‖ ^ 2 ∂μ) + 2 * t * (Module.finrank ℝ E : ℝ) ≤
        1 + (∫ x, ‖gradient U x‖ ^ 2 ∂μ) + 2 * b * (Module.finrank ℝ E : ℝ) := by
      gcongr
      exact ht.2
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    apply hbound.trans
    exact mul_le_mul hcoeff hmom (by positivity) (by unfold gaussianTimeCoefficient; positivity)

end ULA.LSI
