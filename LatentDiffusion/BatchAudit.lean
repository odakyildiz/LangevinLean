import UnadjustedLangevin.GaussianMoments
import Mathlib.Data.Finset.Powerset

/-!
# Exact mini-batch noise and temperature audit

For one fixed datum, a uniform batch of size B among M data has inclusion
probability p = B/M. Algorithm 1 uses an inverse-inclusion drift h/p when the
datum is selected, but adds Gaussian noise of variance 2hp to every particle.
The calculations below integrate the actual standard Gaussian; no diffusion
limit or invariant-law assumption is used. In particular, the source's claimed
variance matching fails even for the one-dimensional quadratic potential.

The scalar moment chains are defined recursions, derived from the exact
one-step conditional Gaussian moment. They do not assert existence or
convergence of a nonlinear adaptive Adam sampler.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatentDiffusion.BatchAudit

/-- Expectation over a Bernoulli selection of marginal probability `p`. -/
def selectionAverage (p : ℝ) (f : Bool → ℝ) : ℝ :=
  (1 - p) * f false + p * f true

/-- The exact inverse-inclusion drift used by the paper's mini-batch update. -/
def selectedDrift (p h g : ℝ) (selected : Bool) : ℝ :=
  if selected then -(h / p) * g else 0

/-- Inverse-inclusion scaling gives the full drift in expectation. -/
theorem selectedDrift_unbiased (p h g : ℝ) (hp : p ≠ 0) :
    selectionAverage p (selectedDrift p h g) = -h * g := by
  simp [selectionAverage, selectedDrift]
  field_simp

/-- Actual Gaussian conditional second moment, with specified noise variance. -/
def gaussianSecondMoment (center variance : ℝ) : ℝ :=
  ∫ w : ℝ, (center + Real.sqrt variance * w) ^ 2 ∂gaussianReal 0 1

/-- The Gaussian integration is proved from its first two moments. -/
theorem gaussianSecondMoment_eq (center variance : ℝ) (hv : 0 ≤ variance) :
    gaussianSecondMoment center variance = center ^ 2 + variance := by
  have hw : MemLp (fun w : ℝ ↦ w) 2 (gaussianReal 0 1) :=
    memLp_id_gaussianReal (2 : ℝ≥0)
  have hwi : Integrable (fun w : ℝ ↦ w) (gaussianReal 0 1) :=
    hw.integrable (by norm_num)
  have hws : Integrable (fun w : ℝ ↦ w ^ 2) (gaussianReal 0 1) := hw.integrable_sq
  have heq (w : ℝ) :
      (center + Real.sqrt variance * w) ^ 2 =
        center ^ 2 + (2 * center * Real.sqrt variance) * w + variance * w ^ 2 := by
    nlinarith [Real.sq_sqrt hv]
  unfold gaussianSecondMoment
  simp_rw [heq]
  have hc : Integrable (fun _ : ℝ ↦ center ^ 2) (gaussianReal 0 1) := integrable_const _
  have hl : Integrable (fun w : ℝ ↦ (2 * center * Real.sqrt variance) * w)
      (gaussianReal 0 1) := hwi.const_mul _
  have hq : Integrable (fun w : ℝ ↦ variance * w ^ 2) (gaussianReal 0 1) :=
    hws.const_mul _
  have hadd := integral_add (hc.add hl) hq
  have hadd' := integral_add hc hl
  simp only [Pi.add_apply] at hadd hadd'
  rw [hadd, hadd']
  have hlinear : (∫ w : ℝ, (2 * center * Real.sqrt variance) * w
      ∂gaussianReal 0 1) = 0 := by
    rw [integral_const_mul]
    have hmean : (∫ w : ℝ, w ∂gaussianReal 0 1) = 0 := integral_id_gaussianReal
    rw [hmean, mul_zero]
  rw [hlinear]
  simp [integral_const_mul, ULA.centered_gaussian_second_moment]

/-- The paper noises every particle with variance `2hp`, even if unselected. -/
def paperConditionalSecondMoment (p h a x : ℝ) : ℝ :=
  selectionAverage p (fun selected ↦
    gaussianSecondMoment (x + selectedDrift p h (a * x) selected) (2 * h * p))

/-- Exact moment of Algorithm 1 for the quadratic potential `a x²/2`. -/
theorem paperConditionalSecondMoment_eq (p h a x : ℝ)
    (hp : 0 < p) (hh : 0 ≤ h) :
    paperConditionalSecondMoment p h a x =
      (1 - 2 * a * h + a ^ 2 * h ^ 2 / p) * x ^ 2 + 2 * h * p := by
  unfold paperConditionalSecondMoment selectionAverage
  simp only [selectedDrift, Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [gaussianSecondMoment_eq _ _ (by positivity),
    gaussianSecondMoment_eq _ _ (by positivity)]
  field_simp
  <;> ring

/-- The exact second-moment contraction coefficient of the paper update. -/
def paperCoefficient (p h a : ℝ) : ℝ := 1 - 2 * a * h + a ^ 2 * h ^ 2 / p

/-- The stability interval is explicit: the scalar moment coefficient is in `[0,1)`. -/
theorem paperCoefficient_stable (p h a : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (ha : 0 < a) (hh : 0 < h) (hstep : a * h < 2 * p) :
    0 ≤ paperCoefficient p h a ∧ paperCoefficient p h a < 1 := by
  have hid : paperCoefficient p h a = (1 - p) + p * (1 - a * h / p) ^ 2 := by
    unfold paperCoefficient
    field_simp
    <;> ring
  constructor
  · rw [hid]
    positivity
  · unfold paperCoefficient
    have hquad : a ^ 2 * h ^ 2 / p < 2 * a * h := by
      apply (div_lt_iff₀ hp).mpr
      nlinarith [mul_pos (mul_pos ha hh) (sub_pos.mpr hstep)]
    linarith

/-- Actual iterated Gaussian integral with a centered Gaussian initial law. -/
theorem paper_gaussian_initial_second_moment (p h a : ℝ) (v : ℝ≥0)
    (hp : 0 < p) (hh : 0 ≤ h) :
    (∫ x : ℝ, paperConditionalSecondMoment p h a x ∂gaussianReal 0 v) =
      paperCoefficient p h a * (v : ℝ) + 2 * h * p := by
  simp_rw [paperConditionalSecondMoment_eq p h a _ hp hh]
  have hsq : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (2 : ℝ≥0)).integrable_sq
  have hc : Integrable (fun _ : ℝ ↦ 2 * h * p) (gaussianReal 0 v) :=
    integrable_const _
  rw [integral_add (hsq.const_mul _) hc]
  simp [integral_const_mul, ULA.centered_gaussian_second_moment, paperCoefficient]

/-- The source target loses second moment for every sufficiently small positive step
whenever the batch is a strict subset of the data. -/
theorem paper_small_step_target_moment_decreases (p h a : ℝ)
    (hp : 0 < p) (ha : 0 < a) (hh : 0 < h)
    (hstep : a * h < 2 * p * (1 - p)) :
    paperCoefficient p h a * (1 / a) + 2 * h * p < 1 / a := by
  have hid : paperCoefficient p h a * (1 / a) + 2 * h * p - 1 / a =
      (h / p) * (a * h - 2 * p * (1 - p)) := by
    unfold paperCoefficient
    field_simp
    <;> ring
  have hn : (h / p) * (a * h - 2 * p * (1 - p)) < 0 :=
    mul_neg_of_pos_of_neg (div_pos hh hp) (sub_neg.mpr hstep)
  linarith

/-- A scalar affine moment chain, independent of any assumed final bound. -/
def momentChain (q b v₀ : ℝ) : ℕ → ℝ
  | 0 => v₀
  | n + 1 => q * momentChain q b v₀ n + b

/-- Every time step has an exact, explicit transient about any fixed point. -/
theorem momentChain_closed (q b v₀ v : ℝ) (hfixed : q * v + b = v) (n : ℕ) :
    momentChain q b v₀ n = v + q ^ n * (v₀ - v) := by
  induction n with
  | zero => simp [momentChain]
  | succ n ih =>
    simp only [momentChain, ih, pow_succ]
    nlinarith [hfixed]

/-- Stationary second moment of the source mini-batch update. -/
def paperStationaryMoment (p h a : ℝ) : ℝ :=
  p / (a * (1 - a * h / (2 * p)))

/-- The source's stationary moment includes the mini-batch temperature `p`. -/
theorem paperStationaryMoment_fixed (p h a : ℝ) (hp : p ≠ 0) (ha : a ≠ 0)
    (hs : 1 - a * h / (2 * p) ≠ 0) :
    paperCoefficient p h a * paperStationaryMoment p h a + 2 * h * p =
      paperStationaryMoment p h a := by
  unfold paperCoefficient paperStationaryMoment
  field_simp [hp] at hs
  have hd : -(a * h) + p * 2 ≠ 0 := by
    intro hz
    apply hs
    have hz' : 2 * p - a * h = 0 := by linarith
    rw [hz', zero_div]
  rw [show 1 - a * h / (2 * p) = (2 * p - a * h) / (2 * p) by
    field_simp [hp]
    <;> ring]
  have hd' : 2 * p - a * h ≠ 0 := by convert hd using 1 <;> ring
  field_simp [hp, ha, hd']
  <;> ring

/-- Exact all-iteration second-moment formula for the source scalar scheme. -/
theorem paper_moment_all_iterations (p h a v₀ : ℝ)
    (hp : p ≠ 0) (ha : a ≠ 0) (hs : 1 - a * h / (2 * p) ≠ 0) (n : ℕ) :
    momentChain (paperCoefficient p h a) (2 * h * p) v₀ n =
      paperStationaryMoment p h a + (paperCoefficient p h a) ^ n *
        (v₀ - paperStationaryMoment p h a) :=
  momentChain_closed _ _ _ _ (paperStationaryMoment_fixed p h a hp ha hs) n

/-- Starting at target variance one, a half-batch changes it to `7/8` in one step.
Thus the target is not invariant for the source algorithm. -/
theorem paper_half_batch_counterexample :
    momentChain (paperCoefficient (1 / 2) (1 / 4) 1)
      (2 * (1 / 4) * (1 / 2)) 1 1 = 7 / 8 ∧
    paperStationaryMoment (1 / 2) (1 / 4) 1 = 2 / 3 := by
  norm_num [momentChain, paperCoefficient, paperStationaryMoment]

/-- A direct target-law counterexample: two Gaussian integrals and the Bernoulli
average give `7/8`, so the intended standard Gaussian cannot be invariant. -/
theorem paper_gaussian_target_not_invariant :
    (∫ x : ℝ, paperConditionalSecondMoment (1 / 2) (1 / 4) 1 x
      ∂gaussianReal 0 1) = 7 / 8 ∧ (7 / 8 : ℝ) ≠ 1 := by
  constructor
  · rw [paper_gaussian_initial_second_moment (1 / 2) (1 / 4) 1 1
      (by norm_num) (by norm_num)]
    norm_num [paperCoefficient]
  · norm_num

/-- Constant-temperature Euler–Maruyama moment update. -/
def eulerMoment (a h temperature v : ℝ) : ℝ :=
  (1 - a * h) ^ 2 * v + 2 * h * temperature

/-- Exact stationary variance of scalar Euler–Maruyama at temperature `τ`. -/
theorem euler_stationary_variance (a h τ : ℝ) (ha : a ≠ 0)
    (hh : 1 - a * h / 2 ≠ 0) :
    eulerMoment a h τ (τ / (a * (1 - a * h / 2))) =
      τ / (a * (1 - a * h / 2)) := by
  unfold eulerMoment
  field_simp at hh
  have hd : 2 - a * h ≠ 0 := by
    intro hz
    apply hh
    rw [hz, zero_div]
  field_simp [ha, hd]
  <;> ring

/-- A corrected random-scan update selects BOTH uninflated drift and noise. -/
def randomScanConditionalSecondMoment (p h a x : ℝ) : ℝ :=
  (1 - p) * x ^ 2 + p * gaussianSecondMoment ((1 - a * h) * x) (2 * h)

/-- Random scan preserves the full-batch temperature: both changes have rate `p`. -/
theorem randomScanConditionalSecondMoment_eq (p h a x : ℝ) (hh : 0 ≤ h) :
    randomScanConditionalSecondMoment p h a x =
      (1 - 2 * p * a * h + p * a ^ 2 * h ^ 2) * x ^ 2 + 2 * p * h := by
  unfold randomScanConditionalSecondMoment
  rw [gaussianSecondMoment_eq _ _ (by positivity)]
  ring

/-- The corrected random-scan stationary second moment has no temperature `p`. -/
theorem randomScan_stationary_variance (p h a : ℝ) (ha : a ≠ 0)
    (hs : 1 - a * h / 2 ≠ 0) :
    (1 - 2 * p * a * h + p * a ^ 2 * h ^ 2) *
        (1 / (a * (1 - a * h / 2))) + 2 * p * h =
      1 / (a * (1 - a * h / 2)) := by
  field_simp at hs
  have hd : 2 - a * h ≠ 0 := by
    intro hz
    apply hs
    rw [hz, zero_div]
  field_simp [ha, hd]
  <;> ring

/-- Alternative correction: retain inverse-inclusion drift and full noise. -/
def fullNoiseConditionalSecondMoment (p h a x : ℝ) : ℝ :=
  selectionAverage p (fun selected ↦
    gaussianSecondMoment (x + selectedDrift p h (a * x) selected) (2 * h))

/-- Full noise restores temperature one, while random drift keeps a `1/p` cost. -/
theorem fullNoiseConditionalSecondMoment_eq (p h a x : ℝ)
    (hp : 0 < p) (hh : 0 ≤ h) :
    fullNoiseConditionalSecondMoment p h a x =
      paperCoefficient p h a * x ^ 2 + 2 * h := by
  unfold fullNoiseConditionalSecondMoment selectionAverage paperCoefficient
  simp only [selectedDrift, Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [gaussianSecondMoment_eq _ _ (by positivity),
    gaussianSecondMoment_eq _ _ (by positivity)]
  field_simp
  <;> ring

/-- The stationary variance for inverse-inclusion drift and corrected full noise. -/
theorem fullNoise_stationary_variance (p h a : ℝ)
    (hp : p ≠ 0) (ha : a ≠ 0) (hs : 1 - a * h / (2 * p) ≠ 0) :
    paperCoefficient p h a * (1 / (a * (1 - a * h / (2 * p)))) + 2 * h =
      1 / (a * (1 - a * h / (2 * p))) := by
  unfold paperCoefficient
  field_simp [hp] at hs
  have hd : -(a * h) + p * 2 ≠ 0 := by
    intro hz
    apply hs
    have hz' : 2 * p - a * h = 0 := by linarith
    rw [hz', zero_div]
  rw [show 1 - a * h / (2 * p) = (2 * p - a * h) / (2 * p) by
    field_simp [hp]
    <;> ring]
  have hd' : 2 * p - a * h ≠ 0 := by convert hd using 1 <;> ring
  field_simp [hp, ha, hd']
  <;> ring

end LatentDiffusion.BatchAudit
