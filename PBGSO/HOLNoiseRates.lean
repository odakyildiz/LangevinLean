import PBGSO.HOLNoise
import PBGSO.HigherOrderRates

/-! # Explicit Brownian noise coupling rate for HOL-MYPGD

The noise is constructed on the actual canonical Brownian source in
`HOLNoise`. The coefficient estimates give a derived `h sqrt(h)` local
coupling error against an Euler step driven by the same Brownian increment.
The vector dimension factor is exactly `sqrt(card ι)`.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO.Methods
open KineticLangevin KineticLangevin.BrownianConvolution

/-- Explicit scalar noise-coupling constant, with no unknown covariance
or innovation remainder parameter. -/
def holScalarNoiseConstant (α γ : ℝ) : ℝ :=
  Real.sqrt (2 * α) * (γ / 2 + γ + α + (holRemainderConstants α γ).μ33)

/-- The implemented middle response is bounded linearly in elapsed time. -/
theorem hol_mu23_bound (α γ s : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ) (hs : 0 ≤ s) :
    |(holCoefficients α γ s).μ23| ≤ γ * s := by
  have he : Real.exp (-α * s) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he' := Real.add_one_le_exp (-α * s)
  have hc : 0 ≤ γ / α := div_nonneg hγ hα.le
  have hmul := mul_le_mul_of_nonneg_left
    (show 1 - Real.exp (-α * s) ≤ α * s by linarith) hc
  dsimp [holCoefficients]
  rw [abs_of_nonneg (mul_nonneg hc (sub_nonneg.mpr he))]
  convert hmul using 1 <;> field_simp <;> ring

/-- All three relevant kernel defects are bounded directly from the exact
printed coefficients. -/
theorem holNoiseKernels_bounds (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (h : ℝ≥0) (hh1 : (h : ℝ) ≤ 1) (s : ℝ) (hs : s ∈ Icc 0 (h : ℝ)) :
    |holNoiseKernels α γ 0 s| ≤ Real.sqrt (2 * α) * (γ / 2) * (h : ℝ) ∧
    |holNoiseKernels α γ 1 s| ≤ Real.sqrt (2 * α) * γ * (h : ℝ) ∧
    |holNoiseKernels α γ 2 s - holNoiseKernels α γ 3 s| ≤
      Real.sqrt (2 * α) * (α + (holRemainderConstants α γ).μ33) * (h : ℝ) := by
  have hs1 : s ≤ 1 := hs.2.trans hh1
  have hs2 : s ^ 2 ≤ (h : ℝ) := by nlinarith [hs.1, hs.2]
  have hc33 : 0 ≤ (holRemainderConstants α γ).μ33 := by
    dsimp [holRemainderConstants]
    positivity
  have h13 : |(holCoefficients α γ s).μ13| ≤ γ / 2 * (h : ℝ) := by
    by_cases hs0 : s = 0
    · simp [hs0, holCoefficients]
      positivity
    · have hc := (holCoefficient_bounds α γ s hα hγ (lt_of_le_of_ne hs.1 (Ne.symm hs0)) hs1).bound13
      change |(holCoefficients α γ s).μ13| ≤ γ / 2 * s ^ 2 at hc
      exact hc.trans (mul_le_mul_of_nonneg_left hs2 (by positivity))
  have h23 := (hol_mu23_bound α γ s hα hγ hs.1).trans
    (mul_le_mul_of_nonneg_left hs.2 hγ)
  have h33 : |(holCoefficients α γ s).μ33 - 1| ≤
      (α + (holRemainderConstants α γ).μ33) * (h : ℝ) := by
    by_cases hs0 : s = 0
    · simp [hs0, holCoefficients]
      positivity
    · have hc := (holCoefficient_bounds α γ s hα hγ (lt_of_le_of_ne hs.1 (Ne.symm hs0)) hs1).bound33
      have ha : |(holCoefficients α γ s).μ33 - 1| ≤
          |(holCoefficients α γ s).μ33 - 1 + α * s| + α * s := by
        have hab := abs_sub ((holCoefficients α γ s).μ33 - 1 + α * s) (α * s)
        simpa [abs_of_nonneg (mul_nonneg hα.le hs.1)] using hab
      have hb := mul_le_mul_of_nonneg_left hs2 hc33
      have hd := mul_le_mul_of_nonneg_left hs.2 hα.le
      nlinarith
  constructor
  · simp only [holNoiseKernels, Matrix.cons_val_zero, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left h13 (Real.sqrt_nonneg _)).trans_eq (by ring)
  constructor
  · simp only [holNoiseKernels, Matrix.cons_val_one, Matrix.cons_val_zero, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left h23 (Real.sqrt_nonneg _)).trans_eq (by ring)
  · have he : holNoiseKernels α γ 2 s - holNoiseKernels α γ 3 s =
        Real.sqrt (2 * α) * ((holCoefficients α γ s).μ33 - 1) := by
      simp [holNoiseKernels]
      ring
    rw [he, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left h33 (Real.sqrt_nonneg _)).trans_eq (by ring)

/-- The exact three-coordinate noise discrepancy from the coupled Brownian
Euler increment is `O(h sqrt(h))`, proved using the Brownian isometry. -/
theorem holScalarNoise_error_le (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (a h : ℝ≥0) (hh1 : (h : ℝ) ≤ 1) :
    ‖holScalarNoise α γ a h 0‖ + ‖holScalarNoise α γ a h 1‖ +
      ‖holScalarNoise α γ a h 2 - holScalarNoise α γ a h 3‖ ≤
      holScalarNoiseConstant α γ * (h : ℝ) * Real.sqrt (h : ℝ) := by
  have hc33 : 0 ≤ (holRemainderConstants α γ).μ33 := by
    dsimp [holRemainderConstants]
    positivity
  have h0 := segmentConvolution_norm_le (holNoiseKernels α γ 0)
    (continuous_holNoiseKernels α γ 0) a h
    (Real.sqrt (2 * α) * (γ / 2) * (h : ℝ)) (by positivity)
    (fun s hs => (holNoiseKernels_bounds α γ hα hγ h hh1 s hs).1)
  have h1 := segmentConvolution_norm_le (holNoiseKernels α γ 1)
    (continuous_holNoiseKernels α γ 1) a h
    (Real.sqrt (2 * α) * γ * (h : ℝ)) (by positivity)
    (fun s hs => (holNoiseKernels_bounds α γ hα hγ h hh1 s hs).2.1)
  have h2 := segmentConvolution_norm_le
    (fun s => holNoiseKernels α γ 2 s - holNoiseKernels α γ 3 s)
    ((continuous_holNoiseKernels α γ 2).sub (continuous_holNoiseKernels α γ 3)) a h
    (Real.sqrt (2 * α) * (α + (holRemainderConstants α γ).μ33) * (h : ℝ))
    (by positivity)
    (fun s hs => (holNoiseKernels_bounds α γ hα hγ h hh1 s hs).2.2)
  rw [← segmentConvolution_sub] at h2
  change ‖holScalarNoise α γ a h 2 - holScalarNoise α γ a h 3‖ ≤ _ at h2
  change ‖holScalarNoise α γ a h 0‖ ≤ _ at h0
  change ‖holScalarNoise α γ a h 1‖ ≤ _ at h1
  calc
    _ ≤ _ := add_le_add (add_le_add h0 h1) h2
    _ = _ := by unfold holScalarNoiseConstant; ring

/-- The vector coupling rate retains the exact square-root dimension
factor, for the actual independently generated spatial Brownian sources. -/
theorem holVectorNoise_error_le (ι : Type*) [Fintype ι] [DecidableEq ι]
    (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (a h : ℝ≥0) (hh1 : (h : ℝ) ≤ 1) :
    ‖holVectorNoise ι α γ a h 0‖ + ‖holVectorNoise ι α γ a h 1‖ +
      ‖holVectorNoise ι α γ a h 2 - holVectorNoise ι α γ a h 3‖ ≤
      (Real.sqrt (Fintype.card ι : ℝ) * holScalarNoiseConstant α γ) *
        (h : ℝ) * Real.sqrt (h : ℝ) := by
  unfold holVectorNoise
  rw [← map_sub, spatialLift_norm, spatialLift_norm, spatialLift_norm]
  have h := mul_le_mul_of_nonneg_left (holScalarNoise_error_le α γ hα hγ a h hh1)
    (Real.sqrt_nonneg (Fintype.card ι : ℝ))
  convert h using 1 <;> ring

end PBGSO.Methods
