import UnadjustedLangevin.Gibbs
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

set_option linter.style.header false

/-! # The actual Gaussian Euler proposal has its displayed Lebesgue density

Gaussian Fourier integration identifies the centered density and translation
identifies every proposal mean. The positive normalizer is defined by an actual
finite Gaussian integral and is independent of the current state. There is no
potential regularity assumption in the density theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The real radial Gaussian integral used for normalization. -/
def radialGaussianIntegral (a : ℝ) : ℝ := ∫ z : H, Real.exp (-a * ‖z‖ ^ 2)

/-- A positive real density normalizer whenever the precision `a` is positive. -/
def radialGaussianNormalizer (a : ℝ) : ℝ := (radialGaussianIntegral (H := H) a)⁻¹

theorem radialGaussianIntegral_pos (a : ℝ) (ha : 0 < a) :
    0 < radialGaussianIntegral (H := H) a :=
  integral_exp_pos (integrable_exp_neg_mul_norm_sq a ha)

theorem radialGaussianNormalizer_pos (a : ℝ) (ha : 0 < a) :
    0 < radialGaussianNormalizer (H := H) a := inv_pos.mpr (radialGaussianIntegral_pos a ha)

/-- The normalized radial density with precision `a` and center `c`. -/
def radialGaussianDensity (a : ℝ) (c z : H) : ℝ≥0∞ :=
  ENNReal.ofReal (radialGaussianNormalizer (H := H) a * Real.exp (-a * ‖z - c‖ ^ 2))

theorem integrable_radialGaussianDensity_real (a : ℝ) (ha : 0 < a) (c : H) :
    Integrable (fun z : H ↦ radialGaussianNormalizer (H := H) a *
      Real.exp (-a * ‖z - c‖ ^ 2)) volume := by
  exact ((integrable_exp_neg_mul_norm_sq (H := H) a ha).comp_sub_right c).const_mul _

theorem integral_radialGaussianDensity_real (a : ℝ) (ha : 0 < a) (c : H) :
    (∫ z : H, radialGaussianNormalizer (H := H) a * Real.exp (-a * ‖z - c‖ ^ 2)) = 1 := by
  rw [integral_const_mul,
    integral_sub_right_eq_self (μ := volume) (fun z : H ↦ Real.exp (-a * ‖z‖ ^ 2)) c]
  exact inv_mul_cancel₀ (radialGaussianIntegral_pos a ha).ne'

/-- Normalization of the displayed density, including finiteness. -/
theorem radialGaussianDensity_isProbability (a : ℝ) (ha : 0 < a) (c : H) :
    IsProbabilityMeasure (volume.withDensity (radialGaussianDensity a c)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  change (∫⁻ z : H, ENNReal.ofReal (radialGaussianNormalizer (H := H) a *
    Real.exp (-a * ‖z - c‖ ^ 2))) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_radialGaussianDensity_real a ha c)
    (ae_of_all _ fun z ↦ mul_nonneg (radialGaussianNormalizer_pos a ha).le (Real.exp_nonneg _)),
    integral_radialGaussianDensity_real a ha c, ENNReal.ofReal_one]

/-- The complex Gaussian normalization factor is the same actual real integral. -/
theorem integral_complex_radialGaussian (a : ℝ) (_ha : 0 < a) :
    (∫ z : H, Complex.exp (-(a : ℂ) * ‖z‖ ^ 2)) =
      (radialGaussianIntegral (H := H) a : ℂ) := by
  calc
    _ = ∫ z : H, (Real.exp (-a * ‖z‖ ^ 2) : ℂ) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z ↦ by
        change Complex.exp (-(a : ℂ) * ‖z‖ ^ 2) = (Real.exp (-a * ‖z‖ ^ 2) : ℂ)
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
    _ = _ := integral_ofReal

/-- The radial Gaussian Fourier integral, expressed using its real normalizer. -/
theorem integral_radialGaussian_character (a : ℝ) (ha : 0 < a) (t : H) :
    (∫ z : H, (Real.exp (-a * ‖z‖ ^ 2) : ℂ) *
      Complex.exp ((inner ℝ z t : ℝ) * Complex.I)) =
      (radialGaussianIntegral (H := H) a : ℂ) *
        Complex.exp (-(‖t‖ ^ 2 : ℝ) / (4 * (a : ℂ))) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := H) (b := (a : ℂ)) (by simpa) Complex.I t
  have hzero := GaussianFourier.integral_cexp_neg_mul_sq_norm
    (V := H) (b := (a : ℂ)) (by simpa using ha)
  rw [integral_complex_radialGaussian a ha] at hzero
  rw [← hzero] at h
  convert h using 1
  · apply integral_congr_ae
    exact ae_of_all _ fun z ↦ by
      change (Real.exp (-a * ‖z‖ ^ 2) : ℂ) *
        Complex.exp ((inner ℝ z t : ℝ) * Complex.I) =
          Complex.exp (-(a : ℂ) * ‖z‖ ^ 2 + Complex.I * (inner ℝ t z : ℝ))
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow,
        real_inner_comm t z]
      ring
  · congr 2
    rw [Complex.I_sq]
    push_cast
    ring

/-- Characteristic function of the displayed normalized radial Gaussian density. -/
theorem charFun_radialGaussianDensity (a : ℝ) (ha : 0 < a) (c t : H) :
    charFun (volume.withDensity (radialGaussianDensity a c)) t =
      Complex.exp (-(‖t‖ ^ 2 : ℝ) / (4 * (a : ℂ))) *
        Complex.exp ((inner ℝ c t : ℝ) * Complex.I) := by
  rw [charFun_apply]
  unfold radialGaussianDensity
  have hm : Measurable (fun z : H ↦ ENNReal.ofReal
      (radialGaussianNormalizer (H := H) a * Real.exp (-a * ‖z - c‖ ^ 2))) := by fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal
    (mul_nonneg (radialGaussianNormalizer_pos a ha).le (Real.exp_nonneg _))]
  have htrans : (∫ z : H, (radialGaussianNormalizer (H := H) a *
      Real.exp (-a * ‖z - c‖ ^ 2)) • Complex.exp ((inner ℝ z t : ℝ) * Complex.I)) =
      (radialGaussianNormalizer (H := H) a : ℂ) *
        ((∫ z : H, (Real.exp (-a * ‖z‖ ^ 2) : ℂ) *
          Complex.exp ((inner ℝ z t : ℝ) * Complex.I)) *
          Complex.exp ((inner ℝ c t : ℝ) * Complex.I)) := by
    rw [← integral_add_right_eq_self (fun z : H ↦
      (radialGaussianNormalizer (H := H) a * Real.exp (-a * ‖z - c‖ ^ 2)) •
        Complex.exp ((inner ℝ z t : ℝ) * Complex.I)) c]
    simp only [add_sub_cancel_right, inner_add_left, Complex.ofReal_add,
      add_mul, Complex.exp_add, Complex.real_smul, Complex.ofReal_mul]
    calc
      _ = ∫ z : H, (radialGaussianNormalizer (H := H) a : ℂ) *
          (((Real.exp (-a * ‖z‖ ^ 2) : ℂ) * Complex.exp ((inner ℝ z t : ℝ) * Complex.I)) *
            Complex.exp ((inner ℝ c t : ℝ) * Complex.I)) := by
        apply integral_congr_ae
        exact ae_of_all _ fun z ↦ by ring
      _ = _ := by rw [integral_const_mul, integral_mul_const]
  rw [htrans, integral_radialGaussian_character a ha]
  rw [radialGaussianNormalizer, Complex.ofReal_inv,
    ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
      (radialGaussianIntegral_pos a ha).ne'), one_mul]

/-- The Gaussian Euler normalizer; it is independent of the proposal center. -/
def gaussianProposalNormalizer (h : ℝ) : ℝ :=
  radialGaussianNormalizer (H := H) (1 / (4 * h))

/-- The exact real Gaussian Euler density, written with covariance `2h I`. -/
def gaussianProposalDensity (h : ℝ) (c y : H) : ℝ≥0∞ :=
  ENNReal.ofReal (gaussianProposalNormalizer (H := H) h *
    Real.exp (-‖y - c‖ ^ 2 / (4 * h)))

theorem gaussianProposalNormalizer_pos (h : ℝ) (hh : 0 < h) :
    0 < gaussianProposalNormalizer (H := H) h := radialGaussianNormalizer_pos _ (by positivity)

theorem radialGaussianDensity_eq_proposalDensity (h : ℝ) (c : H) :
    radialGaussianDensity (1 / (4 * h)) c = gaussianProposalDensity h c := by
  funext y
  unfold radialGaussianDensity gaussianProposalDensity gaussianProposalNormalizer
  congr 2
  congr 1
  ring

/-- The affine image of the actual standard Gaussian has precisely the
displayed normalized Lebesgue density. -/
theorem gaussian_proposal_density (h : ℝ) (hh : 0 < h) (c : H) :
    (stdGaussian H).map (fun ξ ↦ c + Real.sqrt (2 * h) • ξ) =
      volume.withDensity (gaussianProposalDensity h c) := by
  have ha : 0 < 1 / (4 * h) := by positivity
  have := radialGaussianDensity_isProbability (H := H) (1 / (4 * h)) ha c
  rw [← radialGaussianDensity_eq_proposalDensity]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_radialGaussianDensity _ ha c t]
  have hm : (stdGaussian H).map (fun ξ ↦ c + Real.sqrt (2 * h) • ξ) =
      ((stdGaussian H).map (fun ξ ↦ Real.sqrt (2 * h) • ξ)).map (fun z ↦ c + z) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hm, charFun_map_const_add, charFun_map_smul, charFun_stdGaussian]
  congr 2
  have hnorm : ‖Real.sqrt (2 * h) • t‖ ^ 2 = (2 * h) * ‖t‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
  have hnormC : (‖Real.sqrt (2 * h) • t‖ : ℂ) ^ 2 =
      (2 * (h : ℂ)) * (‖t‖ : ℂ) ^ 2 := by exact_mod_cast hnorm
  rw [hnormC]
  push_cast
  field_simp

/-- Equivalent radial-density form, convenient for detailed balance. -/
theorem gaussian_proposal_radial_density (h : ℝ) (hh : 0 < h) (c : H) :
    (stdGaussian H).map (fun ξ ↦ c + Real.sqrt (2 * h) • ξ) =
      volume.withDensity (radialGaussianDensity (1 / (4 * h)) c) := by
  rw [radialGaussianDensity_eq_proposalDensity]
  exact gaussian_proposal_density h hh c

/-- The potential enters the radial-density equality only through the center. -/
theorem ula_proposal_radial_density (U : H → ℝ) (h : ℝ) (hh : 0 < h) (x : H) :
    (stdGaussian H).map (fun ξ ↦ x - h • gradient U x + Real.sqrt (2 * h) • ξ) =
      volume.withDensity (radialGaussianDensity (1 / (4 * h)) (x - h • gradient U x)) :=
  gaussian_proposal_radial_density h hh _

/-- In particular, the ULA proposal has the density used in the Metropolis
ratio. This equality needs no assumptions on `U` at the fixed starting state. -/
theorem ula_proposal_density (U : H → ℝ) (h : ℝ) (hh : 0 < h) (x : H) :
    (stdGaussian H).map (fun ξ ↦ x - h • gradient U x + Real.sqrt (2 * h) • ξ) =
      volume.withDensity (fun y ↦ ENNReal.ofReal (gaussianProposalNormalizer (H := H) h *
        Real.exp (-‖y - x + h • gradient U x‖ ^ 2 / (4 * h)))) := by
  rw [gaussian_proposal_density h hh]
  congr 1
  funext y
  unfold gaussianProposalDensity
  have heq : y - (x - h • gradient U x) = y - x + h • gradient U x := by abel
  rw [heq]

end ULA
