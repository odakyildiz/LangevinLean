import UnadjustedLangevin.GaussianCoordinates
import UnadjustedLangevin.LangevinIntegral

set_option linter.style.header false

/-!
# Constructing the `L²` Langevin equation from Brownian coordinates

Actual Brownian coordinate laws construct a continuous `L²` additive noise path
and its exact square-root increment moment. Picard then constructs the integral
solution for the actual gradient. No integral equation, noise continuity, or
noise moment bound is supplied as an assumption.

This construction does not establish the stationary Gibbs law, a score moment
bound, or independence/adaptedness of the initial state and Brownian input.
Those are distinct probabilistic claims.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace ULA

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (P : Measure Ω)

/-- The additive Langevin noise over a segment starting at real time `a`.
The real-time Brownian presentation is constant at zero at negative times. -/
def brownianLangevinNoise (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ) :
    Lp (EuclideanSpace ℝ ι) 2 P :=
  Real.sqrt 2 • (brownianCoordinatesRealLp P W hW (a + t) -
    brownianCoordinatesRealLp P W hW a)

/-- Noise continuity follows from Gaussian increment moments in `L²`. -/
theorem brownianLangevinNoise_continuous (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a : ℝ) :
    Continuous (brownianLangevinNoise P W hW a) := by
  exact (((brownianCoordinatesRealLp_continuous P W hW).comp
    (continuous_const.add continuous_id)).sub continuous_const).const_smul (Real.sqrt 2)

@[simp] theorem brownianLangevinNoise_zero (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a : ℝ) :
    brownianLangevinNoise P W hW a 0 = 0 := by
  simp only [brownianLangevinNoise, add_zero, sub_self, smul_zero]

/-- The exact segment noise moment is a theorem about the Brownian input. -/
theorem brownianLangevinNoise_norm (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ)
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    ‖brownianLangevinNoise P W hW a t‖ =
      Real.sqrt (2 * (Fintype.card ι : ℝ)) * Real.sqrt t :=
  brownianCoordinatesRealLp_increment_scaled_norm P W hW a t ha ht

variable [IsProbabilityMeasure P]

/-- Actual Brownian coordinates and a Lipschitz gradient construct a continuous
short-time `L²` Langevin solution. The local step restriction belongs to the
Picard construction and may be removed by concatenation. No score bound or
stationary-law assertion is made. -/
theorem exists_lp_langevin_integral_of_brownian_small
    (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsmall : (L : ℝ) * h ≤ 1 / 2) :
    ∃ Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P,
      Continuous Y ∧ Y 0 = initial ∧
      (∀ t ∈ Icc 0 h, Y t - initial =
        -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) +
          brownianLangevinNoise P W hW a t) ∧
      (∀ t ∈ Icc 0 h, ‖brownianLangevinNoise P W hW a t‖ =
        Real.sqrt (2 * (Fintype.card ι : ℝ)) * Real.sqrt t) := by
  obtain ⟨Y, hY, hY0, hYeq⟩ := exists_lp_langevin_integral_small P U L hLip initial
    (brownianLangevinNoise P W hW a) (brownianLangevinNoise_continuous P W hW a)
    (brownianLangevinNoise_zero P W hW a) h hh hsmall
  exact ⟨Y, hY, hY0, hYeq,
    fun t ht ↦ brownianLangevinNoise_norm P W hW a t ha ht.1⟩

/-- Actual Brownian coordinates construct a finite-horizon `L²` Langevin
solution from the Lipschitz gradient, without a small-time restriction. Both
the integral equation and exact noise moment are conclusions. -/
theorem exists_lp_langevin_integral_of_brownian
    (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    ∃ Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P,
      Continuous Y ∧ Y 0 = initial ∧
      (∀ t ∈ Icc 0 h, Y t - initial =
        -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) +
          brownianLangevinNoise P W hW a t) ∧
      (∀ t ∈ Icc 0 h, ‖brownianLangevinNoise P W hW a t‖ =
        Real.sqrt (2 * (Fintype.card ι : ℝ)) * Real.sqrt t) := by
  obtain ⟨Y, hY, hY0, hYeq⟩ := exists_lp_langevin_integral P U L hLip initial
    (brownianLangevinNoise P W hW a) (brownianLangevinNoise_continuous P W hW a)
    (brownianLangevinNoise_zero P W hW a) h hh
  exact ⟨Y, hY, hY0, hYeq,
    fun t ht ↦ brownianLangevinNoise_norm P W hW a t ha ht.1⟩

end ULA
