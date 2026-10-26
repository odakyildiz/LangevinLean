import PBGSO.GeneralProcess
import UnadjustedLangevin.BrownianLangevin

/-! # General mean-field integral dynamics driven by actual Brownian coordinates

Coordinate Gaussian increment laws prove continuity and a square-root L²
increment bound for the sampler input. A fixed linear map permits degenerate
diffusion on augmented sampler states. The optimiser receives zero noise.
These are L² integral solutions. This file does not identify an almost-sure
strong SDE or infer independence of coordinate processes from marginal laws.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace PBGSO

variable {Ω I Z : Type*} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  (Q : Measure Ω)

/-- A constant diffusion applied to the actual sqrt(2)-scaled Brownian
coordinate increment. For an SDE with coefficient sigma, use K=sigma/sqrt(2). -/
def samplerBrownianInput (K : EuclideanSpace ℝ I →L[ℝ] Z)
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (a t : ℝ) : Lp Z 2 Q :=
  K.compLp (ULA.brownianLangevinNoise Q W hW a t)

theorem samplerBrownianInput_continuous (K : EuclideanSpace ℝ I →L[ℝ] Z)
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q) (a : ℝ) :
    Continuous (samplerBrownianInput Q K W hW a) :=
  (K.compLpL 2 Q).continuous.comp (ULA.brownianLangevinNoise_continuous Q W hW a)

@[simp] theorem samplerBrownianInput_zero (K : EuclideanSpace ℝ I →L[ℝ] Z)
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q) (a : ℝ) :
    samplerBrownianInput Q K W hW a 0 = 0 := by
  change (K.compLpL 2 Q) (ULA.brownianLangevinNoise Q W hW a 0) = 0
  rw [ULA.brownianLangevinNoise_zero, map_zero]

/-- The square-root noise coefficient is derived from Gaussian increment
moments, rather than supplied as an analytic input. -/
theorem samplerBrownianInput_bound (K : EuclideanSpace ℝ I →L[ℝ] Z)
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    ‖samplerBrownianInput Q K W hW a t‖ ≤
      ‖K‖ * Real.sqrt (2 * (Fintype.card I : ℝ)) * Real.sqrt t := by
  apply (K.norm_compLp_le _).trans_eq
  rw [ULA.brownianLangevinNoise_norm Q W hW a t ha ht]
  ring

namespace LipschitzDynamics
variable {A G : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [CompleteSpace Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [IsProbabilityMeasure Q] (D : PBGSO.LipschitzDynamics A Z G)

/-- The complete general mean-field integral solution is constructed with
the actual Brownian-coordinate input and zero optimiser diffusion. -/
theorem exists_brownian_integral (initial : A × Lp Z 2 Q)
    (K : EuclideanSpace ℝ I →L[ℝ] Z)
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (a T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → A × Lp Z 2 Q, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 T, Y t - initial =
        (∫ s in 0..t, D.field Q (Y s)) + (0, samplerBrownianInput Q K W hW a t) :=
  D.exists_integral Q initial (samplerBrownianInput Q K W hW a)
    (samplerBrownianInput_continuous Q K W hW a)
    (samplerBrownianInput_zero Q K W hW a) T hT

end LipschitzDynamics
end PBGSO
