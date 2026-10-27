import AverageLMC.LaplacianLocalError
import AverageLMC.LaplacianGenerator
import UnadjustedLangevin.LpDrift
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace AverageLMC

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The local third-order coupling estimate for the actual L² gradient Euler
step. The pairing input is the weak-Dynkin consequence proved for the actual
stationary diffusion; the total defect is derived directly from its integral
equation and Brownian moments. -/
theorem lp_laplacian_one_step_bound
    (f : E → ℝ) (m h d Rgen : ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hm : 0 < m) (hmM : m ≤ (M : ℝ))
    (hh : 0 ≤ h) (hd : 0 ≤ d) (hsmall : h * (M : ℝ) ≤ 1) (hRgen : 0 ≤ Rgen)
    (X : Lp E 2 P) (Y B : ℝ → Lp E 2 P) (hY : Continuous Y)
    (hG : ∀ t ∈ Icc 0 h, ‖ULA.lpDrift P (gradient f) hLip (Y t)‖ ≤
      Real.sqrt ((M : ℝ) * d))
    (hB : ∀ t ∈ Icc 0 h, ‖B t‖ ≤ Real.sqrt (2 * d) * Real.sqrt t)
    (hYe : ∀ t ∈ Icc 0 h, Y t - Y 0 =
      -(∫ s in 0..t, ULA.lpDrift P (gradient f) hLip (Y s)) + B t)
    (hpair : ∀ t ∈ Icc 0 h,
      ⟪(X - h • ULA.lpDrift P (gradient f) hLip X) -
          (Y 0 - h • ULA.lpDrift P (gradient f) hLip (Y 0)),
        ULA.lpDrift P (gradient f) hLip (Y t) -
          ULA.lpDrift P (gradient f) hLip (Y 0)⟫ ≤
        t * ‖(X - h • ULA.lpDrift P (gradient f) hLip X) -
          (Y 0 - h • ULA.lpDrift P (gradient f) hLip (Y 0))‖ * Rgen) :
    ‖X - h • ULA.lpDrift P (gradient f) hLip X + B h - Y h‖ ^ 2 ≤
      (1 - m * h) ^ 2 * ‖X - Y 0‖ ^ 2 +
      h ^ 2 * (1 - m * h) * ‖X - Y 0‖ * Rgen +
      ((3 / 2 : ℝ) * (M : ℝ) * h * Real.sqrt h * Real.sqrt d) ^ 2 := by
  let g := ULA.lpDrift P (gradient f) hLip
  let Ψ := (X - h • g X) - (Y 0 - h • g (Y 0))
  let D := ULA.localDefect g Y h
  have hg := ULA.lpDrift_lipschitz P (gradient f) hLip
  have hgc : Continuous (fun t ↦ g (Y t)) := hg.continuous.comp hY
  have he := ULA.localDefect_euler_identity g Y B h (hgc.intervalIntegrable 0 h)
    (hYe h ⟨hh, le_rfl⟩)
  have hdecomp : X - h • g X + B h - Y h = Ψ + D := by
    rw [he]
    dsimp [Ψ, D]
    module
  have hmh : m * h ≤ 1 := by nlinarith [mul_nonneg hh (sub_nonneg.mpr hmM)]
  have hsmall' : h ≤ 2 / (m + (M : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < m + (M : ℝ))).mpr
    nlinarith
  have hΨ : ‖Ψ‖ ≤ (1 - m * h) * ‖X - Y 0‖ :=
    ULA.lpDrift_gradient_contract P f m h M hf hsc hLip hmM (by positivity) hh hsmall' X (Y 0)
  have hΨ2 : ‖Ψ‖ ^ 2 ≤ (1 - m * h) ^ 2 * ‖X - Y 0‖ ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg Ψ) (by positivity : 0 ≤ (1 - m * h) * ‖X - Y 0‖)).mpr hΨ
    simpa only [mul_pow] using hs
  have hD := localDefect_three_halves_bound g Y B M h d hh hd hsmall hg hG hB hYe
  have hD2 : ‖D‖ ^ 2 ≤ ((3 / 2 : ℝ) * (M : ℝ) * h * Real.sqrt h * Real.sqrt d) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg D) (by positivity)).mpr hD
  have hcont : Continuous (fun t ↦ ⟪Ψ, g (Y t) - g (Y 0)⟫) :=
    continuous_const.inner (hgc.sub continuous_const)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hh
    (hcont.intervalIntegrable 0 h)
    ((continuous_id.mul continuous_const |>.mul continuous_const :
      Continuous (fun t : ℝ ↦ t * ‖Ψ‖ * Rgen)).intervalIntegrable 0 h) hpair
  have hinc : Continuous (fun t ↦ g (Y t) - g (Y 0)) := hgc.sub continuous_const
  have hinner := (innerSL ℝ Ψ).intervalIntegral_comp_comm (μ := volume)
    (hinc.intervalIntegrable 0 h)
  change (∫ t in 0..h, ⟪Ψ, g (Y t) - g (Y 0)⟫) = ⟪Ψ, D⟫ at hinner
  change (∫ t in 0..h, ⟪Ψ, g (Y t) - g (Y 0)⟫) ≤
    ∫ t in 0..h, t * ‖Ψ‖ * Rgen at hi
  rw [hinner] at hi
  have htime : (∫ t in 0..h, t * ‖Ψ‖ * Rgen) = h ^ 2 / 2 * ‖Ψ‖ * Rgen := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, integral_id]
    simp
  rw [htime] at hi
  have hcross : 2 * ⟪Ψ, D⟫ ≤ h ^ 2 * (1 - m * h) * ‖X - Y 0‖ * Rgen := by
    have hs := mul_le_mul_of_nonneg_left hΨ (show 0 ≤ h ^ 2 * Rgen by positivity)
    nlinarith
  change ‖X - h • g X + B h - Y h‖ ^ 2 ≤ _
  rw [hdecomp, norm_add_sq_real]
  nlinarith

end AverageLMC
