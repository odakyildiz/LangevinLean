import AverageLMC.PathwiseEnergy
import ProximalLangevin.SplittingOrthogonality
import UnadjustedLangevin.CanonicalULA
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace AverageLMC

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- A deterministic smoothing inequality remains valid at an independent random center.
All double integrals are justified by the quadratic-growth consequence of smoothness. -/
theorem independent_smoothing (f : E → ℝ) (L : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith L (gradient f))
    (X Z : Lp E 2 P) (η : Measure E) (hZ : P.map Z = η)
    (hind : IndepFun X Z P) (c C : ℝ)
    (hsm : ∀ x, (∫ z, f (x + c • z) - f x ∂η) ≤ C) :
    (∫ ω, f ((X + c • Z) ω) ∂P) - (∫ ω, f (X ω) ∂P) ≤ C := by
  let F : E × E → ℝ := fun p ↦ f (p.1 + c • p.2) - f p.1
  have hFm : Continuous F := (hf.continuous.comp (continuous_fst.add
    (continuous_snd.const_smul c))).sub (hf.continuous.comp continuous_fst)
  have hjoint := hind.map_prod_eq_prod_map_map
    (Lp.aestronglyMeasurable X).aemeasurable (Lp.aestronglyMeasurable Z).aemeasurable
  have hpair : AEMeasurable (fun ω ↦ (X ω, Z ω)) P :=
    (Lp.aestronglyMeasurable X).aemeasurable.prodMk (Lp.aestronglyMeasurable Z).aemeasurable
  have hcomp : Integrable (fun ω ↦ F (X ω, Z ω)) P := by
    exact (integrable_smooth_comp P f L hf hLip (fun ω ↦ X ω + c • Z ω)
      ((Lp.memLp X).add ((Lp.memLp Z).const_smul c))).sub
      (integrable_smooth_compLp P f L hf hLip X)
  have hFint : Integrable F ((P.map X).prod (P.map Z)) := by
    rw [← hjoint]
    exact (integrable_map_measure hFm.aestronglyMeasurable hpair).mpr hcomp
  have hi := integral_mono hFint.integral_prod_left (integrable_const C) (fun x ↦ by
    simpa [F, hZ] using hsm x)
  letI : IsProbabilityMeasure (P.map X) := inferInstance
  rw [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  rw [← integral_prod F hFint, ← hjoint, integral_map hpair hFm.aestronglyMeasurable] at hi
  have heq : (∫ ω, F (X ω, Z ω) ∂P) =
      (∫ ω, f ((X + c • Z) ω) ∂P) - ∫ ω, f (X ω) ∂P := by
    rw [← integral_sub (integrable_smooth_compLp P f L hf hLip (X + c • Z))
      (integrable_smooth_compLp P f L hf hLip X)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add X (c • Z), Lp.coeFn_smul c Z] with ω ha hs
    simp only [F, ha, hs, Pi.add_apply, Pi.smul_apply]
  exact heq ▸ hi

/-- The integrated Gaussian energy estimate. This is derived from the actual
integral equation and supporting planes, rather than a supplied recurrence.
The affine energy premise is instantiated by coordinate smoothing. -/
theorem gaussian_energy_bound (f : E → ℝ) (m h d a b w : ℝ) (L : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith L (gradient f)) (hm : 0 ≤ m) (hh : 0 ≤ h)
    (X : Lp E 2 P) (Y B : ℝ → Lp E 2 P) (hY : Continuous Y) (hB : Continuous B)
    (hYe : ∀ t ∈ Icc 0 h, Y t - Y 0 =
      -(∫ s in 0..t, ULA.lpDrift P (gradient f) hLip (Y s)) + B t)
    (horth : ∀ t ∈ Icc 0 h, ⟪X + B t - Y t, B h - B t⟫ = 0)
    (hnoise : ∀ t ∈ Icc 0 h, ‖B h - B t‖ ^ 2 = 2 * (h - t) * d)
    (hcost : ∀ t ∈ Icc 0 h, w ≤ ‖X + B h - Y t‖ ^ 2)
    (henergy : ∀ t ∈ Icc 0 h,
      (∫ ω, f ((X + B t) ω) ∂P) - (∫ ω, f (Y t ω) ∂P) ≤ a + b * t) :
    (1 + m * h) * w ≤ ‖X - Y 0‖ ^ 2 + 2 * h * a + h ^ 2 * b + m * h ^ 2 * d := by
  let g := fun t ↦ ULA.lpDrift P (gradient f) hLip (Y t)
  have hg : Continuous g := (ULA.lpDrift_lipschitz P (gradient f) hLip).continuous.comp hY
  have hi : Continuous (fun t ↦ 2 * ⟪X + B t - Y t, g t⟫) :=
    continuous_const.mul ((continuous_const.add hB |>.sub hY).inner hg)
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 h) :
      2 * ⟪X + B t - Y t, g t⟫ ≤
        (2 * a + 2 * m * h * d - m * w) + (2 * b - 2 * m * d) * t := by
    have hs := lp_strong_gradient_support P f m L hf hsc hLip (X + B t) (Y t)
    have hn : ‖X + B h - Y t‖ ^ 2 =
        ‖X + B t - Y t‖ ^ 2 + 2 * (h - t) * d := by
      rw [show X + B h - Y t = (X + B t - Y t) + (B h - B t) by abel,
        norm_add_sq_real, horth t ht, hnoise t ht]
      ring
    have hc := hcost t ht
    have he := henergy t ht
    have hm' := mul_le_mul_of_nonneg_left (show w - 2 * (h - t) * d ≤
      ‖X + B t - Y t‖ ^ 2 by linarith) hm
    dsimp [g] at *
    nlinarith
  have hr : Continuous (fun t : ℝ ↦
      (2 * a + 2 * m * h * d - m * w) + (2 * b - 2 * m * d) * t) := by fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hh
    (hi.intervalIntegrable 0 h) (hr.intervalIntegrable 0 h) hpoint
  have hformula : (∫ t in 0..h,
      (2 * a + 2 * m * h * d - m * w) + (2 * b - 2 * m * d) * t) =
      2 * h * a + m * h ^ 2 * d - m * h * w + h ^ 2 * b := by
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
      simp only [sub_zero, zero_pow (by norm_num : 2 ≠ 0), smul_eq_mul]
      ring
    · exact intervalIntegrable_const
    · exact (continuous_const.mul continuous_id).intervalIntegrable 0 h
  rw [hformula] at hmono
  have hidentity := langevin_energy_identity P f L hLip X Y B hY h hh hYe
  have hc := hcost h ⟨hh, le_rfl⟩
  dsimp [g] at hmono
  nlinarith

end AverageLMC
