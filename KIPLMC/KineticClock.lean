import KIPLMC.Rescaling
import KineticLangevin.Dynamics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Exact physical-time kinetic integral equation under the particle clock -/
noncomputable section
open MeasureTheory Set
namespace KIPLMC
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Velocity rescaling as an actual continuous linear map on phase space. -/
def velocityScaleLinear (c : ℝ) : (E×E) →L[ℝ] (E×E) :=
  (c • ContinuousLinearMap.fst ℝ E E).prod (ContinuousLinearMap.snd ℝ E E)

@[simp] theorem velocityScaleLinear_apply (c : ℝ) (z : E×E) :
    velocityScaleLinear c z=rescaleVelocity c z := rfl

/-- The phase drift transforms with exactly the clock factor. -/
theorem kineticNegativeDrift_clock (g : E → E) (c γ : ℝ) (hc : c≠0) (z : E×E) :
    c⁻¹ • velocityScaleLinear c⁻¹ (KineticLangevin.kineticNegativeDrift g (c*γ) 1 z) =
      KineticLangevin.kineticNegativeDrift (fun x ↦ (c^2)⁻¹ • g x) γ 1
        (velocityScaleLinear c⁻¹ z) := by
  have he : c⁻¹*(c⁻¹*(c*γ))=γ*c⁻¹ := by field_simp <;> ring
  ext <;> simp only [velocityScaleLinear_apply,rescaleVelocity,KineticLangevin.kineticNegativeDrift,
    Prod.smul_fst,Prod.smul_snd,one_smul,smul_add,smul_smul,he,inv_pow,pow_two] <;> module

/-- Every actual integral solution at the rescaled clock gives an actual
physical-time integral solution, with the exact transformed Brownian input. -/
theorem kinetic_integral_clock (g : E → E) (hg : Continuous g) (c γ T : ℝ) (hc : 0<c)
    (initial : E×E) (B : ℝ → E) (Y : ℝ → E×E) (hY : Continuous Y)
    (heY : ∀ s ∈ Icc 0 (T/c),Y s-initial =
      -(∫ r in 0..s,KineticLangevin.kineticNegativeDrift g (c*γ) 1 (Y r))+(B s,0)) :
    ∀ t ∈ Icc 0 T,
      rescaleVelocity c⁻¹ (Y (t/c))-rescaleVelocity c⁻¹ initial =
        -(∫ s in 0..t,KineticLangevin.kineticNegativeDrift (fun x ↦ (c^2)⁻¹ • g x) γ 1
          (rescaleVelocity c⁻¹ (Y (s/c))))+(c⁻¹ • B (t/c),0) := by
  intro t ht
  let D := velocityScaleLinear (E := E) c⁻¹
  let F := fun r ↦ KineticLangevin.kineticNegativeDrift g (c*γ) 1 (Y r)
  have hF : Continuous F := by unfold F KineticLangevin.kineticNegativeDrift;fun_prop
  have hInt : (∫ s in 0..t,KineticLangevin.kineticNegativeDrift (fun x ↦ (c^2)⁻¹ • g x) γ 1
      (rescaleVelocity c⁻¹ (Y (s/c)))) = D (∫ r in 0..(t/c),F r) := by
    calc
      _ = ∫ s in 0..t,c⁻¹ • D (F (s/c)) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact (kineticNegativeDrift_clock g c γ hc.ne' (Y (s/c))).symm
      _ = c⁻¹ • ∫ s in 0..t,D (F (s/c)) := by rw [intervalIntegral.integral_smul]
      _ = ∫ s in 0..(t/c),D (F s) := by
        rw [intervalIntegral.integral_comp_div (fun r ↦ D (F r)) hc.ne',zero_div,
          smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
      _ = _ := D.intervalIntegral_comp_comm (hF.intervalIntegrable (μ := volume) 0 (t/c))
  have htc : t/c ∈ Icc 0 (T/c) :=
    ⟨div_nonneg ht.1 hc.le,(div_le_div_iff_of_pos_right hc).mpr ht.2⟩
  have he := congrArg D (heY (t/c) htc)
  rw [map_sub,map_add,map_neg,← hInt] at he
  exact he

end KIPLMC
