import KineticLangevin.Dynamics
import KineticLangevin.BrownianScaling
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
open MeasureTheory Set
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Normalize the velocity while retaining the actual position coordinate. -/
def massPhaseMap (c : ℝ) : (E×E) →L[ℝ] (E×E) :=
  (c • ContinuousLinearMap.fst ℝ E E).prod (ContinuousLinearMap.snd ℝ E E)

/-- The inverse-mass phase drift transforms exactly under the normalized kinetic clock. -/
theorem kinetic_mass_drift_identity (g : E→E) (c γ : ℝ) (hc : c≠0) (z : E×E) :
    c⁻¹ • massPhaseMap c⁻¹ (kineticNegativeDrift g γ (c^2) z) =
      kineticNegativeDrift g (γ/c) 1 (massPhaseMap c⁻¹ z) := by
  have he : c⁻¹*(c⁻¹*c^2)=1 := by field_simp
  have hγ : c⁻¹*(c⁻¹*γ)=(γ/c)*c⁻¹ := by ring
  apply Prod.ext
  · change c⁻¹ • (c⁻¹ • (γ • z.1+c^2 • g z.2)) =
      (γ/c) • (c⁻¹ • z.1)+1 • g z.2
    simp only [smul_add,smul_smul,he,hγ,one_smul]
  · change c⁻¹ • (-z.1)= -(c⁻¹ • z.1)
    rw [smul_neg]

/-- Lemma 1: the complete actual integral equation with inverse mass c² becomes the unit-mass equation. -/
theorem kinetic_mass_integral (g : E→E) (hg : Continuous g) (c γ T : ℝ) (hc : 0<c)
    (initial : E×E) (B : ℝ→E) (Y : ℝ→E×E) (hY : Continuous Y)
    (heY : ∀ s ∈ Icc 0 (T/c),Y s-initial =
      -(∫ r in 0..s,kineticNegativeDrift g γ (c^2) (Y r))+(B s,0)) :
    ∀ t ∈ Icc 0 T,
      massPhaseMap c⁻¹ (Y (t/c))-massPhaseMap c⁻¹ initial =
        -(∫ s in 0..t,kineticNegativeDrift g (γ/c) 1 (massPhaseMap c⁻¹ (Y (s/c))))+
          (c⁻¹ • B (t/c),0) := by
  let D := massPhaseMap (E:=E) c⁻¹
  let F := fun r => kineticNegativeDrift g γ (c^2) (Y r)
  have hF : Continuous F := by unfold F kineticNegativeDrift;fun_prop
  intro t ht
  have hInt : (∫ s in 0..t,kineticNegativeDrift g (γ/c) 1 (D (Y (s/c)))) =
      D (∫ r in 0..(t/c),F r) := by
    calc
      _ = ∫ s in 0..t,c⁻¹ • D (F (s/c)) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact (kinetic_mass_drift_identity g c γ hc.ne' (Y (s/c))).symm
      _ = c⁻¹ • ∫ s in 0..t,D (F (s/c)) := by rw [intervalIntegral.integral_smul]
      _ = ∫ s in 0..(t/c),D (F s) := by
        rw [intervalIntegral.integral_comp_div (fun r => D (F r)) hc.ne',zero_div,
          smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
      _ = _ := D.intervalIntegral_comp_comm (hF.intervalIntegrable (μ:=volume) 0 (t/c))
  have he := congrArg D (heY (t/c) ⟨div_nonneg ht.1 hc.le,(div_le_div_iff_of_pos_right hc).mpr ht.2⟩)
  rw [map_sub,map_add,map_neg,←hInt] at he
  exact he

/-- The transformed actual Brownian input has precisely the new fluctuation-dissipation amplitude. -/
theorem kinetic_mass_noise_amplitude (c γ : ℝ) (hc : 0<c) (hγ : 0≤γ) :
    c⁻¹*Real.sqrt (2*γ*c^2)=Real.sqrt (2*(γ/c))*Real.sqrt c := by
  rw [Real.sqrt_mul (by positivity : 0≤2*γ),Real.sqrt_sq hc.le]
  have he : 2*(γ/c)=(2*γ)/c := by ring
  rw [he,Real.sqrt_div (by positivity : 0≤2*γ)]
  field_simp

end KineticLangevin
