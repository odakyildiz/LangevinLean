import KIPLMC.Target
import KIPLMC.Geometry
import KineticLangevin.LpOneStep

/-! # Exact thermal velocity moments

The scaled physical velocity has temperature `1/N`. Its normalization is
proved as an actual pushforward identity, then used to derive the L² radius
needed by the shared exponential-integrator analysis.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace KIPLMC

/-- Multiplication by `sqrt N` turns the explicit thermal velocity law into
the actual standard Gaussian law. -/
theorem velocityTarget_unscale {N dθ dx : ℕ} (hN : 0 < N) :
    (velocityTarget N dθ dx).map (fun v ↦ Real.sqrt N • v) =
      stdGaussian (State N dθ dx) := by
  have hs : Real.sqrt N ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hN)
  rw [velocityTarget, Measure.map_map (by fun_prop) (by fun_prop)]
  have hid : (fun v : State N dθ dx ↦ Real.sqrt N • ((Real.sqrt N)⁻¹ • v)) = id := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
    rfl
  change (stdGaussian (State N dθ dx)).map
    (fun v ↦ Real.sqrt N • ((Real.sqrt N)⁻¹ • v)) = _
  rw [hid, Measure.map_id]

/-- An L² velocity with the thermal marginal has exactly the required
particle-scaled radius, including zero-dimensional configuration spaces. -/
theorem thermal_velocity_Lp_norm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {N dθ dx : ℕ} (hN : 0 < N)
    (V : Lp (State N dθ dx) 2 P) (hlaw : HasLaw V (velocityTarget N dθ dx) P) :
    ‖V‖ = Real.sqrt (((dθ : ℝ)+(N : ℝ)*(dx : ℝ))/(N : ℝ)) := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hmap : HasLaw (fun v : State N dθ dx ↦ Real.sqrt N • v)
      (stdGaussian (State N dθ dx)) (velocityTarget N dθ dx) :=
    ⟨(by fun_prop : Measurable (fun v : State N dθ dx ↦ Real.sqrt N • v)).aemeasurable,
      velocityTarget_unscale hN⟩
  have hG : HasLaw (Real.sqrt N • V : Lp (State N dθ dx) 2 P)
      (stdGaussian (State N dθ dx)) P :=
    (hmap.comp hlaw).congr (Lp.coeFn_smul (Real.sqrt N) V)
  have hm := KineticLangevin.gaussian_velocity_Lp_norm P (Real.sqrt N • V) hG
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hm
  have hcard : (Fintype.card (Fin dθ ⊕ (Fin N × Fin dx)) : ℝ) =
      (dθ : ℝ)+(N : ℝ)*(dx : ℝ) := by simp
  change Real.sqrt N * ‖V‖ = Real.sqrt
    (Fintype.card (Fin dθ ⊕ (Fin N × Fin dx)) : ℝ) at hm
  rw [hcard] at hm
  rw [Real.sqrt_div (by positivity)]
  exact (eq_div_iff hs.ne').mpr (by nlinarith [hm])

end KIPLMC
