import KineticLangevin.Coefficients
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace KineticLangevin

/-- A continuous damped integral solution has the exact exponential mild form.
The noise is only continuous; its filtered response obeys its own actual integral equation. -/
theorem damped_integral_eq_mild {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (γ T : ℝ) (hT : 0 ≤ T)
    (V F W B : ℝ → E) (hV : Continuous V) (hF : Continuous F) (hB : Continuous B)
    (heq : ∀ t ∈ Icc 0 T, V t - V 0 = -(∫ s in 0..t, γ • V s + F s) + W t)
    (hnoise : ∀ t ∈ Icc 0 T, B t = W t - γ • ∫ s in 0..t, B s) :
    V T = Real.exp (-γ*T) • V 0 -
      (∫ s in 0..T, Real.exp (-γ*(T-s)) • F s) + B T := by
  let D : ℝ → E := fun s => V s - B s
  have hD : Continuous D := hV.sub hB
  have hzero : B 0 = 0 := by
    have he0 := heq 0 ⟨le_rfl, hT⟩
    have hb0 := hnoise 0 ⟨le_rfl, hT⟩
    simp only [sub_self, intervalIntegral.integral_same, neg_zero, zero_add] at he0
    simpa only [intervalIntegral.integral_same, smul_zero, sub_zero, ← he0] using hb0
  have hDeq : ∀ t ∈ Icc 0 T, D t = V 0 - ∫ s in 0..t, γ • D s + F s := by
    intro t ht
    have he := heq t ht
    have hb := hnoise t ht
    have hi : (∫ s in 0..t, γ • D s + F s) =
        (∫ s in 0..t, γ • V s + F s) - γ • ∫ s in 0..t, B s := by
      rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_sub (f := fun s => γ • V s + F s) (g := fun s => γ • B s)
        (((hV.const_smul γ).add hF).intervalIntegrable 0 t)
        ((hB.const_smul γ).intervalIntegrable 0 t)]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [D]
      module
    rw [hi]
    dsimp [D]
    rw [(sub_eq_iff_eq_add).mp he, hb]
    abel
  have hder : ∀ s ∈ Ioo 0 T, HasDerivAt D (-(γ • D s + F s)) s := by
    intro s hs
    have hc : Continuous (fun u => γ • D u + F u) := (hD.const_smul γ).add hF
    have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_sub (V 0)
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu
    exact hDeq u ⟨hu.1.le, hu.2.le⟩
  have hd : ∀ s ∈ Ioo 0 T,
      HasDerivAt (fun u : ℝ => Real.exp (γ*u) • D u)
        (-(Real.exp (γ*s) • F s)) s := by
    intro s hs
    have hh := (((hasDerivAt_id s).const_mul γ).exp).smul (hder s hs)
    convert hh using 1
    · rfl
    · simp only [id_eq, mul_one]
      module
  have hc : Continuous (fun s : ℝ => Real.exp (γ*s) • D s) := by fun_prop
  have hf : Continuous (fun s : ℝ => -(Real.exp (γ*s) • F s)) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun s : ℝ => Real.exp (γ*s) • D s)
    (f' := fun s : ℝ => -(Real.exp (γ*s) • F s))
    hT hc.continuousOn hd (hf.intervalIntegrable 0 T)
  simp only [mul_zero, Real.exp_zero, one_smul] at hi
  have hD0 : D 0 = V 0 := by simp [D, hzero]
  rw [hD0, intervalIntegral.integral_neg] at hi
  have hx := congrArg (fun z : E => Real.exp (-γ*T) • z) hi
  have he : Real.exp (-γ*T) * Real.exp (γ*T) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  rw [smul_sub, smul_smul, he, one_smul, smul_neg, ← intervalIntegral.integral_smul] at hx
  have hi' : (∫ s in 0..T, Real.exp (-γ*T) • (Real.exp (γ*s) • F s)) =
      ∫ s in 0..T, Real.exp (-γ*(T-s)) • F s := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [smul_smul, ← Real.exp_add]
    congr 2
    ring
  rw [hi'] at hx
  dsimp [D] at hx
  have hvt := (sub_eq_iff_eq_add).mp ((sub_eq_iff_eq_add).mp hx.symm)
  exact hvt.trans (by abel)

end KineticLangevin
