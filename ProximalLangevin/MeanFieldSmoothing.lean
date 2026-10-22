import ProximalLangevin.MeanFieldProcess
import ProximalLangevin.SplittingMoments
import ProximalLangevin.MYIPLA
import UnadjustedLangevin.LangevinUniqueness

set_option linter.style.header false

/-! # Quantitative smoothing stability of the constructed mean-field L² process

The actual proximal residual equals the original smooth score at the proximal
point. This proves a uniform score defect of order `η`. A common additive
input cancels between the two constructed integral solutions, allowing an
ordinary Banach-space Grönwall proof. The conclusion controls the supremum of
the L² norms over time; it does not assert an expectation of a pathwise supremum.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace ProximalLangevin

section Score
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

/-- A supporting subgradient of a differentiable function is its actual gradient. -/
theorem IsSubgradient.eq_gradient {f : E → ℝ} {p s : E}
    (hs : IsSubgradient f p s) (hf : DifferentiableAt ℝ f p) : s = gradient f p := by
  let F := fun y => f y - ⟪s, y⟫
  have hmin (y : E) : F p ≤ F y := by
    have h := hs y
    rw [inner_sub_right] at h
    dsimp [F]
    linarith
  have hz := gradient_eq_zero_at_minimum hmin
  have hd : HasFDerivAt F (InnerProductSpace.toDual ℝ E (gradient f p - s)) p := by
    simpa only [F, map_sub, Pi.sub_def, InnerProductSpace.toDual_apply_apply] using
      hf.hasGradientAt.hasFDerivAt.sub (InnerProductSpace.toDual ℝ E s).hasFDerivAt
  have hg := (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient
  rw [hg] at hz
  exact (sub_eq_zero.mp hz).symm

/-- The actual Moreau score is the original smooth score at the true proximal point. -/
theorem gradient_moreau_eq_gradient_prox {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) (hb : ∃ b, ∀ z, b ≤ f z)
    (hf : Differentiable ℝ f) {η : ℝ} (hη : 0 < η) (x : E) :
    gradient (moreau f η) x = gradient f (prox f η x) := by
  rw [gradient_moreau hconv hb hη]
  exact (subgradient_of_isProxPoint hconv hη (prox_isProxPoint hconv hb hη x)).eq_gradient
    (hf _)

/-- Smoothness of the original score is preserved by the actual Moreau envelope. -/
theorem smooth_moreau_gradient_lipschitz {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) (hb : ∃ b, ∀ z, b ≤ f z)
    (hf : Differentiable ℝ f) {η : ℝ} (hη : 0 < η)
    {L : ℝ≥0} (hLip : LipschitzWith L (gradient f)) :
    LipschitzWith L (gradient (moreau f η)) := by
  have heq : gradient (moreau f η) = gradient f ∘ prox f η :=
    funext (gradient_moreau_eq_gradient_prox hconv hb hf hη)
  rw [heq]
  simpa only [mul_one] using hLip.comp (prox_lipschitz hconv hb hη)

/-- The uniform score defect is derived from proximal optimality and displacement.
Its coefficient is independent of the smoothing parameter. -/
theorem gradient_moreau_defect_le {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) (hb : ∃ b, ∀ z, b ≤ f z)
    (hf : Differentiable ℝ f) {η : ℝ} (hη : 0 < η)
    {L K : ℝ≥0} (hLip : LipschitzWith L (gradient f)) (hK : LipschitzWith K f) (x : E) :
    ‖gradient f x - gradient (moreau f η) x‖ ≤ η * (L : ℝ) * (K : ℝ) := by
  rw [gradient_moreau_eq_gradient_prox hconv hb hf hη]
  calc
    _ ≤ (L : ℝ) * ‖x - prox f η x‖ := hLip.norm_sub_le _ _
    _ ≤ (L : ℝ) * (η * (K : ℝ)) :=
      mul_le_mul_of_nonneg_left (prox_displacement_le hconv hb hη hK x) L.coe_nonneg
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
/-- Original-model differentiability and smoothness derive the missing component
regularity, rather than requiring a separate inverse-scale estimate. -/
theorem component_differentiable_of_sum {f g : E → ℝ}
    (hfg : Differentiable ℝ (fun x => f x + g x)) (hf : Differentiable ℝ f) :
    Differentiable ℝ g := by
  convert hfg.sub hf using 1
  funext x
  change g x = (f x + g x) - f x
  ring

/-- If the full original score and first component are Lipschitz, the second
component's score has their summed Lipschitz constant. -/
theorem component_gradient_lipschitz_of_sum {f g : E → ℝ}
    (hfg : Differentiable ℝ (fun x => f x + g x)) (hf : Differentiable ℝ f)
    {LU Lf : ℝ≥0} (hLU : LipschitzWith LU (gradient (fun x => f x + g x)))
    (hLf : LipschitzWith Lf (gradient f)) :
    LipschitzWith (LU + Lf) (gradient g) := by
  have hg := component_differentiable_of_sum hfg hf
  have heq : gradient g = fun x => gradient (fun y => f y + g y) x - gradient f x := by
    funext x
    rw [gradient_add_of_differentiable hf hg]
    abel
  rw [heq]
  exact hLU.sub hLf

end Score

section IntegralPerturbation
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Two actual integral equations driven by common additive input differ by
the Grönwall response to a uniform drift defect. No derivative of the input is
used, and no error recurrence is assumed. -/
theorem integral_drift_perturbation
    (g k : H → H) (L M : ℝ≥0) (hg : LipschitzWith L g) (hk : LipschitzWith M k)
    (ε : ℝ) (hdefect : ∀ x, ‖g x - k x‖ ≤ ε)
    (x y : H) (B Y Z : ℝ → H) (hY : Continuous Y) (hZ : Continuous Z)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (hZe : ∀ t ∈ Icc 0 T, Z t - y = -(∫ s in 0..t, k (Z s)) + B t) :
    ∀ t ∈ Icc 0 T, ‖Y t - Z t‖ ≤ gronwallBound ‖x - y‖ (L : ℝ) ε t := by
  let D : ℝ → H := fun t => Y t - Z t
  let F : ℝ → H := fun t => (x - y) -
    ((∫ s in 0..t, g (Y s)) - ∫ s in 0..t, k (Z s))
  have hD (t : ℝ) (ht : t ∈ Icc 0 T) : D t = F t := by
    have hy := hYe t ht
    have hz := hZe t ht
    dsimp [D, F]
    rw [sub_eq_iff_eq_add] at hy hz
    rw [hy, hz]
    abel
  have hcY : Continuous (fun s => g (Y s)) := hg.continuous.comp hY
  have hcZ : Continuous (fun s => k (Z s)) := hk.continuous.comp hZ
  have hderiv : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt D (-(g (Y t) - k (Z t))) (Ici t) t := by
    intro t ht
    have hiY := intervalIntegral.integral_hasDerivAt_right
      (hcY.intervalIntegrable 0 t) (hcY.stronglyMeasurableAtFilter volume (𝓝 t)) hcY.continuousAt
    have hiZ := intervalIntegral.integral_hasDerivAt_right
      (hcZ.intervalIntegrable 0 t) (hcZ.stronglyMeasurableAtFilter volume (𝓝 t)) hcZ.continuousAt
    have hf : HasDerivAt F (-(g (Y t) - k (Z t))) t := by
      convert (hasDerivAt_const t (x - y)).sub (hiY.sub hiZ) using 1
      simp
    have hevent : D =ᶠ[𝓝[Ici t] t] F := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds ht.2)] with s hst hsT
      exact hD s ⟨ht.1.trans hst, hsT.le⟩
    exact hf.hasDerivWithinAt.congr_of_eventuallyEq hevent (hD t ⟨ht.1, ht.2.le⟩)
  have hD0 : D 0 = x - y := by
    simpa only [F, intervalIntegral.integral_same, sub_self, sub_zero] using hD 0 ⟨le_rfl, hT⟩
  have hbound (t : ℝ) (_ht : t ∈ Ico 0 T) :
      ‖-(g (Y t) - k (Z t))‖ ≤ (L : ℝ) * ‖D t‖ + ε := by
    rw [norm_neg]
    calc
      _ ≤ ‖g (Y t) - g (Z t)‖ + ‖g (Z t) - k (Z t)‖ := by
        simpa only [dist_eq_norm_sub] using dist_triangle (g (Y t)) (g (Z t)) (k (Z t))
      _ ≤ _ := add_le_add (hg.norm_sub_le _ _) (hdefect _)
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := D)
    (f' := fun t => -(g (Y t) - k (Z t)))
    (δ := ‖x - y‖) (K := (L : ℝ)) (ε := ε)
    (hY.sub hZ).continuousOn hderiv (by rw [hD0]) hbound
  intro t ht
  simpa only [D, sub_zero] using h t ht

end IntegralPerturbation

/-- Explicit finite-horizon coefficient for the mean-field L² smoothing error.
The Grönwall response is `T` at zero smoothness and otherwise
`(exp (2*(L₁+L₂)*T)-1)/(2*(L₁+L₂))`. -/
def meanFieldSmoothingConstant (L₁ L₂ K : ℝ≥0) (T : ℝ) : ℝ :=
  2 * (L₂ : ℝ) * (K : ℝ) * gronwallBound 0 (2 * ((L₁ : ℝ) + (L₂ : ℝ))) 1 T

section MeanField
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {dθ dx : ℕ} {g₁ g₂ : IPLA.Joint dθ dx → ℝ}
    (hg₁ : Differentiable ℝ g₁) (hg₂ : Differentiable ℝ g₂)
    (hconv : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ z, b ≤ g₂ z)
    {L₁ L₂ K : ℝ≥0} (hL₁ : LipschitzWith L₁ (gradient g₁))
    (hL₂ : LipschitzWith L₂ (gradient g₂)) (hK : LipschitzWith K g₂)
    {η : ℝ} (hη : 0 < η)

include hg₁ hg₂ hconv hb hL₁ hL₂ hK hη

/-- Constructed original and smoothed mean-field processes share their actual
initial variable and continuous additive input. Their L² distance, uniformly
over the finite horizon, is bounded by `η` times an explicit η-independent
constant. This is `sup_t ||error_t||₂`, not a pathwise supremum inside an expectation. -/
theorem exists_meanField_smoothing_comparison
    (initial : Lp (IPLA.Joint dθ dx) 2 Q)
    (B : ℝ → Lp (IPLA.Joint dθ dx) 2 Q) (hB : Continuous B) (hB0 : B 0 = 0)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ (hU : LipschitzWith (L₁ + L₂) (gradient (fun x => g₁ x + g₂ x)))
      (hV : LipschitzWith (L₁ + L₂) (gradient (smoothedPotential g₁ g₂ η)))
      (Y Z : ℝ → Lp (IPLA.Joint dθ dx) 2 Q),
      Continuous Y ∧ Continuous Z ∧ Y 0 = initial ∧ Z 0 = initial ∧
      (∀ t ∈ Icc 0 T, Y t - initial =
        -(∫ s in 0..t, lpMeanFieldDrift Q (fun x => g₁ x + g₂ x) hU (Y s)) + B t) ∧
      (∀ t ∈ Icc 0 T, Z t - initial =
        -(∫ s in 0..t, lpMeanFieldDrift Q (smoothedPotential g₁ g₂ η) hV (Z s)) + B t) ∧
      ∀ t ∈ Icc 0 T, ‖Y t - Z t‖ ≤ η * meanFieldSmoothingConstant L₁ L₂ K T := by
  have hU := smoothed_gradient_lipschitz hg₁ hg₂ hL₁ hL₂
  have hV := smoothed_gradient_lipschitz hg₁ (moreau_differentiable hconv hb hη) hL₁
    (smooth_moreau_gradient_lipschitz hconv hb hg₂ hη hL₂)
  let U := fun x => g₁ x + g₂ x
  let V := smoothedPotential g₁ g₂ η
  have hscore (x : IPLA.Joint dθ dx) :
      ‖gradient U x - gradient V x‖ ≤ η * (L₂ : ℝ) * (K : ℝ) := by
    change ‖gradient (fun y => g₁ y + g₂ y) x -
      gradient (fun y => g₁ y + moreau g₂ η y) x‖ ≤ η * (L₂ : ℝ) * (K : ℝ)
    rw [gradient_add_of_differentiable hg₁ hg₂,
      gradient_add_of_differentiable hg₁ (moreau_differentiable hconv hb hη),
      add_sub_add_left_eq_sub]
    exact gradient_moreau_defect_le hconv hb hg₂ hη hL₂ hK x
  have hlp (X : Lp (IPLA.Joint dθ dx) 2 Q) :
      ‖ULA.lpDrift Q (gradient U) hU X - ULA.lpDrift Q (gradient V) hV X‖ ≤
        η * (L₂ : ℝ) * (K : ℝ) := by
    have hpoint : ∀ᵐ ω ∂Q,
        ‖(ULA.lpDrift Q (gradient U) hU X - ULA.lpDrift Q (gradient V) hV X) ω‖ ≤
          η * (L₂ : ℝ) * (K : ℝ) := by
      filter_upwards [Lp.coeFn_sub (ULA.lpDrift Q (gradient U) hU X)
        (ULA.lpDrift Q (gradient V) hV X), ULA.lpDrift_coe Q (gradient U) hU X,
        ULA.lpDrift_coe Q (gradient V) hV X] with ω hsub hu hv
      simpa only [hsub, Pi.sub_apply, hu, hv] using hscore (X ω)
    simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound
      (show 0 ≤ η * (L₂ : ℝ) * (K : ℝ) by positivity) hpoint
  have hdefect (X : Lp (IPLA.Joint dθ dx) 2 Q) :
      ‖lpMeanFieldDrift Q U hU X - lpMeanFieldDrift Q V hV X‖ ≤
        2 * η * (L₂ : ℝ) * (K : ℝ) := by
    unfold lpMeanFieldDrift
    rw [← map_sub]
    exact (meanFieldAverageCLM_norm_le Q _).trans (by nlinarith [hlp X])
  obtain ⟨Y, hY, hY0, hYe⟩ := exists_lp_meanField_integral Q U hU initial B hB hB0 T hT
  obtain ⟨Z, hZ, hZ0, hZe⟩ := exists_lp_meanField_integral Q V hV initial B hB hB0 T hT
  refine ⟨hU, hV, Y, Z, hY, hZ, hY0, hZ0, hYe, hZe, ?_⟩
  have hp := integral_drift_perturbation
    (lpMeanFieldDrift Q U hU) (lpMeanFieldDrift Q V hV) (2 * (L₁ + L₂)) (2 * (L₁ + L₂))
    (lpMeanFieldDrift_lipschitz Q U hU) (lpMeanFieldDrift_lipschitz Q V hV)
    (2 * η * (L₂ : ℝ) * (K : ℝ)) hdefect initial initial B Y Z hY hZ T hT hYe hZe
  intro t ht
  have htime := gronwallBound_mono (δ := 0) (K := (2 * (L₁ + L₂) : ℝ≥0))
    (ε := 2 * η * (L₂ : ℝ) * (K : ℝ)) (by norm_num) (by positivity) (by positivity) ht.2
  have heq : gronwallBound 0 ((2 * (L₁ + L₂) : ℝ≥0) : ℝ)
      (2 * η * (L₂ : ℝ) * (K : ℝ)) T = η * meanFieldSmoothingConstant L₁ L₂ K T := by
    unfold meanFieldSmoothingConstant gronwallBound
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_add]
    split_ifs <;> ring
  have hpt : ‖Y t - Z t‖ ≤ gronwallBound 0 ((2 * (L₁ + L₂) : ℝ≥0) : ℝ)
      (2 * η * (L₂ : ℝ) * (K : ℝ)) t := by
    simpa only [sub_self, norm_zero] using hp t ht
  exact hpt.trans (htime.trans_eq heq)

end MeanField
end ProximalLangevin
