import PBGSO.PaperTheorems
import KineticLangevin.IntegralCoupling

/-!
# Contraction of actual common-input integral solutions

The result applies to arbitrary nonlinear, nonconservative drifts. The
ambient Banach space can be an optimiser state times an L² sampler state;
the continuous linear transformation provides a Hilbert quadratic metric.
The energy differential inequality is derived from the integral equations,
not supplied as a hypothesis. Shared additive noise cancels in those
equations. State-dependent stochastic noise requires a separate Itô proof.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace NNReal Topology
namespace PBGSO

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Squared transformed-distance decay for actual integral solutions of an
arbitrary Lipschitz drift driven by the same additive input. -/
theorem transformed_additive_integral_energy_decay
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (C : E →L[ℝ] H) (ρ : ℝ)
    (hmono : ∀ x y, ρ * ‖C (x - y)‖ ^ 2 ≤
      ⟪C (x - y), C (g x - g y)⟫)
    (Y Z B : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T,
      Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T,
      Z t - Z 0 = -(∫ s in 0..t, g (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖C (Y t - Z t)‖ ^ 2 ≤
      ‖C (Y 0 - Z 0)‖ ^ 2 * Real.exp (-2 * ρ * t) := by
  let F : ℝ → ℝ := fun r => ‖C (Y r - Z r)‖ ^ 2
  let F' : ℝ → ℝ := fun r =>
    -2 * ⟪C (Y r - Z r), C (g (Y r) - g (Z r))⟫
  have hc : ContinuousOn F (Icc 0 T) :=
    ((C.continuous.comp (hY.sub hZ)).norm.pow 2).continuousOn
  have hd : ∀ r ∈ Ico 0 T, HasDerivWithinAt F (F' r) (Ici r) r := by
    intro r hr
    have hdiff := KineticLangevin.integral_difference_hasDerivWithinAt
      g L hg Y Z B hY hZ T heY heZ r hr
    have hC := C.hasFDerivAt.comp_hasDerivWithinAt r hdiff
    simpa only [F, F', Function.comp_def, map_neg, inner_neg_right,
      mul_neg, neg_mul] using hC.norm_sq
  have hm : ∀ r ∈ Ico 0 T, F' r ≤ -2 * ρ * F r := by
    intro r hr
    dsimp [F', F]
    have h := hmono (Y r) (Z r)
    nlinarith
  exact energy_decay hc hd hm t ht

/-- Exponential contraction in the specified transformed Hilbert norm. -/
theorem transformed_additive_integral_contraction
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (C : E →L[ℝ] H) (ρ : ℝ)
    (hmono : ∀ x y, ρ * ‖C (x - y)‖ ^ 2 ≤
      ⟪C (x - y), C (g x - g y)⟫)
    (Y Z B : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T,
      Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T,
      Z t - Z 0 = -(∫ s in 0..t, g (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖C (Y t - Z t)‖ ≤ Real.exp (-ρ * t) * ‖C (Y 0 - Z 0)‖ := by
  have h := transformed_additive_integral_energy_decay
    g L hg C ρ hmono Y Z B hY hZ T heY heZ t ht
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  have hexp : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  simpa [mul_comm] using h

/-- The paper's square-root condition-number prefactor, now derived from
the actual integral equations and monotonicity of their drift. -/
theorem additive_integral_contraction_with_condition_number
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (C : E →L[ℝ] H) (ρ lower upper : ℝ)
    (hlower : 0 < lower) (hupper : 0 ≤ upper)
    (hcompLower : ∀ x, lower * ‖x‖ ^ 2 ≤ ‖C x‖ ^ 2)
    (hcompUpper : ∀ x, ‖C x‖ ^ 2 ≤ upper * ‖x‖ ^ 2)
    (hmono : ∀ x y, ρ * ‖C (x - y)‖ ^ 2 ≤
      ⟪C (x - y), C (g x - g y)⟫)
    (Y Z B : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T,
      Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T,
      Z t - Z 0 = -(∫ s in 0..t, g (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖Y t - Z t‖ ≤ Real.sqrt (upper / lower) * Real.exp (-ρ * t) *
      ‖Y 0 - Z 0‖ := by
  have hdec := transformed_additive_integral_energy_decay
    g L hg C ρ hmono Y Z B hY hZ T heY heZ t ht
  have hexp : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hupper hlower.le), hexp]
  apply (mul_le_mul_iff_of_pos_left hlower).mp
  have hi := mul_le_mul_of_nonneg_right (hcompUpper (Y 0 - Z 0))
    (Real.exp_pos (-2 * ρ * t)).le
  calc
    lower * ‖Y t - Z t‖ ^ 2 ≤ ‖C (Y t - Z t)‖ ^ 2 := hcompLower _
    _ ≤ upper * ‖Y 0 - Z 0‖ ^ 2 * Real.exp (-2 * ρ * t) := hdec.trans hi
    _ = lower * (upper / lower * Real.exp (-2 * ρ * t) * ‖Y 0 - Z 0‖ ^ 2) := by
      field_simp
      <;> ring

/-- Common additive noise also cancels when the reference trajectory has
an explicit continuous forcing. The resulting derivative is derived by
the fundamental theorem of calculus from the two integral equations. -/
theorem forced_integral_difference_hasDerivWithinAt
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (Y Z B f : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z)
    (hf : Continuous f) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T,
      Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T,
      Z t - Z 0 = -(∫ s in 0..t, g (Z s)) + (∫ s in 0..t, f s) + B t)
    (t : ℝ) (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun r => Y r - Z r)
      (-(g (Y t) - g (Z t) + f t)) (Ici t) t := by
  have hforce : Continuous (fun s => g (Y s) - g (Z s) + f s) :=
    ((hg.continuous.comp hY).sub (hg.continuous.comp hZ)).add hf
  have heq : ∀ r ∈ Icc 0 T,
      Y r - Z r = Y 0 - Z 0 - ∫ s in 0..r, g (Y s) - g (Z s) + f s := by
    intro r hr
    have hiY : IntervalIntegrable (fun s => g (Y s)) volume 0 r :=
      (hg.continuous.comp hY).intervalIntegrable _ _
    have hiZ : IntervalIntegrable (fun s => g (Z s)) volume 0 r :=
      (hg.continuous.comp hZ).intervalIntegrable _ _
    have hiYZ : IntervalIntegrable (fun s => g (Y s) - g (Z s)) volume 0 r :=
      hiY.sub hiZ
    rw [intervalIntegral.integral_add hiYZ (hf.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_sub hiY hiZ]
    have hy := heY r hr
    have hz := heZ r hr
    rw [sub_eq_iff_eq_add] at hy hz
    rw [hy, hz]
    abel
  have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
    (hforce.intervalIntegrable 0 t)
    (hforce.stronglyMeasurableAtFilter volume (𝓝 t)) hforce.continuousAt
  have hmem : Icc 0 T ∈ 𝓝[Ici t] t := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2)] with r hr hrT
    exact ⟨ht.1.trans hr, hrT⟩
  have he : (fun r => Y r - Z r) =ᶠ[𝓝[Ici t] t]
      (fun r => Y 0 - Z 0 - ∫ s in 0..r, g (Y s) - g (Z s) + f s) := by
    filter_upwards [hmem] with r hr
    exact heq r hr
  exact (hd.const_sub (Y 0 - Z 0)).hasDerivWithinAt.congr_of_eventuallyEq he
    (heq t ⟨ht.1, ht.2.le⟩)

/-- Exact perturbation bound for actual integral solutions. It is uniform
over time when the transformed forcing has uniform bound `c`. This is the
deterministic comparison mechanism behind the finite-particle estimate. -/
theorem forced_additive_integral_contraction
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (C : E →L[ℝ] H) (ρ c : ℝ) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hmono : ∀ x y, ρ * ‖C (x - y)‖ ^ 2 ≤
      ⟪C (x - y), C (g x - g y)⟫)
    (Y Z B f : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z)
    (hf : Continuous f) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T,
      Y t - Y 0 = -(∫ s in 0..t, g (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T,
      Z t - Z 0 = -(∫ s in 0..t, g (Z s)) + (∫ s in 0..t, f s) + B t)
    (hforcing : ∀ t ∈ Icc 0 T, ‖C (f t)‖ ≤ c)
    (hinitial : Y 0 = Z 0) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖C (Y t - Z t)‖ ≤ c / ρ * (1 - Real.exp (-ρ * t)) := by
  let F : ℝ → ℝ := fun r => ‖C (Y r - Z r)‖ ^ 2
  let F' : ℝ → ℝ := fun r => 2 *
    ⟪C (Y r - Z r), C (-(g (Y r) - g (Z r) + f r))⟫
  have hcont : ContinuousOn F (Icc 0 T) :=
    ((C.continuous.comp (hY.sub hZ)).norm.pow 2).continuousOn
  have hder : ∀ r ∈ Ico 0 T, HasDerivWithinAt F (F' r) (Ici r) r := by
    intro r hr
    exact (C.hasFDerivAt.comp_hasDerivWithinAt r
      (forced_integral_difference_hasDerivWithinAt
        g L hg Y Z B f hY hZ hf T heY heZ r hr)).norm_sq
  have hnonneg : ∀ r ∈ Icc 0 T, 0 ≤ F r := fun r _ => sq_nonneg _
  have hzero : F 0 = 0 := by simp [F, hinitial]
  have hdiss : ∀ r ∈ Ico 0 T,
      F' r ≤ -2 * ρ * F r + 2 * c * Real.sqrt (F r) := by
    intro r hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.le⟩
    have hm := hmono (Y r) (Z r)
    have hs := real_inner_le_norm (C (Y r - Z r)) (-C (f r))
    rw [norm_neg] at hs
    have hb := mul_le_mul_of_nonneg_left (hforcing r hr') (norm_nonneg (C (Y r - Z r)))
    dsimp [F', F]
    rw [Real.sqrt_sq (norm_nonneg _), map_neg, map_add,
      inner_neg_right, inner_add_right]
    simp only [inner_neg_right] at hs
    nlinarith
  have h := forced_energy_bound hρ hc hcont hder hnonneg hzero hdiss t ht
  simpa only [F, Real.sqrt_sq (norm_nonneg _)] using h

end PBGSO
