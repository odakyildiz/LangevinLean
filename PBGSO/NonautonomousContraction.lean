import PBGSO.PaperTheorems
import KineticLangevin.IntegralCoupling

/-!
# Time-dependent general optimiser responses

These trajectory theorems allow an arbitrary time-dependent drift, as in
the paper's `Ψ_t`. They do not require the drift to be a gradient or the
sampler to be overdamped. Existence is not asserted: the input trajectories
must satisfy the displayed actual integral equations with common additive
noise. Continuity of each drift along each trajectory is explicit.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace Topology
namespace PBGSO

variable {E H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The difference of two actual common-input integral equations has the
difference of their drifts as right derivative. No time homogeneity is
needed. -/
theorem common_input_difference_hasDerivWithinAt
    (Y Z B a b : ℝ → E) (ha : Continuous a) (hb : Continuous b) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 = (∫ s in 0..t, a s) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 = (∫ s in 0..t, b s) + B t)
    (t : ℝ) (ht : t ∈ Ico 0 T) :
    HasDerivWithinAt (fun r => Y r - Z r) (a t - b t) (Ici t) t := by
  have heq : ∀ r ∈ Icc 0 T,
      Y r - Z r = Y 0 - Z 0 + ∫ s in 0..r, a s - b s := by
    intro r hr
    rw [intervalIntegral.integral_sub (ha.intervalIntegrable _ _)
      (hb.intervalIntegrable _ _)]
    have hy := heY r hr
    have hz := heZ r hr
    rw [sub_eq_iff_eq_add] at hy hz
    rw [hy, hz]
    abel
  have hdiff : Continuous (fun s => a s - b s) := ha.sub hb
  have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
    (hdiff.intervalIntegrable 0 t)
    (hdiff.stronglyMeasurableAtFilter volume (𝓝 t)) hdiff.continuousAt
  have hmem : Icc 0 T ∈ 𝓝[Ici t] t := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht.2)] with r hr hrT
    exact ⟨ht.1.trans hr, hrT⟩
  have he : (fun r => Y r - Z r) =ᶠ[𝓝[Ici t] t]
      (fun r => Y 0 - Z 0 + ∫ s in 0..r, a s - b s) := by
    filter_upwards [hmem] with r hr
    exact heq r hr
  exact (hd.const_add (Y 0 - Z 0)).hasDerivWithinAt.congr_of_eventuallyEq he
    (heq t ⟨ht.1, ht.2.le⟩)

/-- The paper's contraction mechanism for an arbitrary time-dependent
general drift. The full deterministic optimizer/sampler drift can be used
here on a lifted Banach space, with any Hilbert quadratic metric `C`. -/
theorem nonautonomous_additive_integral_energy_decay
    (g : ℝ → E → E) (C : E →L[ℝ] H) (ρ T : ℝ)
    (hmono : ∀ r ∈ Ico 0 T, ∀ x y,
      ρ * ‖C (x - y)‖ ^ 2 ≤ ⟪C (x - y), C (g r x - g r y)⟫)
    (Y Z B : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z)
    (hgY : Continuous (fun r => g r (Y r)))
    (hgZ : Continuous (fun r => g r (Z r)))
    (heY : ∀ t ∈ Icc 0 T,
      Y t - Y 0 = -(∫ s in 0..t, g s (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T,
      Z t - Z 0 = -(∫ s in 0..t, g s (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖C (Y t - Z t)‖ ^ 2 ≤
      ‖C (Y 0 - Z 0)‖ ^ 2 * Real.exp (-2 * ρ * t) := by
  let F : ℝ → ℝ := fun r => ‖C (Y r - Z r)‖ ^ 2
  let F' : ℝ → ℝ := fun r =>
    -2 * ⟪C (Y r - Z r), C (g r (Y r) - g r (Z r))⟫
  have hc : ContinuousOn F (Icc 0 T) :=
    ((C.continuous.comp (hY.sub hZ)).norm.pow 2).continuousOn
  have hd : ∀ r ∈ Ico 0 T, HasDerivWithinAt F (F' r) (Ici r) r := by
    intro r hr
    have hy : ∀ u ∈ Icc 0 T,
        Y u - Y 0 = (∫ s in 0..u, -g s (Y s)) + B u := by
      intro u hu
      simpa only [intervalIntegral.integral_neg] using heY u hu
    have hz : ∀ u ∈ Icc 0 T,
        Z u - Z 0 = (∫ s in 0..u, -g s (Z s)) + B u := by
      intro u hu
      simpa only [intervalIntegral.integral_neg] using heZ u hu
    have hdiff := common_input_difference_hasDerivWithinAt
      Y Z B (fun s => -g s (Y s)) (fun s => -g s (Z s))
      hgY.neg hgZ.neg T hy hz r hr
    have hdiff' : HasDerivWithinAt (fun r => Y r - Z r)
        (-(g r (Y r) - g r (Z r))) (Ici r) r := by
      convert hdiff using 1 <;> abel
    have hC := C.hasFDerivAt.comp_hasDerivWithinAt r hdiff'
    simpa only [F, F', Function.comp_def, map_neg, inner_neg_right,
      mul_neg, neg_mul] using hC.norm_sq
  have hm : ∀ r ∈ Ico 0 T, F' r ≤ -2 * ρ * F r := by
    intro r hr
    dsimp [F', F]
    have h := hmono r hr (Y r) (Z r)
    nlinarith
  exact energy_decay hc hd hm t ht

/-- The square-root form, including arbitrary time-dependent optimiser
responses and arbitrary continuous common additive inputs. -/
theorem nonautonomous_additive_integral_contraction
    (g : ℝ → E → E) (C : E →L[ℝ] H) (ρ T : ℝ)
    (hmono : ∀ r ∈ Ico 0 T, ∀ x y,
      ρ * ‖C (x - y)‖ ^ 2 ≤ ⟪C (x - y), C (g r x - g r y)⟫)
    (Y Z B : ℝ → E) (hY : Continuous Y) (hZ : Continuous Z)
    (hgY : Continuous (fun r => g r (Y r)))
    (hgZ : Continuous (fun r => g r (Z r)))
    (heY : ∀ t ∈ Icc 0 T,
      Y t - Y 0 = -(∫ s in 0..t, g s (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T,
      Z t - Z 0 = -(∫ s in 0..t, g s (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖C (Y t - Z t)‖ ≤ Real.exp (-ρ * t) * ‖C (Y 0 - Z 0)‖ := by
  have h := nonautonomous_additive_integral_energy_decay
    g C ρ T hmono Y Z B hY hZ hgY hgZ heY heZ t ht
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  have hexp : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  simpa [mul_comm] using h

end PBGSO
