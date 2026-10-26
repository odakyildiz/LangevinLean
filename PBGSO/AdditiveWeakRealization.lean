import PBGSO.AdditiveJointBridge
import PBGSO.ParameterBound
import UnadjustedLangevin.LangevinUniqueness

/-! # Actual additive L² trajectories realize the quadratic weak coupling
Marginal tests are empty and the pair test is the actual weighted separation.
Thus no marginal Itô assertion is hidden in this constructor: optimiser ODEs
come from zero optimiser input and the paired quadratic forward equation comes
from cancellation of the common additive sampler input. Correct diffusion
matching and stronger marginal generator domains are separate requirements.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace Topology
namespace PBGSO

variable {Ω A G Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Actual global norm-continuous integral trajectory, with zero optimiser
input. This contains equations, not a contraction or derivative conclusion. -/
structure IsGlobalAdditiveIntegralSolution (L : LipschitzDynamics A Z G)
    (Y : ℝ → A × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q) : Prop where
  continuous : Continuous Y
  equation : ∀ t, 0 ≤ t → Y t - Y 0 =
    (∫ r in 0..t, L.field Q (Y r)) + (0, B t)

/-- Primitive global Lipschitz maps and a continuous input give an actual
global L² integral trajectory. Finite Picard choices are glued by their
proved common-input uniqueness, not by a process-existence assumption. -/
theorem exists_global_additive_integral_solution
    (L : LipschitzDynamics A Z G) (initial : A × Lp Z 2 Q)
    (B : ℝ → Lp Z 2 Q) (hB : Continuous B) (hB0 : B 0 = 0) :
    ∃ Y : ℝ → A × Lp Z 2 Q,
      IsGlobalAdditiveIntegralSolution Q L Y B ∧ Y 0 = initial := by
  classical
  let flow := fun n : ℕ ↦ Classical.choose
    (L.exists_integral Q initial B hB hB0 ((n : ℝ) + 1) (Nat.cast_add_one_pos n).le)
  have hs (n : ℕ) : Continuous (flow n) ∧ flow n 0 = initial ∧
      ∀ t ∈ Icc 0 ((n : ℝ) + 1), flow n t - initial =
        (∫ r in 0..t, L.field Q (flow n r)) + (0, B t) :=
    Classical.choose_spec
      (L.exists_integral Q initial B hB hB0 ((n : ℝ) + 1) (Nat.cast_add_one_pos n).le)
  have coherent (m n : ℕ) (r : ℝ) (hr : 0 ≤ r)
      (hm : r ≤ (m : ℝ) + 1) (hn : r ≤ (n : ℝ) + 1) : flow m r = flow n r := by
    have hg : LipschitzWith L.fieldLip (fun z ↦ -L.field Q z) := (L.field_lipschitz Q).neg
    have he := ULA.langevin_integral_unique (fun z ↦ -L.field Q z) L.fieldLip hg initial
      (fun t ↦ (0, B t)) (flow m) (flow n) (hs m).1 (hs n).1 r hr
      (fun t ht ↦ by
        simpa only [intervalIntegral.integral_neg, neg_neg] using
          (hs m).2.2 t ⟨ht.1, ht.2.trans hm⟩)
      (fun t ht ↦ by
        simpa only [intervalIntegral.integral_neg, neg_neg] using
          (hs n).2.2 t ⟨ht.1, ht.2.trans hn⟩)
    exact he ⟨hr, le_rfl⟩
  let Y := fun t : ℝ ↦ flow (Nat.ceil (max 0 t)) (max 0 t)
  have agree (n : ℕ) (r : ℝ) (hr : max 0 r ≤ (n : ℝ) + 1) :
      Y r = flow n (max 0 r) := by
    apply coherent _ n _ (le_max_left _ _)
    · exact (Nat.le_ceil _).trans (by linarith)
    · exact hr
  have hcont : Continuous Y := by
    apply continuous_iff_continuousAt.mpr
    intro t
    let n := Nat.ceil (max 0 t)
    have ht : max 0 t < (n : ℝ) + 1 := lt_of_le_of_lt (Nat.le_ceil _) (by linarith)
    have hc : Continuous (fun r : ℝ ↦ max 0 r) := continuous_const.max continuous_id
    have hev : ∀ᶠ r in 𝓝 t, max 0 r < (n : ℝ) + 1 := hc.continuousAt.eventually (gt_mem_nhds ht)
    apply ((hs n).1.comp hc).continuousAt.congr_of_eventuallyEq
    exact hev.mono fun r hr ↦ agree n r hr.le
  have hzero : Y 0 = initial := by
    have h : Y 0 = flow 0 0 := by simpa only [max_self] using agree 0 0 (by norm_num)
    exact h.trans (hs 0).2.1
  refine ⟨Y, ⟨hcont, ?_⟩, hzero⟩
  intro t ht
  let n := Nat.ceil t
  have hnt : t ≤ (n : ℝ) + 1 := (Nat.le_ceil t).trans (by linarith)
  have he (r : ℝ) (hr : r ∈ Icc 0 t) : Y r = flow n r := by
    simpa only [max_eq_right hr.1] using agree n r (by rw [max_eq_right hr.1]; exact hr.2.trans hnt)
  have hint : (∫ r in 0..t, L.field Q (Y r)) = ∫ r in 0..t, L.field Q (flow n r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht] at hr
    change L.field Q (Y r) = L.field Q (flow n r)
    rw [he r hr]
  rw [he t ⟨ht, le_rfl⟩, hzero, hint]
  exact (hs n).2.2 t ⟨ht, hnt⟩

namespace IsGlobalAdditiveIntegralSolution
variable {Q} {L : LipschitzDynamics A Z G} {Y W : ℝ → A × Lp Z 2 Q}
  {B : ℝ → Lp Z 2 Q}

/-- Zero optimiser input yields its actual ODE at every nonnegative time. -/
theorem optimizer_hasDerivWithinAt
    (H : IsGlobalAdditiveIntegralSolution Q L Y B) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r ↦ (Y r).1) (L.field Q (Y t)).1 (Ici 0) t := by
  let f := fun r ↦ (L.field Q (Y r)).1
  have hc : Continuous f := continuous_fst.comp ((L.field_lipschitz Q).continuous.comp H.continuous)
  have heq (r : ℝ) (hr : 0 ≤ r) : (Y r).1 = (Y 0).1 + ∫ u in 0..r, f u := by
    have he := congrArg Prod.fst (H.equation r hr)
    have hint : IntervalIntegrable (fun u ↦ L.field Q (Y u)) volume 0 r :=
      ((L.field_lipschitz Q).continuous.comp H.continuous).intervalIntegrable 0 r
    have hi := (ContinuousLinearMap.fst ℝ A (Lp Z 2 Q)).intervalIntegral_comp_comm hint
    change (∫ u in 0..r, f u) = (∫ u in 0..r, L.field Q (Y u)).1 at hi
    simp only [Prod.fst_sub, Prod.fst_add, add_zero] at he
    rw [← hi] at he
    exact sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _)
  have hint : IntervalIntegrable f volume 0 t := hc.intervalIntegrable 0 t
  have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
    hint (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt
  exact (hd.const_add (Y 0).1).hasDerivWithinAt.congr heq (heq t ht)

/-- The full difference ODE is derived from the actual two integral
equations; the common additive input cancels. -/
theorem difference_hasDerivWithinAt
    (HY : IsGlobalAdditiveIntegralSolution Q L Y B)
    (HW : IsGlobalAdditiveIntegralSolution Q L W B) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r ↦ Y r - W r)
      (L.field Q (Y t) - L.field Q (W t)) (Ici 0) t := by
  let f := fun r ↦ L.field Q (Y r) - L.field Q (W r)
  have hc : Continuous f := ((L.field_lipschitz Q).continuous.comp HY.continuous).sub
    ((L.field_lipschitz Q).continuous.comp HW.continuous)
  have heq (r : ℝ) (hr : 0 ≤ r) : Y r - W r = Y 0 - W 0 + ∫ u in 0..r, f u := by
    have hiy : IntervalIntegrable (fun u ↦ L.field Q (Y u)) volume 0 r :=
      ((L.field_lipschitz Q).continuous.comp HY.continuous).intervalIntegrable 0 r
    have hiw : IntervalIntegrable (fun u ↦ L.field Q (W u)) volume 0 r :=
      ((L.field_lipschitz Q).continuous.comp HW.continuous).intervalIntegrable 0 r
    rw [intervalIntegral.integral_sub hiy hiw]
    have hy := HY.equation r hr
    have hw := HW.equation r hr
    rw [sub_eq_iff_eq_add] at hy hw
    rw [hy, hw]
    module
  have hint : IntervalIntegrable f volume 0 t := hc.intervalIntegrable 0 t
  have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
    hint (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt
  exact (hd.const_add (Y 0 - W 0)).hasDerivWithinAt.congr heq (heq t ht)

/-- Primitive Lipschitz uniqueness identifies any two actual global
integral trajectories with the same input and initial state. -/
theorem eq_of_initial
    (HY : IsGlobalAdditiveIntegralSolution Q L Y B)
    (HW : IsGlobalAdditiveIntegralSolution Q L W B) (hzero : Y 0 = W 0)
    (t : ℝ) (ht : 0 ≤ t) : Y t = W t := by
  have hg : LipschitzWith L.fieldLip (fun z ↦ -L.field Q z) := (L.field_lipschitz Q).neg
  have he := ULA.langevin_integral_unique (fun z ↦ -L.field Q z) L.fieldLip hg (Y 0)
    (fun r ↦ (0, B r)) Y W HY.continuous HW.continuous t ht
    (fun r hr ↦ by simpa only [intervalIntegral.integral_neg, neg_neg] using HY.equation r hr.1)
    (fun r hr ↦ by simpa only [intervalIntegral.integral_neg, neg_neg, hzero] using HW.equation r hr.1)
  exact he ⟨ht, le_rfl⟩

/-- Actual sampler marginal laws of the constructed trajectory. -/
def samplerLaw (Y : ℝ → A × Lp Z 2 Q) (t : ℝ) : Measure Z := Q.map (Y t).2

/-- The actual marginal meets the weak contract with empty test family.
This asserts the true optimiser ODE, probability, P₂ and observation
integrability; it does not assert any unproved marginal Itô formula. -/
theorem isWeakSolution_empty
    (HY : IsGlobalAdditiveIntegralSolution Q L Y B) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) :
    M.IsWeakSolution ∅ (fun t ↦ (Y t).1) (samplerLaw (Q := Q) Y) where
  probability := by
    intro t _
    exact (Measure.isProbabilityMeasure_map_iff
      (Lp.aestronglyMeasurable (Y t).2).aemeasurable).mpr inferInstance
  second_moment := fun t _ ↦ lp_law_second_moment Q (Y t).2
  gradient_integrable := by
    intro t _
    letI : IsProbabilityMeasure (Q.map (Y t).2) :=
      (Measure.isProbabilityMeasure_map_iff
        (Lp.aestronglyMeasurable (Y t).2).aemeasurable).mpr inferInstance
    dsimp [samplerLaw]
    simp_rw [H.observation]
    exact observation_integrable_of_lipschitz (Q.map (Y t).2) _
      (L.observation_state (Y t).1) (lp_law_second_moment Q (Y t).2)
  optimizer_ode := by
    intro t ht
    have hd := HY.optimizer_hasDerivWithinAt t ht
    convert hd using 1
    dsimp [Model.optimizerField, samplerLaw, LipschitzDynamics.field]
    rw [model_meanGradient_eq_expectedObservation Q L M H (Y t).1 (Y t).2,
      H.response t ht]
  test_integrable := by simp
  generator_integrable := by simp
  forward_equation := by simp

/-- The quadratic separation test's weak equation follows from shared-input
cancellation in L² and the exact source synchronous-generator computation. -/
theorem pair_quadratic_forward
    (HY : IsGlobalAdditiveIntegralSolution Q L Y B)
    (HW : IsGlobalAdditiveIntegralSolution Q L W B)
    (M : Model A G Z X I) (H : AdditiveModelCompatibility L M)
    (D : TwistedGeometry A Z) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun r ↦ ∫ zz, couplingQuadratic D zz ∂samplerPairLaw Q (Y r).2 (W r).2)
      (∫ zz, synchronousGenerator M (Y t).1 (W t).1 (couplingQuadratic D) zz
        ∂samplerPairLaw Q (Y t).2 (W t).2) (Ici 0) t := by
  let Bs : Lp Z 2 Q →L[ℝ] Lp Z 2 Q →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (Lp Z 2 Q))
      (D.samplerWeight.compLpL 2 Q)
  have hdiff := HY.difference_hasDerivWithinAt HW t ht
  have hx := (ContinuousLinearMap.snd ℝ A (Lp Z 2 Q)).hasFDerivAt.comp_hasDerivWithinAt t hdiff
  have hF := (quadratic_hasFDerivAt Bs ((Y t).2 - (W t).2)).comp_hasDerivWithinAt t hx
  have hsym (u v : Lp Z 2 Q) : Bs u v = Bs v u := by
    change ⟪u, D.samplerWeight.compLpL 2 Q v⟫_ℝ = ⟪v, D.samplerWeight.compLpL 2 Q u⟫_ℝ
    rw [lp_weighted_pairing_eq_integral, lp_weighted_pairing_eq_integral]
    apply integral_congr_ae
    exact ae_of_all Q fun ω ↦ (D.sampler_symmetric _ _).trans (real_inner_comm _ _)
  have he (r : ℝ) : (∫ zz, couplingQuadratic D zz ∂samplerPairLaw Q (Y r).2 (W r).2) =
      Bs ((Y r).2 - (W r).2) ((Y r).2 - (W r).2) :=
    samplerPairLaw_cost_integral Q D (Y r).2 (W r).2
  have hv : (∫ zz, synchronousGenerator M (Y t).1 (W t).1 (couplingQuadratic D) zz
      ∂samplerPairLaw Q (Y t).2 (W t).2) =
      2 * Bs ((Y t).2 - (W t).2) (L.field Q (Y t) - L.field Q (W t)).2 := by
    simp_rw [synchronousGenerator_quadratic]
    rw [integral_const_mul, samplerPairLaw_work_integral Q L M H D]
    rfl
  rw [hv]
  convert hF using 1
  · funext r
    exact he r
  · change 2 * Bs ((Y t).2 - (W t).2) (L.field Q (Y t) - L.field Q (W t)).2 =
      Bs ((Y t).2 - (W t).2) (L.field Q (Y t) - L.field Q (W t)).2 +
      Bs (L.field Q (Y t) - L.field Q (W t)).2 ((Y t).2 - (W t).2)
    rw [hsym]
    ring

/-- Actual integral trajectories give a genuine quadratic weak coupling,
with actual marginal pushforward laws. No final contraction or law-equality
bound is assumed. Marginal tests are exactly empty. -/
theorem isCoupledWeakSolution_quadratic
    (HY : IsGlobalAdditiveIntegralSolution Q L Y B)
    (HW : IsGlobalAdditiveIntegralSolution Q L W B)
    (M : Model A G Z X I) (H : AdditiveModelCompatibility L M)
    (D : TwistedGeometry A Z) :
    IsCoupledWeakSolution M ∅ {couplingQuadratic D}
      (fun t ↦ (Y t).1) (fun t ↦ (W t).1)
      (samplerLaw (Q := Q) Y) (samplerLaw (Q := Q) W)
      (fun t ↦ samplerPairLaw Q (Y t).2 (W t).2) where
  left := HY.isWeakSolution_empty M H
  right := HW.isWeakSolution_empty M H
  coupling := fun t _ ↦ samplerPairLaw_coupling Q (Y t).2 (W t).2
  test_integrable := by
    intro φ hφ t _
    have he : φ = couplingQuadratic D := Set.mem_singleton_iff.mp hφ
    subst φ
    exact samplerPairLaw_cost_integrable Q D (Y t).2 (W t).2
  generator_integrable := by
    intro φ hφ t _
    have he : φ = couplingQuadratic D := Set.mem_singleton_iff.mp hφ
    subst φ
    have heq : synchronousGenerator M (Y t).1 (W t).1 (couplingQuadratic D) =
        fun zz ↦ 2 * samplerCouplingWork M D (Y t).1 (W t).1 zz :=
      funext (synchronousGenerator_quadratic M D (Y t).1 (W t).1)
    rw [heq]
    exact (samplerPairLaw_work_integrable Q L M H D (Y t).1 (W t).1 (Y t).2 (W t).2).const_mul 2
  forward_equation := by
    intro φ hφ t ht
    have he : φ = couplingQuadratic D := Set.mem_singleton_iff.mp hφ
    subst φ
    exact HY.pair_quadratic_forward HW M H D t ht

end IsGlobalAdditiveIntegralSolution
end PBGSO
