import PBGSO.RawDampedState
import PBGSO.LinearGrowthMoment

/-! Global second moments from a one-sided raw Lyapunov condition.
The drift may be superlinear. Neither a global drift moment nor an expected
energy identity is supplied: the genuine localizations derive both bounds. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.RawCoerciveMoment
open FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q] {D : Driver (I := I) Q} {T : ℝ≥0}
  {L : RawLocalDiffusion (Z := Z) Q D T}
  (U : RawDampedState.Data L)
  (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z,W w⟫_ℝ = ⟪W z,w⟫_ℝ)
  (m C S : ℝ) (hm : 0 < m) (hC : 0 ≤ C) (hS : 0 ≤ S)
  (hcoerc : ∀ z, m*‖z‖^2 ≤ ⟪z,W z⟫_ℝ)
  (hwork : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q, ⟪U.state r ω,W (U.drift r ω)⟫_ℝ ≤ C)
  (hnoise : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q,
    (∑ i, ⟪L.sigma i r ω,W (L.sigma i r ω)⟫_ℝ) ≤ S)
include hW hm hC hS hcoerc hwork hnoise

def budget : ℝ := ((∫ ω, ⟪U.state 0 ω,W (U.state 0 ω)⟫_ℝ ∂Q) + (2*C+S)*T)/m

theorem budget_nonneg : 0 ≤ budget U W m C S := by
  apply div_nonneg _ hm.le
  exact add_nonneg (integral_nonneg (fun ω => (mul_nonneg hm.le (sq_nonneg _)).trans (hcoerc _)))
    (mul_nonneg (by positivity) T.coe_nonneg)

theorem damped_generator_le (n : ℕ) (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    ∀ᵐ ω ∂Q,
      2*⟪U.dampedState n 0 r ω,W (U.dampedDrift n 0 r ω)⟫_ℝ +
        ∑ i, ⟪L.stoppedSigma n i r ω,W (L.stoppedSigma n i r ω)⟫_ℝ ≤ 2*C+S := by
  filter_upwards [hwork r hr,hnoise r hr] with ω hw hn
  by_cases hs : r ≤ (L.stop n ω : ℝ)
  · have hx : U.dampedState n 0 r ω = U.state r ω := by
      rw [RawDampedState.Data.dampedState,DampedContinuation.extension_before _ _ _ hs,
        RawDampedState.Data.clampedState,RawDampedState.timeClamp_eq T hr]
    simpa only [hx,RawDampedState.Data.dampedDrift,DampedContinuation.drift,hs,ite_true,
      RawLocalDiffusion.stoppedSigma,LocalizedDiffusion.stoppedField] using add_le_add (mul_le_mul_of_nonneg_left hw (by norm_num)) hn
  · simp only [RawDampedState.Data.dampedDrift,DampedContinuation.drift,hs,ite_false,
      neg_zero,zero_smul,map_zero,inner_zero_right,mul_zero,RawLocalDiffusion.stoppedSigma,
      LocalizedDiffusion.stoppedField,Finset.sum_const_zero,zero_add]
    positivity

theorem damped_moment_bound (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    ‖(U.dampedState_square n (by norm_num : (0 : ℝ) ≤ 0) t).toLp (U.dampedState n 0 t)‖^2 ≤
      budget U W m C S := by
  let x := U.dampedState n 0
  let b := U.dampedDrift n 0
  let e := fun r => ∫ ω, ⟪x r ω,W (x r ω)⟫_ℝ ∂Q
  let w := fun r => 2*(∫ ω, ⟪x r ω,W (b r ω)⟫_ℝ ∂Q) +
    ∫ ω, ∑ i,⟪L.stoppedSigma n i r ω,W (L.stoppedSigma n i r ω)⟫_ℝ ∂Q
  have he := U.energy_integral n (by norm_num : (0 : ℝ) ≤ 0) W hW
  have hiw := U.work_product_integrable n (by norm_num : (0 : ℝ) ≤ 0) W
  have hid := rawDiffusion_weighted_integrable Q T (L.stoppedSigma n)
    (L.stoppedSigma_strong n) (L.stoppedSigma_square n) W
  have hwle : ∀ᵐ r ∂volume.restrict (Ioc 0 (T : ℝ)), w r ≤ 2*C+S := by
    filter_upwards [hiw.prod_right_ae,hid.prod_right_ae,ae_restrict_mem measurableSet_Ioc]
      with r hw hd hr
    have hi := integral_mono_ae ((hw.const_mul 2).add hd) (integrable_const (2*C+S))
      (damped_generator_le U W hW m C S hm hC hS hcoerc hwork hnoise n r (Ioc_subset_Icc_self hr))
    simp only [Pi.add_apply] at hi
    rw [integral_add (hw.const_mul 2) hd,integral_const_mul] at hi
    simpa [w] using hi
  have hwt : (∫ r in 0..(t : ℝ),w r) ≤ (2*C+S)*t := by
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    have hit : IntegrableOn w (Ioc 0 (t : ℝ)) := he.1.def'.mono_set
      (by simpa only [uIoc_of_le T.coe_nonneg] using Ioc_subset_Ioc le_rfl (show (t : ℝ) ≤ T by exact_mod_cast ht))
    have hwl := ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc le_rfl (show (t : ℝ) ≤ T by exact_mod_cast ht)) hwle
    have hh := integral_mono_ae hit (integrable_const (2*C+S)) hwl
    simpa [Real.volume_Ioc,t.coe_nonneg, mul_comm] using hh
  have heq : e t = (∫ ω,⟪U.state 0 ω,W (U.state 0 ω)⟫_ℝ ∂Q) + ∫ r in 0..(t : ℝ),w r := by
    simpa only [e,w,x,b,RawDampedState.Data.dampedState_zero] using he.2 t ht
  have hx := U.dampedState_square n (by norm_num : (0 : ℝ) ≤ 0) (t : ℝ)
  have hix : Integrable (fun ω => ⟪x t ω,W (x t ω)⟫_ℝ) Q := by
    apply ((memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx |>.const_mul ‖W‖).mono'
      (hx.aestronglyMeasurable.inner (W.continuous.comp_aestronglyMeasurable hx.aestronglyMeasurable))
    filter_upwards with ω
    exact (norm_inner_le_norm _ _).trans (by nlinarith [W.le_opNorm (x t ω),norm_nonneg (x t ω)])
  have hlow : m*‖hx.toLp (x t)‖^2 ≤ e t := by
    rw [LinearGrowthMoment.toLp_norm_sq Q _ hx,← integral_const_mul]
    exact integral_mono (((memLp_two_iff_integrable_sq_norm hx.aestronglyMeasurable).mp hx).const_mul m)
      hix (fun ω => hcoerc (x t ω))
  apply (le_div_iff₀ hm).mpr
  have htime : (2*C+S)*(t : ℝ) ≤ (2*C+S)*T :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast ht) (by positivity)
  change _ ≤ _
  nlinarith

theorem state_moment_bound (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ∃ hx : MemLp (U.state t) 2 Q, ‖hx.toLp (U.state t)‖^2 ≤ budget U W m C S := by
  apply LinearGrowthMoment.localized_limit_memLp Q (fun n => U.dampedState n 0 t) (U.state t)
    (budget_nonneg U W hW m C S hm hC hS hcoerc hwork hnoise)
    (fun n => U.dampedState_square n (by norm_num : (0 : ℝ) ≤ 0) t)
  · intro n
    have hh := damped_moment_bound U W hW m C S hm hC hS hcoerc hwork hnoise n t.toNNReal
      (by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ ht.1]; exact ht.2)
    simpa only [Real.coe_toNNReal _ ht.1] using hh
  · apply Eventually.of_forall
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [U.dampedState_eventually_original 0 t ht ω] with n hn
    exact hn.symm

theorem state_product_memLp :
    MemLp (Function.uncurry U.state) 2 ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  let h (r : ℝ) (hr : r ∈ Ioc 0 (T : ℝ)) :=
    state_moment_bound U W hW m C S hm hC hS hcoerc hwork hnoise r (Ioc_subset_Icc_self hr)
  exact LinearGrowthMoment.product_memLp_of_uniform_moment Q U.state T U.state_strong
    (fun r hr => (h r hr).choose) (fun r hr => (h r hr).choose_spec)

end PBGSO.RawCoerciveMoment
