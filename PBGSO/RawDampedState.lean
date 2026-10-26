import PBGSO.RawStoppingAdaptation
import PBGSO.DampedContinuation
import PBGSO.RawStoppingCoordinates
import PBGSO.StrongMartingaleRadius
import PBGSO.ConstructedRandomVariationIntegral
import PBGSO.ConstructedRandomVariationWork

/-! # Actual raw damped localizations of an original strong equation -/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.RawDampedState
open FilteredBrownian RawStoppingCoordinates
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {T : ℝ≥0}

/-- Natural raw strong-equation data, before any global coefficient moment
or stopped energy is known. The noise is the actual constructed local Ito
integral. -/
structure Data (L : RawLocalDiffusion (Z := Z) Q D T) where
  state : ℝ → Ω → Z
  drift : ℝ → Ω → Z
  state_strong : StronglyMeasurable (Function.uncurry state)
  drift_strong : StronglyMeasurable (Function.uncurry drift)
  drift_control : ∀ r ω, ‖drift r ω‖ ≤ L.q r ω
  initial_square : MemLp (state 0) 2 Q
  state_adapted : ∀ t : ℝ≥0, AEStronglyMeasurable[D.filtration t] (state t) Q
  state_continuous : ∀ᵐ ω ∂Q, ContinuousOn (fun r => state r ω) (Icc 0 (T : ℝ))
  equation : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ), state t ω = state 0 ω +
    (∫ r in 0..t, drift r ω) + L.localNoise t.toNNReal ω

def timeClamp (T : ℝ≥0) (r : ℝ) : ℝ := max 0 (min r T)

theorem timeClamp_mem (T : ℝ≥0) (r : ℝ) : timeClamp T r ∈ Icc 0 (T : ℝ) :=
  ⟨le_max_left _ _, max_le T.coe_nonneg (min_le_right _ _)⟩

theorem timeClamp_eq (T : ℝ≥0) {r : ℝ} (hr : r ∈ Icc 0 (T : ℝ)) : timeClamp T r = r := by
  rw [timeClamp,min_eq_left hr.2,max_eq_right hr.1]

theorem timeClamp_min (T : ℝ≥0) (τ r : ℝ) (hτ : τ ∈ Icc 0 (T : ℝ)) :
    timeClamp T (min r τ) = min (timeClamp T r) τ := by
  dsimp only [timeClamp]
  grind [min_def,max_def]

namespace Data
variable {L : RawLocalDiffusion (Z := Z) Q D T} (U : Data L)

def clampedState (r : ℝ) (ω : Ω) := U.state (timeClamp T r) ω

def stoppedDrift (n : ℕ) := LocalizedDiffusion.stoppedField (L.stop n) U.drift

def stoppedState (n : ℕ) := RawStoppingCoordinates.stoppedState (L.stop n) U.state

theorem stoppedDrift_strong (n : ℕ) : StronglyMeasurable (Function.uncurry (U.stoppedDrift n)) :=
  LocalizedDiffusion.stoppedField_stronglyMeasurable _ (L.stop_measurable n) U.drift U.drift_strong

theorem stoppedDrift_paths (n : ℕ) : ∀ ω,
    IntervalIntegrable (fun r => U.stoppedDrift n r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖U.stoppedDrift n r ω‖) ≤ n := by
  intro ω
  have hi : IntegrableOn (fun r => U.drift r ω) (Ioc 0 (T : ℝ)) :=
    (L.q_local ω).mono' U.drift_strong.of_uncurry_right.aestronglyMeasurable
      (Eventually.of_forall (fun r => U.drift_control r ω))
  have hs : IntegrableOn (fun r => U.stoppedDrift n r ω) (Ioc 0 (T : ℝ)) := by
    change Integrable ((Iic (L.stop n ω : ℝ)).indicator (fun r => U.drift r ω)) _
    exact hi.indicator measurableSet_Iic
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr hs, ?_⟩
  rw [intervalIntegral.integral_of_le T.coe_nonneg]
  have hm : ∀ r, ‖U.stoppedDrift n r ω‖ ≤
      LocalizedDiffusion.stoppedField (L.stop n) L.q r ω := by
    intro r
    change ‖if r ≤ (L.stop n ω : ℝ) then U.drift r ω else 0‖ ≤
      if r ≤ (L.stop n ω : ℝ) then L.q r ω else 0
    split_ifs
    · exact U.drift_control r ω
    · simp
  have hqi : IntegrableOn (fun r => LocalizedDiffusion.stoppedField (L.stop n) L.q r ω)
      (Ioc 0 (T : ℝ)) := (L.q_local ω).indicator measurableSet_Iic
  calc
    _ ≤ ∫ r in Ioc 0 (T : ℝ), LocalizedDiffusion.stoppedField (L.stop n) L.q r ω :=
      integral_mono hs.norm hqi hm
    _ = ∫ r in Ioc 0 (L.stop n ω : ℝ), L.q r ω := by
      rw [← intervalIntegral.integral_of_le T.coe_nonneg,
        stoppedField_integral (L.stop n) L.q (T : ℝ) T.coe_nonneg ω,
        min_eq_right (show (L.stop n ω : ℝ) ≤ T by exact_mod_cast L.stop_bound n ω),
        intervalIntegral.integral_of_le (L.stop n ω).coe_nonneg]
    _ ≤ n := L.stop_energy_bound n ω

/-- The genuine stopped raw equation holds on a single event for every
time; its stochastic part is the actual computed martingale version. -/
theorem stopped_equation (n : ℕ) : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ),
    U.stoppedState n t ω = U.state 0 ω +
      (∫ r in 0..t, U.stoppedDrift n r ω) + L.version n t.toNNReal ω := by
  filter_upwards [U.equation,L.localNoise_stopped] with ω heq hn
  intro t ht
  have hmin : (min t (L.stop n ω : ℝ)).toNNReal = min t.toNNReal (L.stop n ω) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_min, Real.coe_toNNReal _ (le_min ht.1 (L.stop n ω).coe_nonneg),
      Real.coe_toNNReal _ ht.1]
  change U.state (min t (L.stop n ω : ℝ)) ω = _
  rw [heq _ ⟨le_min ht.1 (L.stop n ω).coe_nonneg,(min_le_left _ _).trans ht.2⟩,
    ← stoppedField_integral (L.stop n) U.drift t ht.1 ω,hmin,
    ← hn n t.toNNReal (by rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ ht.1]; exact ht.2)]
  rfl

theorem clampedState_strong : StronglyMeasurable (Function.uncurry U.clampedState) :=
  U.state_strong.comp_measurable
    (((by unfold timeClamp; fun_prop : Continuous (timeClamp T)).measurable.comp measurable_fst).prodMk measurable_snd)

theorem clampedState_continuous : ∀ᵐ ω ∂Q, Continuous (fun r => U.clampedState r ω) := by
  filter_upwards [U.state_continuous] with ω hc
  exact hc.comp_continuous (by unfold timeClamp; fun_prop : Continuous (timeClamp T)) (timeClamp_mem T)

theorem clampedState_adapted (t : ℝ≥0) :
    AEStronglyMeasurable[D.filtration t] (U.clampedState t) Q := by
  by_cases h : t ≤ T
  · have he : U.clampedState t = U.state t := by
      funext ω
      rw [clampedState,timeClamp_eq T ⟨t.coe_nonneg,by exact_mod_cast h⟩]
    rw [he]
    exact U.state_adapted t
  · have he : U.clampedState t = U.state T := by
      funext ω
      simp only [clampedState,timeClamp,min_eq_right (show (T : ℝ) ≤ t by exact_mod_cast le_of_not_ge h),
        max_eq_right T.coe_nonneg]
    rw [he]
    exact (U.state_adapted T).mono (D.filtration.mono (le_of_not_ge h))

/-- The actual stopped raw state has a square-integrable path radius,
derived from the primitive variation cap and actual Doob inequality. -/
theorem exists_stopped_radius (n : ℕ) : ∃ C : Ω → ℝ, Measurable C ∧ (∀ ω, 0 ≤ C ω) ∧
    MemLp C 2 Q ∧ ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ), ‖U.stoppedState n t ω‖ ≤ C ω := by
  obtain ⟨R,hRm,hR0,hR2,hRB,hRbound⟩ := DoobStrongL2.exists_continuous_radius Q D.filtration
    (L.version n) (L.version_martingale n) (L.version_memLp n)
    (Icc 0 T) ⟨0,le_rfl,zero_le⟩ T (fun _ ht => ht.2)
    ((L.version_continuous n).mono (fun _ hc => hc.continuousOn))
  let C : Ω → ℝ := fun ω => ‖U.state 0 ω‖ + n + R ω
  have hC2 : MemLp C 2 Q := (U.initial_square.norm.add (memLp_const (n : ℝ))).add hR2
  have hCm : Measurable C :=
    ((U.state_strong.of_uncurry_left.measurable.norm).add measurable_const).add hRm
  refine ⟨C,hCm,fun ω => add_nonneg
    (add_nonneg (norm_nonneg _) (Nat.cast_nonneg n)) (hR0 ω),hC2,?_⟩
  filter_upwards [U.stopped_equation n,hRbound] with ω heq hR
  intro t ht
  rw [heq t ht]
  have hprim := (BoundedVariationRealization.primitive_norm_le T _ (U.stoppedDrift_paths n ω).1 t ht).trans
    (U.stoppedDrift_paths n ω).2
  have hMt : ‖L.version n t.toNNReal ω‖ ≤ R ω := hR _ ⟨bot_le,by
    rw [← NNReal.coe_le_coe,Real.coe_toNNReal _ ht.1]; exact ht.2⟩
  dsimp only [C]
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl hprim)) hMt)

def radius (n : ℕ) : Ω → ℝ := Classical.choose (U.exists_stopped_radius n)

theorem radius_measurable (n : ℕ) : Measurable (U.radius n) := (Classical.choose_spec (U.exists_stopped_radius n)).1

theorem radius_nonneg (n : ℕ) (ω : Ω) : 0 ≤ U.radius n ω := (Classical.choose_spec (U.exists_stopped_radius n)).2.1 ω

theorem radius_square (n : ℕ) : MemLp (U.radius n) 2 Q := (Classical.choose_spec (U.exists_stopped_radius n)).2.2.1

theorem radius_bound (n : ℕ) : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ), ‖U.stoppedState n t ω‖ ≤ U.radius n ω :=
  (Classical.choose_spec (U.exists_stopped_radius n)).2.2.2

def dampedState (n : ℕ) (ρ r : ℝ) (ω : Ω) :=
  DampedContinuation.extension ρ (L.stop n ω) (fun r => U.clampedState r ω) r

def dampedDrift (n : ℕ) (ρ r : ℝ) (ω : Ω) :=
  DampedContinuation.drift ρ (L.stop n ω) (fun r => U.clampedState r ω) (fun r => U.drift r ω) r

def variationBudget (n : ℕ) (ρ : ℝ) (ω : Ω) : ℝ := n + ρ * T * U.radius n ω

theorem variationBudget_square (n : ℕ) (ρ : ℝ) : MemLp (U.variationBudget n ρ) 2 Q :=
  (memLp_const (n : ℝ)).add ((U.radius_square n).const_mul (ρ * T))

theorem dampedState_strong (n : ℕ) (ρ : ℝ) : StronglyMeasurable (Function.uncurry (U.dampedState n ρ)) := by
  have hτ : Measurable (fun p : ℝ × Ω => (L.stop n p.2 : ℝ)) :=
    (measurable_coe_nnreal_real.comp (L.stop_measurable n)).comp measurable_snd
  have hmin := measurable_fst.min hτ
  have hx := U.clampedState_strong.comp_measurable (hmin.prodMk measurable_snd)
  have he := ((measurable_fst.sub hmin).const_mul (-ρ)).exp
  exact he.stronglyMeasurable.smul hx

theorem dampedDrift_strong (n : ℕ) (ρ : ℝ) : StronglyMeasurable (Function.uncurry (U.dampedDrift n ρ)) := by
  have hτ : Measurable (fun p : ℝ × Ω => (L.stop n p.2 : ℝ)) :=
    (measurable_coe_nnreal_real.comp (L.stop_measurable n)).comp measurable_snd
  exact U.drift_strong.piecewise (measurableSet_le measurable_fst hτ)
    ((U.dampedState_strong n ρ).const_smul (-ρ))

theorem dampedState_zero (n : ℕ) (ρ : ℝ) (ω : Ω) : U.dampedState n ρ 0 ω = U.state 0 ω := by
  rw [dampedState,DampedContinuation.extension_before ρ _ _ (L.stop n ω).coe_nonneg,
    clampedState,timeClamp_eq T ⟨le_rfl,T.coe_nonneg⟩]

theorem dampedState_continuous (n : ℕ) (ρ : ℝ) :
    ∀ᵐ ω ∂Q, Continuous (fun r => U.dampedState n ρ r ω) := by
  filter_upwards [U.clampedState_continuous] with ω hc
  unfold dampedState DampedContinuation.extension DampedContinuation.damping
  exact (Real.continuous_exp.comp (continuous_const.mul
    (continuous_id.sub (continuous_id.min continuous_const)))).smul
      (hc.comp (continuous_id.min continuous_const))

theorem dampedState_norm_bound (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∀ᵐ ω ∂Q, ∀ r : ℝ, ‖U.dampedState n ρ r ω‖ ≤ U.radius n ω := by
  filter_upwards [U.radius_bound n] with ω hc
  intro r
  apply (DampedContinuation.extension_norm_le hρ (L.stop n ω) (fun s => U.clampedState s ω) r).trans
  have hτ : (L.stop n ω : ℝ) ∈ Icc 0 (T : ℝ) :=
    ⟨(L.stop n ω).coe_nonneg, by exact_mod_cast L.stop_bound n ω⟩
  change ‖U.state (timeClamp T (min r (L.stop n ω : ℝ))) ω‖ ≤ _
  rw [timeClamp_min T _ r hτ]
  exact hc (timeClamp T r) (timeClamp_mem T r)

theorem dampedState_square (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (r : ℝ) :
    MemLp (U.dampedState n ρ r) 2 Q :=
  (U.radius_square n).mono' (U.dampedState_strong n ρ).of_uncurry_left.aestronglyMeasurable
    ((U.dampedState_norm_bound n hρ).mono (fun ω hc => hc r))

/-- The damped equation is derived simultaneously at every time from the
original strong equation and the proved actual local-integral stopping. -/
theorem damped_equation (n : ℕ) (ρ : ℝ) : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ),
    U.dampedState n ρ t ω = U.state 0 ω +
      (∫ r in 0..t, U.dampedDrift n ρ r ω) + L.version n t.toNNReal ω := by
  filter_upwards [U.stopped_equation n] with ω he
  intro t ht
  have hib : IntervalIntegrable (fun r => U.stoppedDrift n r ω) volume 0 t :=
    (U.stoppedDrift_paths n ω).1.mono_set' (by
      rw [uIoc_of_le ht.1,uIoc_of_le T.coe_nonneg]
      exact Ioc_subset_Ioc_right ht.2)
  have he' : U.clampedState (min t (L.stop n ω : ℝ)) ω = U.clampedState 0 ω +
      (∫ r in 0..t, U.stoppedDrift n r ω) + L.version n t.toNNReal ω := by
    rw [clampedState,timeClamp_eq T ⟨le_min ht.1 (L.stop n ω).coe_nonneg,(min_le_left _ _).trans ht.2⟩,
      clampedState,timeClamp_eq T ⟨le_rfl,T.coe_nonneg⟩]
    exact he t ht
  have hd := DampedContinuation.extension_integral_equation ρ (L.stop n ω) t
    (L.stop n ω).coe_nonneg ht.1 (fun r => U.clampedState r ω)
    (fun r => U.drift r ω) (fun r => L.version n r.toNNReal ω) hib he'
  have hz : U.clampedState 0 ω = U.state 0 ω := by
    rw [clampedState,timeClamp_eq T ⟨le_rfl,T.coe_nonneg⟩]
  rw [hz] at hd
  exact hd

theorem dampedDrift_paths (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) : ∀ᵐ ω ∂Q,
    IntervalIntegrable (fun r => U.dampedDrift n ρ r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖U.dampedDrift n ρ r ω‖) ≤ U.variationBudget n ρ ω := by
  filter_upwards [U.radius_bound n] with ω hc
  refine ⟨DampedContinuation.drift_integrable ρ (L.stop n ω) _ _ 0 T
    (U.stoppedDrift_paths n ω).1, ?_⟩
  apply DampedContinuation.drift_variation_le hρ (L.stop n ω) T n (U.radius n ω) T.coe_nonneg
    (fun r => U.clampedState r ω) (fun r => U.drift r ω)
    (U.stoppedDrift_paths n ω).1 (U.stoppedDrift_paths n ω).2
  intro r hr
  rw [clampedState,timeClamp_eq T
    ⟨le_min hr.1 (L.stop n ω).coe_nonneg,(min_le_left _ _).trans hr.2⟩]
  exact hc r hr

theorem minStop_measurable (n : ℕ) (t : ℝ≥0) :
    Measurable[D.filtration t] (fun ω => min t (L.stop n ω)) := by
  apply measurable_of_Iic
  intro r
  change MeasurableSet[D.filtration t] {ω | min t (L.stop n ω) ≤ r}
  by_cases hr : t ≤ r
  · have he : {ω | min t (L.stop n ω) ≤ r} = univ :=
      Set.eq_univ_of_forall (fun ω => (min_le_left _ _).trans hr)
    rw [he]
    exact MeasurableSet.univ
  · have he : {ω | min t (L.stop n ω) ≤ r} = {ω | L.stop n ω ≤ r} := by
      ext ω
      simp only [mem_setOf_eq,min_le_iff,hr,false_or]
    rw [he]
    exact D.filtration.mono (le_of_not_ge hr) _ (L.stop_stopping n r)

theorem dampedState_adapted (n : ℕ) (ρ : ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[D.filtration t] (U.dampedState n ρ t) Q := by
  have hx := stopped_raw_aestronglyAdapted Q D (L.stop n) (L.stop_stopping n)
    (fun t : ℝ≥0 => U.clampedState t) U.clampedState_adapted
    (U.clampedState_continuous.mono (fun _ hc => hc.comp continuous_subtype_val)) t
  have hc : Measurable[D.filtration t] (fun ω => Real.exp (-ρ * ((t : ℝ) - (min t (L.stop n ω) : ℝ)))) :=
    (((measurable_coe_nnreal_real.comp (minStop_measurable (L := L) n t)).const_sub (t : ℝ)).const_mul (-ρ)).exp
  have he : U.dampedState n ρ t = fun ω =>
      Real.exp (-ρ * ((t : ℝ) - (min t (L.stop n ω) : ℝ))) • U.clampedState (min t (L.stop n ω)) ω := by
    funext ω
    simp only [dampedState,DampedContinuation.extension,DampedContinuation.damping,NNReal.coe_min]
  rw [he]
  exact hc.aestronglyMeasurable.smul hx

/-- Exact integral energy family of the genuine damped localization. Every
coefficient curve, martingale, energy identity and random variation budget
is derived from the original raw strong equation. -/
theorem energy_integral (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z,W w⟫_ℝ = ⟪W z,w⟫_ℝ) :
    let e := fun r => ∫ ω, ⟪U.dampedState n ρ r ω,W (U.dampedState n ρ r ω)⟫_ℝ ∂Q
    let w := fun r => 2 * (∫ ω, ⟪U.dampedState n ρ r ω,W (U.dampedDrift n ρ r ω)⟫_ℝ ∂Q) +
      ∫ ω, ∑ i, ⟪L.stoppedSigma n i r ω,W (L.stoppedSigma n i r ω)⟫_ℝ ∂Q
    IntervalIntegrable w volume 0 (T : ℝ) ∧
      ∀ S : ℝ≥0, S ≤ T → e S = e 0 + ∫ r in 0..(S : ℝ), w r := by
  refine ConstructedRandomVariationIntegral.energy_integral Q D W hW T
    (L.stoppedSigma n) (L.stoppedSigma_strong n) (L.stoppedSigma_square n) (L.stoppedSigma_adapted n)
    (U.dampedState n ρ) (U.dampedDrift n ρ) (fun r ω => L.version n r.toNNReal ω)
    (U.dampedState_square n hρ) (U.dampedState_strong n ρ) ?_ ?_ ?_
    (U.dampedDrift_strong n ρ) (U.variationBudget n ρ) (U.variationBudget_square n ρ)
    ((U.dampedState_continuous n ρ).mono (fun _ hc => hc.continuousOn)) ?_
  · intro t ht
    have hh := U.dampedState_adapted n ρ t.toNNReal
    simpa only [Real.coe_toNNReal _ ht.1] using hh
  · intro t
    exact (L.version_martingale n).stronglyAdapted t.toNNReal
  · intro t
    exact L.version_ae n t.toNNReal
  · filter_upwards [U.dampedDrift_paths n hρ,U.damped_equation n ρ] with ω hp he
    refine ⟨hp.1,hp.2,?_⟩
    intro t ht
    rw [U.dampedState_zero n ρ ω]
    exact he t ht

/-- The actual damped localizations eventually agree exactly with the
original state at every fixed time, on every sample path. -/
theorem dampedState_eventually_original (ρ : ℝ) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, U.dampedState n ρ t ω = U.state t ω := by
  filter_upwards [L.stop_eventually_horizon ω] with n hn
  rw [dampedState,hn,DampedContinuation.extension_before ρ T _ ht.2,
    clampedState,timeClamp_eq T ht]

/-- Absolute joint integrability of the raw damped drift work is derived
from its actual variation budget and computed martingale. -/
theorem work_product_integrable (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) (W : Z →L[ℝ] Z) :
    Integrable (fun p : ℝ × Ω => ⟪U.dampedState n ρ p.1 p.2,W (U.dampedDrift n ρ p.1 p.2)⟫_ℝ)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  refine ConstructedRandomVariationWork.work_product_integrable Q D W T
    (L.stoppedSigma n) (L.stoppedSigma_strong n) (L.stoppedSigma_square n) (L.stoppedSigma_adapted n)
    (U.dampedState n ρ) (U.dampedDrift n ρ) (fun r ω => L.version n r.toNNReal ω)
    (U.dampedState_square n hρ) (U.dampedState_strong n ρ) ?_ ?_ ?_
    (U.dampedDrift_strong n ρ) (U.variationBudget n ρ) (U.variationBudget_square n ρ)
    ((U.dampedState_continuous n ρ).mono (fun _ hc => hc.continuousOn)) ?_
  · intro t ht
    have hh := U.dampedState_adapted n ρ t.toNNReal
    simpa only [Real.coe_toNNReal _ ht.1] using hh
  · intro t
    exact (L.version_martingale n).stronglyAdapted t.toNNReal
  · intro t
    exact L.version_ae n t.toNNReal
  · filter_upwards [U.dampedDrift_paths n hρ,U.damped_equation n ρ] with ω hp he
    refine ⟨hp.1,hp.2,?_⟩
    intro t ht
    rw [U.dampedState_zero n ρ ω]
    exact he t ht

end Data
end PBGSO.RawDampedState
