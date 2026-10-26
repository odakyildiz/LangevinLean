import PBGSO.RawDampedState
import PBGSO.RawLocalSolutionTransport
import PBGSO.RawLocalGauge
import PBGSO.DriverNullAugmentation

/-! # Natural raw drift equations acquire a genuine localization gauge
An a.s. pathwise L¹ drift and progressive norm give an everywhere-defined
local energy after the proved initial-null augmentation. No expected drift
moment, quadratic-energy identity, or stochastic-output match is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawDriftGauge
open FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {T : ℝ≥0}

/-- A natural original raw equation produces the controlled localization
data. Only an a.s. ordinary drift integral is required, with no spatial L²
drift or expected variation assumption. The returned raw state is literal. -/
theorem exists_data (L : RawLocalDiffusion (Z := Z) Q D T)
    (x b : ℝ → Ω → Z)
    (hx : StronglyMeasurable (Function.uncurry x))
    (hb : StronglyMeasurable (Function.uncurry b))
    (h0 : MemLp (x 0) 2 Q)
    (hA : ∀ t : ℝ≥0, AEStronglyMeasurable[D.filtration t] (x t) Q)
    (hC : ∀ᵐ ω ∂Q, ContinuousOn (fun r => x r ω) (Icc 0 (T : ℝ)))
    (hbi : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ))
    (hbp : ∀ t : ℝ≥0,
      StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod
        ((nullAugmentedDriver Q D).filtration t)]
        (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => ‖b r p.2‖) p.1))
    (heq : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ),
      x t ω = x 0 ω+(∫ r in 0..t, b r ω)+L.localNoise t.toNNReal ω) :
    ∃ K : RawLocalDiffusion (Z := Z) Q (nullAugmentedDriver Q D) T,
      ∃ U : RawDampedState.Data K,
        U.state = x ∧ (∀ᵐ ω ∂Q, ∀ r, U.drift r ω = b r ω) ∧
        (∀ᵐ ω ∂Q, ∀ i r, K.sigma i r ω = L.sigma i r ω) ∧
        (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → K.localNoise t ω = L.localNoise t ω) := by
  classical
  let E := nullAugmentedDriver Q D
  have hF (t : ℝ≥0) : (pullbackDriver (MeasurePreserving.id Q) D).filtration t ≤ E.filtration t := by
    change (D.filtration t).comap id ≤ E.filtration t
    simpa only [MeasurableSpace.comap_id,E,nullAugmentedDriver] using filtration_le_nullAugmented Q D.filtration t
  let P := L.pullback (MeasurePreserving.id Q) E hF
  have hn : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → P.localNoise t ω = L.localNoise t ω :=
    L.pullback_localNoise_on_horizon (MeasurePreserving.id Q) E hF (fun _ _ => ae_eq_refl _)
  let Good (ω : Ω) := IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ)
  obtain ⟨B,hbad,hBm,hB0⟩ := exists_measurable_superset_of_null (ae_iff.mp hbi)
  let b' : ℝ → Ω → Z := fun r ω => if ω ∈ B then 0 else b r ω
  have hb' : StronglyMeasurable (Function.uncurry b') :=
    stronglyMeasurable_const.piecewise (hBm.preimage measurable_snd) hb
  have hbAE : ∀ᵐ ω ∂Q, ∀ r, b' r ω = b r ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hB0] with ω hω r
    exact ite_eq_right hω
  have hbi' (ω : Ω) : IntegrableOn (fun r => ‖b' r ω‖) (Ioc 0 (T : ℝ)) := by
    by_cases hω : ω ∈ B
    · simp only [b',ite_eq_left hω,norm_zero]
      exact integrableOn_zero
    · have hg : Good ω := by
        by_contra hn
        exact hω (hbad hn)
      simpa only [b',ite_eq_right hω,IntegrableOn] using
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp hg).norm
  have hbp' (t : ℝ≥0) :
      StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (E.filtration t)]
        (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => ‖b' r p.2‖) p.1) := by
    have hm : MeasurableSet[(inferInstance : MeasurableSpace ℝ).prod (E.filtration t)]
        {p : ℝ × Ω | p.2 ∈ B} :=
      (measurableSet_nullAugmentation Q (D.filtration t) B hBm hB0).preimage measurable_snd
    have hz : StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (E.filtration t)]
        (fun _ : ℝ × Ω => (0 : ℝ)) := stronglyMeasurable_const
    convert hz.piecewise hm (hbp t) using 1
    funext p
    by_cases hω : p.2 ∈ B <;> by_cases hr : p.1 ∈ Ioc 0 (t : ℝ) <;>
      simp [b',hω,hr]
    all_goals exact Classical.decPred _
  let K : RawLocalDiffusion (Z := Z) Q E T := {
    sigma := P.sigma
    sigma_strong := P.sigma_strong
    sigma_adapted := P.sigma_adapted
    q r ω := P.q r ω+‖b' r ω‖
    q_strong := P.q_strong.add hb'.norm
    q_nonneg r ω := add_nonneg (P.q_nonneg r ω) (norm_nonneg _)
    q_local ω := (P.q_local ω).add (hbi' ω)
    q_progressive t := by
      convert (P.q_progressive t).add (hbp' t) using 1
      funext p
      by_cases hp : p.1 ∈ Ioc 0 (t : ℝ) <;> simp [hp]
    sigma_control r ω := (P.sigma_control r ω).trans (le_add_of_nonneg_right (norm_nonneg _)) }
  have hk : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → K.localNoise t ω = L.localNoise t ω := by
    filter_upwards [K.localNoise_gauge_congr_of_eq P (fun _ _ _ => rfl),hn] with ω hk hn t ht
    exact (hk t ht).trans (hn t ht)
  let U : RawDampedState.Data K := {
    state := x
    drift := b'
    state_strong := hx
    drift_strong := hb'
    drift_control r ω := le_add_of_nonneg_left (P.q_nonneg r ω)
    initial_square := h0
    state_adapted t := (hA t).mono (filtration_le_nullAugmented Q D.filtration t)
    state_continuous := hC
    equation := by
      filter_upwards [heq,hbAE,hk] with ω he hb hk t ht
      rw [hk t.toNNReal ((Real.toNNReal_le_iff_le_coe).mpr ht.2)]
      convert he t ht using 2
      congr 1
      apply intervalIntegral.integral_congr
      intro r _
      exact hb r }
  exact ⟨K,U,rfl,hbAE,Eventually.of_forall (fun _ _ _ => rfl),hk⟩

end PBGSO.RawDriftGauge
