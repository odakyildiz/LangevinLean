import PBGSO.RawLocalGauge
import PBGSO.RawLocalRegularization
import PBGSO.RawLocalPullbackLocal

/-! # Adding raw drift variation to an actual local stochastic gauge
The local Brownian integral is unchanged when the gauge also controls raw
pathwise drift variation. The AE-path version derives a common null-set
normalization on the proved null-augmented Driver; it does not require a
pre-existing drift-control or noise-matching assumption.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {T : ℝ≥0}
  (L : RawLocalDiffusion (Z := Z) Q D T)
  (b : ℝ → Ω → Z) (hb : StronglyMeasurable (Function.uncurry b))
  (hprog : ∀ t : ℝ≥0,
    StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (D.filtration t)]
      (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => b r p.2) p.1))

include hprog in
private theorem augmented_progressive (t : ℝ≥0) :
    StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (D.filtration t)]
      (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => L.q r p.2+‖b r p.2‖) p.1) := by
  have he : (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => L.q r p.2+‖b r p.2‖) p.1) =
      (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => L.q r p.2) p.1)+
        (fun p : ℝ × Ω => ‖(Ioc 0 (t : ℝ)).indicator (fun r => b r p.2) p.1‖) := by
    funext p
    by_cases h : p.1 ∈ Ioc 0 (t : ℝ) <;> simp [h]
  rw [he]
  exact (L.q_progressive t).add (hprog t).norm

/-- The raw diffusion is unchanged; the actual energy is augmented by the
literal drift norm. Only primitive measurability/progressivity and path L¹
are required, and no global expected coefficient moments are imposed. -/
def RawLocalDiffusion.withDriftEnergy
    (hloc : ∀ ω, IntegrableOn (fun r => b r ω) (Ioc 0 (T : ℝ))) :
    RawLocalDiffusion (Z := Z) Q D T where
  sigma := L.sigma
  sigma_strong := L.sigma_strong
  sigma_adapted := L.sigma_adapted
  q r ω := L.q r ω+‖b r ω‖
  q_strong := L.q_strong.add hb.norm
  q_nonneg r ω := add_nonneg (L.q_nonneg r ω) (norm_nonneg _)
  q_local ω := (L.q_local ω).add (hloc ω).norm
  q_progressive := augmented_progressive L b hprog
  sigma_control r ω := (L.sigma_control r ω).trans (le_add_of_nonneg_right (norm_nonneg _))

/-- Actual drift domination is a conclusion of the new gauge definition. -/
theorem RawLocalDiffusion.withDriftEnergy_control
    (hloc : ∀ ω, IntegrableOn (fun r => b r ω) (Ioc 0 (T : ℝ))) (r : ℝ) (ω : Ω) :
    ‖b r ω‖ ≤ (L.withDriftEnergy b hb hprog hloc).q r ω :=
  le_add_of_nonneg_left (L.q_nonneg r ω)

/-- The actual local Brownian integral is preserved simultaneously over the
horizon after adding drift variation to the stopping gauge. -/
theorem RawLocalDiffusion.withDriftEnergy_noise
    (hloc : ∀ ω, IntegrableOn (fun r => b r ω) (Ioc 0 (T : ℝ))) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T →
      (L.withDriftEnergy b hb hprog hloc).localNoise t ω = L.localNoise t ω :=
  (L.withDriftEnergy b hb hprog hloc).localNoise_gauge_congr_of_eq L (fun _ _ _ => rfl)

include hb hprog in
/-- Almost-sure pathwise drift integrability is sufficient after the proved
initial null augmentation. The output drift-control and actual local-noise
matching are derived, not supplied as realization assumptions. -/
theorem RawLocalDiffusion.exists_withDriftEnergy_of_ae
    (hloc : ∀ᵐ ω ∂Q, IntegrableOn (fun r => b r ω) (Ioc 0 (T : ℝ))) :
    ∃ K : RawLocalDiffusion (Z := Z) Q (nullAugmentedDriver Q D) T,
      ∃ b' : ℝ → Ω → Z,
        StronglyMeasurable (Function.uncurry b') ∧
        (∀ r ω, ‖b' r ω‖ ≤ K.q r ω) ∧
        (∀ᵐ ω ∂Q, ∀ r, b' r ω = b r ω) ∧
        (∀ᵐ ω ∂Q, ∀ i r, K.sigma i r ω = L.sigma i r ω) ∧
        (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → K.localNoise t ω = L.localNoise t ω) := by
  classical
  let q : ℝ → Ω → ℝ := fun r ω => L.q r ω+‖b r ω‖
  have hq : StronglyMeasurable (Function.uncurry q) := L.q_strong.add hb.norm
  have hpos : ∀ r ω, 0 ≤ q r ω := fun r ω => add_nonneg (L.q_nonneg r ω) (norm_nonneg _)
  have hl : ∀ᵐ ω ∂Q, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ)) :=
    hloc.mono (fun ω h => (L.q_local ω).add h.norm)
  have hcontrol : ∀ r ω, ∑ i, ‖L.sigma i r ω‖ ^ 2 ≤ q r ω :=
    fun r ω => (L.sigma_control r ω).trans (le_add_of_nonneg_right (norm_nonneg _))
  obtain ⟨K,B,hBm,hB0,hKσ,hKq,hreal⟩ := RawLocalDiffusion.exists_of_ae Q D T L.sigma
    L.sigma_strong L.sigma_adapted q hq hpos hl (augmented_progressive L b hprog) hcontrol
  let b' : ℝ → Ω → Z := fun r ω => if ω ∈ B then 0 else b r ω
  have hb' : StronglyMeasurable (Function.uncurry b') :=
    stronglyMeasurable_const.piecewise (hBm.preimage measurable_snd) hb
  have hdom : ∀ r ω, ‖b' r ω‖ ≤ K.q r ω := by
    intro r ω
    rw [hKq r ω]
    by_cases h : ω ∈ B
    · simp [b',h]
    · simpa only [b',ite_eq_right h,q] using (le_add_of_nonneg_left (L.q_nonneg r ω) : ‖b r ω‖ ≤ L.q r ω+‖b r ω‖)
  have hbAE : ∀ᵐ ω ∂Q, ∀ r, b' r ω = b r ω := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hB0] with ω hω
    intro r
    exact ite_eq_right hω
  let hf := MeasurePreserving.id Q
  let E := nullAugmentedDriver Q D
  have he : ∀ t, (pullbackDriver hf D).filtration t ≤ E.filtration t := by
    intro t
    simpa only [pullbackDriver,pullbackFiltration,MeasurableSpace.comap_id,E,nullAugmentedDriver] using
      (filtration_le_nullAugmented Q D.filtration t)
  let L0 := L.pullback hf E he
  have hp : ∀ i t, (pullbackDriver hf D).process i t =ᵐ[Q] E.process i t :=
    fun _ _ => Eventually.of_forall (fun _ => rfl)
  have hnoise0 := L.pullback_localNoise_on_horizon hf E he hp
  have hσAE : ∀ᵐ ω ∂Q, ∀ i r, r ∈ Ioc 0 (T : ℝ) → K.sigma i r ω = L0.sigma i r ω :=
    hreal.mono (fun ω h i r _ => h.1 i r)
  have hnoiseK := K.localNoise_gauge_congr_on_horizon L0 hσAE
  refine ⟨K,b',hb',hdom,hbAE,hreal.mono (fun _ h => h.1),?_⟩
  filter_upwards [hnoiseK,hnoise0] with ω hk h0
  intro t ht
  exact (hk t ht).trans (h0 t ht)

end PBGSO.FilteredBrownian
