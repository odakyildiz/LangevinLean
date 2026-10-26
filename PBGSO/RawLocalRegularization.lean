import PBGSO.RawLocalIntegral
import PBGSO.DriverNullAugmentation

/-! # Actual local diffusion data from almost-sure path integrability
One proved initial-null augmentation and one common raw coefficient mask
supply the everywhere-defined localization data. No global moment, stopped
integral, stopping time, approximation, or stochastic energy premise enters.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators Classical
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Primitive raw progressively measurable locally-square diffusion fields
produce actual data for the constructed local integral on the proved
null-augmented Brownian driver. All columns and the controlling raw path
energy keep their original meaning on one common event of probability one. -/
theorem RawLocalDiffusion.exists_of_ae (T : ℝ≥0)
    (σ : I → ℝ → Ω → Z)
    (hσ : ∀ i, StronglyMeasurable (Function.uncurry (σ i)))
    (hA : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (σ i t) Q)
    (q : ℝ → Ω → ℝ) (hq : StronglyMeasurable (Function.uncurry q))
    (hpos : ∀ r ω, 0 ≤ q r ω)
    (hlocal : ∀ᵐ ω ∂Q, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ)))
    (hpast : ∀ t : ℝ≥0,
      StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (D.filtration t)]
        (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => q r p.2) p.1))
    (hcontrol : ∀ r ω, ∑ i, ‖σ i r ω‖ ^ 2 ≤ q r ω) :
    ∃ L : RawLocalDiffusion (Z := Z) Q (nullAugmentedDriver Q D) T,
      ∃ B : Set Ω, MeasurableSet B ∧ Q B = 0 ∧
        (∀ i r ω, L.sigma i r ω = if ω ∈ B then 0 else σ i r ω) ∧
        (∀ r ω, L.q r ω = if ω ∈ B then 0 else q r ω) ∧
        (∀ᵐ ω ∂Q, (∀ i r, L.sigma i r ω = σ i r ω) ∧ ∀ r, L.q r ω = q r ω) := by
  classical
  let P : Ω → Prop := fun ω => IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ))
  have hP : ∀ᵐ ω ∂Q, P ω := hlocal
  have hP0 : Q {ω | ¬ P ω} = 0 := ae_iff.mp hP
  obtain ⟨B,hbad,hBm,hB0⟩ := exists_measurable_superset_of_null hP0
  let σ' : I → ℝ → Ω → Z := fun i r ω => if ω ∈ B then 0 else σ i r ω
  let q' : ℝ → Ω → ℝ := fun r ω => if ω ∈ B then 0 else q r ω
  have hBprod : MeasurableSet {p : ℝ × Ω | p.2 ∈ B} := hBm.preimage measurable_snd
  have hσs (i : I) : StronglyMeasurable (Function.uncurry (σ' i)) :=
    (stronglyMeasurable_const : StronglyMeasurable (fun _ : ℝ × Ω => (0 : Z))).piecewise hBprod (hσ i)
  have hσA (t : ℝ≥0) (i : I) :
      AEStronglyMeasurable[(nullAugmentedDriver Q D).filtration t] (σ' i t) Q := by
    have hAE := (hA t i).mono (filtration_le_nullAugmented Q D.filtration t)
    have hb := measurableSet_nullAugmentation Q (D.filtration t) B hBm hB0
    refine ⟨fun ω => if ω ∈ B then 0 else hAE.mk (σ i t) ω,
      stronglyMeasurable_const.piecewise hb hAE.stronglyMeasurable_mk, ?_⟩
    filter_upwards [hAE.ae_eq_mk] with ω hω
    by_cases hB : ω ∈ B <;> simp [σ',hB,hω]
  have hqs : StronglyMeasurable (Function.uncurry q') :=
    (stronglyMeasurable_const : StronglyMeasurable (fun _ : ℝ × Ω => (0 : ℝ))).piecewise hBprod hq
  have hqA (t : ℝ≥0) :
      StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod ((nullAugmentedDriver Q D).filtration t)]
        (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => q' r p.2) p.1) := by
    have hprod : (inferInstance : MeasurableSpace ℝ).prod (D.filtration t) ≤
        (inferInstance : MeasurableSpace ℝ).prod ((nullAugmentedDriver Q D).filtration t) :=
      sup_le_sup le_rfl (MeasurableSpace.comap_mono (filtration_le_nullAugmented Q D.filtration t))
    have hp := (hpast t).mono hprod
    have hb : MeasurableSet[(inferInstance : MeasurableSpace ℝ).prod ((nullAugmentedDriver Q D).filtration t)]
        {p : ℝ × Ω | p.2 ∈ B} :=
      (measurableSet_nullAugmentation Q (D.filtration t) B hBm hB0).preimage measurable_snd
    have he : (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => q' r p.2) p.1) =
        fun p : ℝ × Ω => if p.2 ∈ B then 0 else (Ioc 0 (t : ℝ)).indicator (fun r => q r p.2) p.1 := by
      funext p
      by_cases hB : p.2 ∈ B <;> by_cases ht : p.1 ∈ Ioc 0 (t : ℝ) <;> simp [q',hB,ht]
    rw [he]
    exact stronglyMeasurable_const.piecewise hb hp
  have hqlocal (ω : Ω) : IntegrableOn (fun r => q' r ω) (Ioc 0 (T : ℝ)) := by
    by_cases hω : ω ∈ B
    · simpa only [q',ite_eq_left hω] using (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) _)
    · have hp : P ω := by
        by_contra hn
        exact hω (hbad hn)
      simpa only [q',ite_eq_right hω] using hp
  let L : RawLocalDiffusion (Z := Z) Q (nullAugmentedDriver Q D) T :=
    { sigma := σ'
      sigma_strong := hσs
      sigma_adapted := hσA
      q := q'
      q_strong := hqs
      q_nonneg := fun r ω => by by_cases hω : ω ∈ B <;> simp [q',hω,hpos]
      q_local := hqlocal
      q_progressive := hqA
      sigma_control := fun r ω => by
        by_cases hω : ω ∈ B
        · simp [σ',q',hω]
        · simpa only [σ',q',ite_eq_right hω] using hcontrol r ω }
  refine ⟨L,B,hBm,hB0,(fun _ _ _ => rfl),(fun _ _ => rfl),?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hB0] with ω hω
  exact ⟨fun i r => ite_eq_right hω, fun r => ite_eq_right hω⟩

end PBGSO.FilteredBrownian
