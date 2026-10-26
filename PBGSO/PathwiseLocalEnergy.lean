import PBGSO.LocalizedDiffusion
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Continuous adapted path energies from raw local coefficients
The local energy is a literal time integral. Continuity, monotonicity and
current-past measurability are derived; no stopping-time or energy-cap
conclusion is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.PathwiseLocalEnergy
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The actual cumulative path energy, constant after the fixed horizon. -/
def energy (T : ℝ≥0) (q : ℝ → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..(t : ℝ), (Ioc 0 (T : ℝ)).indicator (fun r => q r ω) r

/-- Literal raw integral identification at every time before the horizon. -/
theorem energy_eq_integral (T : ℝ≥0) (q : ℝ → Ω → ℝ) (t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    energy T q t ω = ∫ r in Ioc 0 (t : ℝ), q r ω := by
  rw [energy, intervalIntegral.integral_of_le t.coe_nonneg,
    setIntegral_indicator measurableSet_Ioc]
  have hs : Ioc (0 : ℝ) t ∩ Ioc 0 (T : ℝ) = Ioc 0 (t : ℝ) := by
    exact Set.inter_eq_left.mpr (Ioc_subset_Ioc_right (by exact_mod_cast ht))
  rw [hs]

/-- Mere pathwise time-L¹ integrability supplies all-path continuity. -/
theorem energy_continuous (T : ℝ≥0) (q : ℝ → Ω → ℝ)
    (hlocal : ∀ ω, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ))) (ω : Ω) :
    Continuous (fun t => energy T q t ω) := by
  have hi : Integrable ((Ioc 0 (T : ℝ)).indicator (fun r => q r ω)) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (hlocal ω)
  exact (hi.continuous_primitive 0).comp continuous_subtype_val

/-- Nonnegative raw energy makes the actual cumulative integral monotone. -/
theorem energy_monotone (T : ℝ≥0) (q : ℝ → Ω → ℝ)
    (hlocal : ∀ ω, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ)))
    (hpos : ∀ r ω, 0 ≤ q r ω) (ω : Ω) : Monotone (fun t => energy T q t ω) := by
  intro s t hst
  change (∫ r in (0 : ℝ)..(s : ℝ), (Ioc 0 (T : ℝ)).indicator (fun r => q r ω) r) ≤
    (∫ r in (0 : ℝ)..(t : ℝ), (Ioc 0 (T : ℝ)).indicator (fun r => q r ω) r)
  rw [intervalIntegral.integral_of_le s.coe_nonneg,
    intervalIntegral.integral_of_le t.coe_nonneg]
  apply setIntegral_mono_set
    (((integrable_indicator_iff measurableSet_Ioc).mpr (hlocal ω)).integrableOn)
  · exact Eventually.of_forall (fun r => Set.indicator_nonneg (fun r _ => hpos r ω) r)
  · exact Eventually.of_forall (fun r hr => ⟨hr.1, hr.2.trans (by exact_mod_cast hst)⟩)

/-- Raw progressive measurability on each past time window implies actual
adaptedness of its time integral in that same past algebra. -/
theorem energy_measurable (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (q : ℝ → Ω → ℝ)
    (hpast : ∀ t : ℝ≥0,
      StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (ℱ t)]
        (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => q r p.2) p.1))
    (t : ℝ≥0) : Measurable[ℱ t] (energy T q t) := by
  have hm : StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (ℱ t)]
      (fun p : ℝ × Ω => (Ioc 0 (T : ℝ)).indicator
        (fun r => (Ioc 0 (t : ℝ)).indicator (fun r => q r p.2) r) p.1) := by
    exact (hpast t).piecewise (measurableSet_Ioc.preimage measurable_fst) stronglyMeasurable_const
  have he : energy T q t = fun ω => ∫ r,
      (Ioc 0 (T : ℝ)).indicator
        (fun r => (Ioc 0 (t : ℝ)).indicator (fun r => q r ω) r) r := by
    funext ω
    rw [energy, intervalIntegral.integral_of_le t.coe_nonneg]
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with r
    by_cases ht : r ∈ Ioc 0 (t : ℝ) <;> by_cases hT : r ∈ Ioc 0 (T : ℝ) <;>
      simp [ht,hT]
  rw [he]
  have hm' := @StronglyMeasurable.integral_prod_left ℝ Ω ℝ
    (inferInstance : MeasurableSpace ℝ) (ℱ t) volume _ _ _
    (fun r ω => (Ioc 0 (T : ℝ)).indicator
      (fun r => (Ioc 0 (t : ℝ)).indicator (fun r => q r ω) r) r) hm
  exact hm'.measurable

/-- The first-hit localization prerequisites are conclusions of the raw
pathwise time-integrability and progressive scalar energy. -/
theorem energy_firstHit_properties (ℱ : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (q : ℝ → Ω → ℝ)
    (hlocal : ∀ ω, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ)))
    (hpos : ∀ r ω, 0 ≤ q r ω)
    (hpast : ∀ t : ℝ≥0,
      StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (ℱ t)]
        (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => q r p.2) p.1))
    (c : ℝ) (hc : 0 ≤ c) :
    let τ := PathEnergyStopping.firstHit T (energy T q) c
    (∀ t, MeasurableSet[ℱ t] {ω | τ ω ≤ t}) ∧
    (∀ ω, τ ω ≤ T) ∧
    (∀ ω, (∫ r in Ioc 0 (τ ω : ℝ), q r ω) ≤ c) ∧
    (∀ ω, ∀ᶠ n : ℕ in atTop,
      PathEnergyStopping.firstHit T (energy T q) n ω = T) := by
  have hC := energy_continuous T q hlocal
  have hM := energy_monotone T q hlocal hpos
  refine ⟨PathEnergyStopping.firstHit_stopping ℱ T _ c hC hM (energy_measurable ℱ T q hpast),
    fun ω => PathEnergyStopping.firstHit_le_horizon T _ c ω (hC ω), ?_,
    fun ω => PathEnergyStopping.firstHit_nat_eventually_horizon T _ ω (hM ω)⟩
  intro ω
  rw [← energy_eq_integral T q _
    (PathEnergyStopping.firstHit_le_horizon T _ c ω (hC ω)) ω]
  apply PathEnergyStopping.firstHit_energy_le T _ c ω (hC ω)
  simpa only [energy, NNReal.coe_zero, intervalIntegral.integral_same] using hc

end PBGSO.PathwiseLocalEnergy
