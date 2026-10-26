import PBGSO.RawIntegralStopping
import PBGSO.PathwiseLocalEnergy
import Mathlib.MeasureTheory.Function.FactorsThrough

/-! # Actual local stochastic integrals from pathwise local square coefficients
Every localized integral is a computed Brownian completion. Their consistency
is proved by actual coefficient stopping, then a single local noise process
is glued without a stopped-equation or output-equality premise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- Primitive raw locally square-integrable diffusion data. The scalar path
energy may also include raw drift variation. No global expected coefficient
energy, stopped integral, local-noise process, martingale, or isometry enters. -/
structure RawLocalDiffusion (T : ℝ≥0) where
  sigma : I → ℝ → Ω → Z
  sigma_strong : ∀ i, StronglyMeasurable (Function.uncurry (sigma i))
  sigma_adapted : ∀ t : ℝ≥0, ∀ i, AEStronglyMeasurable[D.filtration t] (sigma i t) Q
  q : ℝ → Ω → ℝ
  q_strong : StronglyMeasurable (Function.uncurry q)
  q_nonneg : ∀ r ω, 0 ≤ q r ω
  q_local : ∀ ω, IntegrableOn (fun r => q r ω) (Ioc 0 (T : ℝ))
  q_progressive : ∀ t : ℝ≥0,
    StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (D.filtration t)]
      (fun p : ℝ × Ω => (Ioc 0 (t : ℝ)).indicator (fun r => q r p.2) p.1)
  sigma_control : ∀ r ω, ∑ i, ‖sigma i r ω‖ ^ 2 ≤ q r ω

namespace RawLocalDiffusion
variable {Q D} {T : ℝ≥0} (L : RawLocalDiffusion (Z := Z) Q D T)

def pathEnergy := PathwiseLocalEnergy.energy T L.q

def stop (n : ℕ) : Ω → ℝ≥0 := PathEnergyStopping.firstHit T L.pathEnergy n

theorem pathEnergy_continuous (ω : Ω) : Continuous (fun t => L.pathEnergy t ω) :=
  PathwiseLocalEnergy.energy_continuous T L.q L.q_local ω

theorem pathEnergy_monotone (ω : Ω) : Monotone (fun t => L.pathEnergy t ω) :=
  PathwiseLocalEnergy.energy_monotone T L.q L.q_local L.q_nonneg ω

theorem pathEnergy_measurable (t : ℝ≥0) : Measurable[D.filtration t] (L.pathEnergy t) :=
  PathwiseLocalEnergy.energy_measurable D.filtration T L.q L.q_progressive t

theorem stop_stopping (n : ℕ) (t : ℝ≥0) : MeasurableSet[D.filtration t] {ω | L.stop n ω ≤ t} :=
  PathEnergyStopping.firstHit_stopping D.filtration T L.pathEnergy n
    L.pathEnergy_continuous L.pathEnergy_monotone L.pathEnergy_measurable t

theorem stop_bound (n : ℕ) (ω : Ω) : L.stop n ω ≤ T :=
  PathEnergyStopping.firstHit_le_horizon T L.pathEnergy n ω (L.pathEnergy_continuous ω)

theorem stop_energy_bound (n : ℕ) (ω : Ω) :
    (∫ r in Ioc 0 (L.stop n ω : ℝ), L.q r ω) ≤ n := by
  rw [← PathwiseLocalEnergy.energy_eq_integral T L.q (L.stop n ω) (L.stop_bound n ω) ω]
  apply PathEnergyStopping.firstHit_energy_le T L.pathEnergy n ω (L.pathEnergy_continuous ω)
  simpa only [pathEnergy, PathwiseLocalEnergy.energy, NNReal.coe_zero,
    intervalIntegral.integral_same] using (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

theorem stop_measurable (n : ℕ) : Measurable (L.stop n) :=
  stoppingTime_measurable Q D (L.stop n) (L.stop_stopping n)

theorem stop_mono {n m : ℕ} (h : n ≤ m) (ω : Ω) : L.stop n ω ≤ L.stop m ω :=
  PathEnergyStopping.firstHit_mono_threshold T L.pathEnergy n m (by exact_mod_cast h)
    ω (L.pathEnergy_continuous ω) (L.pathEnergy_monotone ω)

theorem stop_eventually_horizon (ω : Ω) : ∀ᶠ n : ℕ in atTop, L.stop n ω = T :=
  PathEnergyStopping.firstHit_nat_eventually_horizon T L.pathEnergy ω (L.pathEnergy_monotone ω)

def stoppedSigma (n : ℕ) (i : I) : ℝ → Ω → Z :=
  LocalizedDiffusion.stoppedField (L.stop n) (L.sigma i)

theorem stoppedSigma_strong (n : ℕ) (i : I) : StronglyMeasurable (Function.uncurry (L.stoppedSigma n i)) :=
  LocalizedDiffusion.stoppedField_stronglyMeasurable _ (L.stop_measurable n) _ (L.sigma_strong i)

theorem stoppedSigma_adapted (n : ℕ) (t : ℝ≥0) (i : I) :
    AEStronglyMeasurable[D.filtration t] (L.stoppedSigma n i t) Q :=
  LocalizedDiffusion.stoppedField_adapted D.filtration (L.stop n) (L.stop_stopping n)
    (L.sigma i) Q (fun t => L.sigma_adapted t i) t

theorem stoppedSigma_square (n : ℕ) (i : I) :
    Integrable (fun p : ℝ × Ω => ‖L.stoppedSigma n i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  apply LocalizedDiffusion.firstHit_column_square_integrable Q T L.q L.q_strong
    L.q_nonneg L.q_local L.pathEnergy L.pathEnergy_continuous
    (fun t ht ω => PathwiseLocalEnergy.energy_eq_integral T L.q t ht ω)
    n (Nat.cast_nonneg n) (L.stop_measurable n) (L.sigma i) (L.sigma_strong i)
  intro r ω
  apply le_trans _ (L.sigma_control r ω)
  exact Finset.single_le_sum (fun j _ => sq_nonneg ‖L.sigma j r ω‖) (Finset.mem_univ i)

/-- The literal computed noise of the first-hit restricted raw diffusion. -/
def noise (n : ℕ) : ℝ≥0 → Lp Z 2 Q :=
  rawDiffusionIntegral Q D T (L.stoppedSigma n) (L.stoppedSigma_strong n)
    (L.stoppedSigma_square n) (L.stoppedSigma_adapted n)

theorem exists_version (n : ℕ) :
    ∃ M : ℝ≥0 → Ω → Z, Martingale M D.filtration Q ∧
      (∀ᵐ ω ∂Q, Continuous (fun t => M t ω)) ∧ ∀ t, M t =ᵐ[Q] L.noise n t :=
  rawDiffusionIntegral_exists_continuous_martingale Q D T (L.stoppedSigma n)
    (L.stoppedSigma_strong n) (L.stoppedSigma_square n) (L.stoppedSigma_adapted n)

def version (n : ℕ) : ℝ≥0 → Ω → Z := Classical.choose (L.exists_version n)

theorem version_martingale (n : ℕ) : Martingale (L.version n) D.filtration Q :=
  (Classical.choose_spec (L.exists_version n)).1

theorem version_continuous (n : ℕ) : ∀ᵐ ω ∂Q, Continuous (fun t => L.version n t ω) :=
  (Classical.choose_spec (L.exists_version n)).2.1

theorem version_ae (n : ℕ) (t : ℝ≥0) : L.version n t =ᵐ[Q] L.noise n t :=
  (Classical.choose_spec (L.exists_version n)).2.2 t

theorem version_memLp (n : ℕ) (t : ℝ≥0) : MemLp (L.version n t) 2 Q :=
  (memLp_congr_ae (L.version_ae n t)).mpr (Lp.memLp (L.noise n t))

/-- The terminal expected stochastic energy is bounded by the actual
first-hit threshold, derived from raw square coefficients and isometry. -/
theorem noise_terminal_sq_le (n : ℕ) : ‖L.noise n T‖ ^ 2 ≤ n := by
  have ht := LocalizedDiffusion.firstHit_physical_columns Q D.filtration T L.q L.q_strong
    L.q_nonneg L.q_local L.pathEnergy L.pathEnergy_continuous L.pathEnergy_monotone
    L.pathEnergy_measurable
    (fun t ht ω => PathwiseLocalEnergy.energy_eq_integral T L.q t ht ω)
    n (Nat.cast_nonneg n) L.sigma L.sigma_strong L.sigma_adapted L.sigma_control
  have htot := ht.2.2.2.2
  have hi : Integrable (fun p : ℝ × Ω => ∑ i, ‖L.stoppedSigma n i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) :=
    integrable_finsetSum _ (fun i _ => L.stoppedSigma_square n i)
  change ‖rawDiffusionIntegral Q D T _ _ _ _ T‖ ^ 2 ≤ _
  rw [rawDiffusionIntegral_norm_sq Q D T _ _ _ _ T le_rfl]
  calc
    _ = ∫ p : ℝ × Ω, ∑ i, ‖L.stoppedSigma n i p.1 p.2‖ ^ 2
        ∂((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := (integral_prod _ hi).symm
    _ = ∑ i, ∫ p : ℝ × Ω, ‖L.stoppedSigma n i p.1 p.2‖ ^ 2
        ∂((volume.restrict (Ioc 0 (T : ℝ))).prod Q) :=
      integral_finsetSum _ (fun i _ => L.stoppedSigma_square n i)
    _ = ∫ r in Ioc 0 (T : ℝ),
        ‖ProductLpSections.columnSections Q (L.stoppedSigma n) r‖ ^ 2 :=
      (ProductLpSections.integral_columnSections_norm_sq _ Q _
        (L.stoppedSigma_strong n) (L.stoppedSigma_square n)).symm
    _ ≤ n := htot

theorem version_terminal_sq_le (n : ℕ) : (∫ ω, ‖L.version n T ω‖ ^ 2 ∂Q) ≤ n := by
  calc
    _ = ∫ ω, ‖L.noise n T ω‖ ^ 2 ∂Q :=
      integral_congr_ae ((L.version_ae n T).fun_comp (fun z => ‖z‖ ^ 2))
    _ = ‖L.noise n T‖ ^ 2 := (ProximalLangevin.lp_norm_sq_eq_integral Q (L.noise n T)).symm
    _ ≤ n := L.noise_terminal_sq_le n

/-- Nested coefficient masks give literal random-time consistency of the
computed martingale versions, simultaneously at every observation time. -/
theorem version_consistent {n m : ℕ} (h : n ≤ m) :
    ∀ᵐ ω ∂Q, ∀ t, L.version n t ω = L.version m (min t (L.stop n ω)) ω := by
  apply rawDiffusionIntegral_stopped_version Q D T (L.stop n) (L.stop_bound n)
    (L.stop_stopping n) (L.stoppedSigma m) (L.stoppedSigma n)
    (L.stoppedSigma_strong m) (L.stoppedSigma_square m) (L.stoppedSigma_adapted m)
    (L.stoppedSigma_strong n) (L.stoppedSigma_square n) (L.stoppedSigma_adapted n)
    _ (L.version m) (L.version n) (L.version_ae m) (L.version_ae n)
    (L.version_continuous m) (L.version_continuous n)
  intro i r ω
  unfold stoppedSigma LocalizedDiffusion.stoppedField
  by_cases hn : r ≤ (L.stop n ω : ℝ)
  · have hm : r ≤ (L.stop m ω : ℝ) := hn.trans (by exact_mod_cast L.stop_mono h ω)
    simp [hn,hm]
  · simp [hn]

/-- A finite path energy always reaches some localization threshold only
after the horizon, so some actual first-hit stop equals T on every sample. -/
def horizonIndex (ω : Ω) : ℕ := Nat.find ((L.stop_eventually_horizon ω).exists)

theorem horizonIndex_spec (ω : Ω) : L.stop (L.horizonIndex ω) ω = T :=
  Nat.find_spec ((L.stop_eventually_horizon ω).exists)

/-- The actual local stochastic integral, glued from actual computed
localized martingales. No stopped-output law is used to define it. -/
def localNoise (t : ℝ≥0) (ω : Ω) : Z := L.version (L.horizonIndex ω) t ω

/-- Single common event supporting the entire localized family. -/
theorem all_consistency :
    ∀ᵐ ω ∂Q, ∀ n m : ℕ, n ≤ m → ∀ t,
      L.version n t ω = L.version m (min t (L.stop n ω)) ω := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro m
  by_cases h : n ≤ m
  · exact (L.version_consistent h).mono (fun _ hc _ => hc)
  · exact Eventually.of_forall (fun _ hn => False.elim (h hn))

/-- Genuine random-time stopped realization of the constructed local Ito
process. The stopped equation is a conclusion, not a realization premise. -/
theorem localNoise_stopped : ∀ᵐ ω ∂Q, ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ T →
    L.version n t ω = L.localNoise (min t (L.stop n ω)) ω := by
  filter_upwards [L.all_consistency] with ω hc
  intro n t ht
  let k := max n (L.horizonIndex ω)
  have hn := hc n k (le_max_left _ _) t
  have hN := hc (L.horizonIndex ω) k (le_max_right _ _) (min t (L.stop n ω))
  rw [L.horizonIndex_spec ω, min_eq_left ((min_le_left _ _).trans ht)] at hN
  exact hn.trans hN.symm

theorem localNoise_continuous : ∀ᵐ ω ∂Q, Continuous (fun t => L.localNoise t ω) := by
  filter_upwards [ae_all_iff.mpr (fun n => L.version_continuous n)] with ω hc
  exact hc (L.horizonIndex ω)

theorem version_zero (n : ℕ) : L.version n 0 =ᵐ[Q] (fun _ => (0 : Z)) := by
  have hz : L.noise n 0 = 0 := rawDiffusionIntegral_zero Q D T _ _ _ _
  filter_upwards [L.version_ae n 0, Lp.coeFn_zero (E := Z) (p := 2) (μ := Q)] with ω hm h0
  rw [hz] at hm
  exact hm.trans h0

theorem localNoise_zero : L.localNoise 0 =ᵐ[Q] (fun _ => (0 : Z)) := by
  filter_upwards [ae_all_iff.mpr (fun n => L.version_zero n)] with ω hω
  exact hω (L.horizonIndex ω)

/-- At every fixed time in the horizon, the actual finite-threshold
martingales eventually equal the constructed local noise on each good path. -/
theorem version_eventually_localNoise : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T →
    ∀ᶠ n : ℕ in atTop, L.version n t ω = L.localNoise t ω := by
  filter_upwards [L.localNoise_stopped] with ω hs
  intro t ht
  filter_upwards [L.stop_eventually_horizon ω] with n hn
  simpa only [hn,min_eq_left ht] using hs n t ht

/-- Genuine past AE-adaptation of the glued local process follows from its
actual adapted martingale approximants. No adaptation of the future-dependent
horizon selector is asserted. -/
theorem localNoise_adapted (t : ℝ≥0) (ht : t ≤ T) :
    AEStronglyMeasurable[D.filtration t] (L.localNoise t) Q := by
  have hsm : StronglyMeasurable[D.filtration t]
      (fun ω => limUnder atTop (fun n => L.version n t ω)) :=
    @StronglyMeasurable.limUnder ℕ Ω Z (D.filtration t) _ _ atTop _
      (fun n ω => L.version n t ω) _ _ (fun n => (L.version_martingale n).stronglyAdapted t)
  refine ⟨fun ω => limUnder atTop (fun n => L.version n t ω), hsm, ?_⟩
  filter_upwards [L.version_eventually_localNoise] with ω hω
  have hc : Tendsto (fun n => L.version n t ω) atTop (𝓝 (L.localNoise t ω)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hω t ht] with n hn
    exact hn.symm
  exact hc.limUnder_eq.symm

end RawLocalDiffusion
end PBGSO.FilteredBrownian
