import PBGSO.RawLocalIntegral
import PBGSO.BoundedVariationState
import PBGSO.RawStoppingCoordinates
import PBGSO.LinearGrowthHorizon
import PBGSO.RawDiffusionAlgebra
import PBGSO.MartingaleMaximalL2
import PBGSO.RawToPredictableData

/-! # Raw linear-growth strong equations and derived global moments
The original equation is driven by the actually constructed local Brownian
integral. No globally integrable coefficient curve, stopped-state moment,
noise isometry or expected-energy premise is supplied.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawLinearGrowthState
open FilteredBrownian ProductLpSections RawStoppingCoordinates LinearGrowthMoment
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {T : ℝ≥0}

/-- A natural original raw integral equation in the linear-growth branch.
The local diffusion object contains only raw measurable adapted columns and
pathwise local energy, not global expected coefficient moments. -/
structure Data (L : RawLocalDiffusion (Z := Z) Q D T) (K P : ℝ) where
  state : ℝ → Ω → Z
  drift : ℝ → Ω → Z
  drift_strong : StronglyMeasurable (Function.uncurry drift)
  drift_control : ∀ r ω, ‖drift r ω‖ ≤ L.q r ω
  initial_square : MemLp (state 0) 2 Q
  K_nonneg : 0 ≤ K
  P_nonneg : 0 ≤ P
  growth : ∀ r ∈ Icc 0 (T : ℝ), ∀ᵐ ω ∂Q,
    ‖drift r ω‖ + ‖WithLp.toLp 2 (fun i => L.sigma i r ω)‖ ≤
      K * (1 + P + ‖state r ω‖)
  equation : ∀ᵐ ω ∂Q, ∀ t ∈ Icc 0 (T : ℝ), state t ω = state 0 ω +
    (∫ r in 0..t, drift r ω) + L.localNoise t.toNNReal ω

namespace Data
variable {L : RawLocalDiffusion (Z := Z) Q D T} {K P : ℝ} (U : Data L K P)

def stoppedDrift (n : ℕ) := LocalizedDiffusion.stoppedField (L.stop n) U.drift

def stoppedState (n : ℕ) := RawStoppingCoordinates.stoppedState (L.stop n) U.state

theorem stoppedDrift_strong (n : ℕ) : StronglyMeasurable (Function.uncurry (U.stoppedDrift n)) :=
  LocalizedDiffusion.stoppedField_stronglyMeasurable _ (L.stop_measurable n) U.drift U.drift_strong

/-- The original local path-energy cap bounds actual stopped drift variation. -/
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

/-- Stopping the actual original equation derives its true raw stopped form. -/
theorem stopped_equation (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    U.stoppedState n t =ᵐ[Q] fun ω => U.state 0 ω +
      (∫ r in 0..t, U.stoppedDrift n r ω) + L.version n t.toNNReal ω := by
  filter_upwards [U.equation, L.localNoise_stopped] with ω heq hn
  have hmin : (min t (L.stop n ω : ℝ)).toNNReal = min t.toNNReal (L.stop n ω) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_min, Real.coe_toNNReal _ (le_min ht.1 (L.stop n ω).coe_nonneg),
      Real.coe_toNNReal _ ht.1]
  change U.state (min t (L.stop n ω : ℝ)) ω = _
  rw [heq _ ⟨le_min ht.1 (L.stop n ω).coe_nonneg, (min_le_left _ _).trans ht.2⟩,
    ← stoppedField_integral (L.stop n) U.drift t ht.1 ω, hmin,
    ← hn n t.toNNReal (by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1]; exact ht.2)]
  rfl

/-- Local stopped states have actual spatial L² values, derived from their
original raw equations and true capped Brownian martingales. -/
theorem stoppedState_memLp (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    MemLp (U.stoppedState n t) 2 Q :=
  BoundedVariationRealization.state_memLp Q T (U.stoppedDrift n) (U.stoppedDrift_strong n) n
    (Eventually.of_forall (U.stoppedDrift_paths n)) (U.state 0) (U.stoppedState n t)
    (L.version n t.toNNReal) U.initial_square (L.version_memLp n t.toNNReal) t ht
    (U.stopped_equation n t ht)

/-- Genuine martingale endpoint moments are bounded by their terminal
moment; the actual stopped diffusion cap then supplies the numerical bound. -/
theorem version_moment_le (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, ‖L.version n t ω‖ ^ 2 ∂Q) ≤ n := by
  have hm := MartingaleMaximalL2.norm_sq_submartingale Q D.filtration
    (L.version n) (L.version_martingale n) (L.version_memLp n)
  have hi := hm.setIntegral_le ht (s := Set.univ) MeasurableSet.univ
  have hle : (∫ ω, ‖L.version n t ω‖ ^ 2 ∂Q) ≤ ∫ ω, ‖L.version n T ω‖ ^ 2 ∂Q := by
    simpa only [setIntegral_univ] using hi
  exact hle.trans (L.version_terminal_sq_le n)

/-- Localized raw state moments follow from the literal capped variation
and actual constructed noise, without any original state-moment premise. -/
theorem stoppedState_moment_le (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ‖(U.stoppedState_memLp n t ht).toLp (U.stoppedState n t)‖ ^ 2 ≤
      3 * ‖U.initial_square.toLp (U.state 0)‖ ^ 2 + 3 * (n : ℝ) ^ 2 + 3 * n := by
  rw [toLp_norm_sq Q _ _, toLp_norm_sq Q _ _]
  have hm := BoundedVariationRealization.state_moment_bound Q T
    (U.stoppedDrift n) (U.stoppedDrift_strong n) n (Nat.cast_nonneg n)
    (Eventually.of_forall (U.stoppedDrift_paths n)) (U.state 0) (U.stoppedState n t)
    (L.version n t.toNNReal) U.initial_square (L.version_memLp n t.toNNReal) t ht
    (U.stopped_equation n t ht)
  have hn := version_moment_le (L := L) n t.toNNReal (by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1]; exact ht.2)
  linarith

/-- All finite physical columns are represented in their literal Euclidean
noise norm; the full primitive growth inequality retains every column. -/
def packedStoppedSigma (U : Data L K P) (n : ℕ) (r : ℝ) (ω : Ω) : PiLp 2 (fun _ : I => Z) :=
  WithLp.toLp 2 (fun i => L.stoppedSigma n i r ω)

theorem packedStoppedSigma_strong (n : ℕ) :
    StronglyMeasurable (Function.uncurry (U.packedStoppedSigma n)) := by
  apply (PiLp.continuous_toLp 2 (fun _ : I => Z)).comp_stronglyMeasurable
  exact (measurable_pi_iff.mpr (fun i => (L.stoppedSigma_strong n i).measurable)).stronglyMeasurable

/-- Primitive raw linear growth applies to the actual stopped state. Both
spatial coefficient moments are conclusions of this theorem. -/
theorem stopped_coefficients (n : ℕ) (r : ℝ) (hr : r ∈ Ioc 0 (T : ℝ)) :
    ∃ hb2 : MemLp (U.stoppedDrift n r) 2 Q,
    ∃ hσ2 : MemLp (U.packedStoppedSigma n r) 2 Q,
      ‖hb2.toLp (U.stoppedDrift n r)‖ ^ 2 + ‖hσ2.toLp (U.packedStoppedSigma n r)‖ ^ 2 ≤
        3 * K ^ 2 * (1 + P ^ 2 +
          ‖(U.stoppedState_memLp n r (Ioc_subset_Icc_self hr)).toLp (U.stoppedState n r)‖ ^ 2) := by
  apply coefficients_of_linear_growth Q (U.stoppedState n r) (U.stoppedDrift n r)
    (U.packedStoppedSigma n r) (U.stoppedState_memLp n r (Ioc_subset_Icc_self hr))
    (U.stoppedDrift_strong n).of_uncurry_left.aestronglyMeasurable
    (U.packedStoppedSigma_strong n).of_uncurry_left.aestronglyMeasurable U.K_nonneg U.P_nonneg
  filter_upwards [U.growth r (Ioc_subset_Icc_self hr)] with ω hg
  by_cases hω : r ≤ (L.stop n ω : ℝ)
  · have hb : U.stoppedDrift n r ω = U.drift r ω := by
      simp only [stoppedDrift, LocalizedDiffusion.stoppedField, ite_eq_left hω]
    have hσ : U.packedStoppedSigma n r ω = WithLp.toLp 2 (fun i => L.sigma i r ω) := by
      unfold packedStoppedSigma
      congr 1
      funext i
      simp only [RawLocalDiffusion.stoppedSigma, LocalizedDiffusion.stoppedField, ite_eq_left hω]
    rw [hb, hσ]
    simpa only [stoppedState, RawStoppingCoordinates.stoppedState, min_eq_left hω] using hg
  · have hb : U.stoppedDrift n r ω = 0 := by
      simp only [stoppedDrift, LocalizedDiffusion.stoppedField, ite_eq_right hω]
    have hσ : U.packedStoppedSigma n r ω = 0 := by
      apply (WithLp.equiv 2 (I → Z)).injective
      funext i
      change L.stoppedSigma n i r ω = 0
      simp only [RawLocalDiffusion.stoppedSigma, LocalizedDiffusion.stoppedField, ite_eq_right hω]
    simp only [hb, hσ, norm_zero, add_zero]
    exact mul_nonneg U.K_nonneg (by linarith [U.P_nonneg, norm_nonneg (U.stoppedState n r ω)])


/-- The local state bound derives genuine stopped drift product L², even
though the original raw drift was assumed only pathwise L¹. -/
theorem stoppedDrift_product_square (n : ℕ) :
    Integrable (fun p : ℝ × Ω => ‖U.stoppedDrift n p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have hpoint (r : ℝ) (hr : r ∈ Ioc 0 (T : ℝ)) := U.stopped_coefficients n r hr
  choose hb hσ hg using hpoint
  have hB : ∀ r (hr : r ∈ Ioc 0 (T : ℝ)), ‖(hb r hr).toLp (U.stoppedDrift n r)‖ ^ 2 ≤
      3 * K ^ 2 * (1 + P ^ 2 + (3 * ‖U.initial_square.toLp (U.state 0)‖ ^ 2 +
        3 * (n : ℝ) ^ 2 + 3 * n)) := by
    intro r hr
    have hc := mul_le_mul_of_nonneg_left (U.stoppedState_moment_le n r (Ioc_subset_Icc_self hr))
      (show 0 ≤ 3 * K ^ 2 by positivity)
    nlinarith [hg r hr, sq_nonneg ‖(hσ r hr).toLp (U.packedStoppedSigma n r)‖]
  have hm := product_memLp_of_uniform_moment Q (U.stoppedDrift n) T
    (U.stoppedDrift_strong n) hb hB
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

/-- Literal actual stopped-state L² coordinate. -/
def stateLp (n : ℕ) (r : ℝ) : Lp Z 2 Q := sectionLp Q (U.stoppedState n) r

def driftLp (n : ℕ) (r : ℝ) : Lp Z 2 Q := sectionLp Q (U.stoppedDrift n) r

def sigmaCurve (U : Data L K P) (n : ℕ) : ℝ → ColumnHilbert (I := I) (Z := Z) Q :=
  rawDiffusionCurve Q (L.stoppedSigma n)

theorem driftLp_square (n : ℕ) : MemLp (U.driftLp n) 2 (volume.restrict (Ioc 0 (T : ℝ))) :=
  sectionLp_memLp _ Q _ (U.stoppedDrift_strong n) (U.stoppedDrift_product_square n)

theorem sigmaCurve_square (n : ℕ) :
    MemLp (U.sigmaCurve n) 2 (volume.restrict (Ioc 0 (T : ℝ))) :=
  rawDiffusionCurve_square Q T _ (L.stoppedSigma_strong n) (L.stoppedSigma_square n)

theorem sigmaCurve_adapted (n : ℕ) (t : ℝ≥0) (i : I) :
    AEStronglyMeasurable[D.filtration t] ((U.sigmaCurve n t).ofLp i) Q :=
  rawDiffusionCurve_adapted Q D _ (L.stoppedSigma_adapted n) t i

/-- Original raw stopped equations produce the actual integral equation in
L²; all raw/curve identities and drift Fubini transfer are derived. -/
theorem stateLp_integral (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    U.stateLp n t = U.stateLp n 0 + (∫ r in 0..t, U.driftLp n r) +
      ConstructedPredictableModel.integral Q D T (U.sigmaCurve n)
        (U.sigmaCurve_square n) (U.sigmaCurve_adapted n) t := by
  have hstate := sectionLp_ae Q (U.stoppedState n) (U.stoppedState_memLp n t ht)
  have hzero := sectionLp_ae Q (U.stoppedState n)
    (U.stoppedState_memLp n 0 ⟨le_rfl,T.coe_nonneg⟩)
  have hz : U.stateLp n 0 =ᵐ[Q] U.state 0 := hzero.trans (Eventually.of_forall (fun ω => by
    simp only [stoppedState, RawStoppingCoordinates.stoppedState, min_eq_left (L.stop n ω).coe_nonneg]))
  have hi := ConstructedPredictableModel.rawDrift_sections_integral_ae Q T
    (U.stoppedDrift n) (U.stoppedDrift_strong n) (U.stoppedDrift_product_square n) t ht
  have he := U.stopped_equation n t ht
  have hn : ConstructedPredictableModel.integral Q D T (U.sigmaCurve n)
        (U.sigmaCurve_square n) (U.sigmaCurve_adapted n) t = L.noise n t.toNNReal := rfl
  rw [hn]
  apply Lp.ext
  have hadd : (U.stateLp n 0 + (∫ r in 0..t, U.driftLp n r) + L.noise n t.toNNReal) =ᵐ[Q]
      fun ω => U.state 0 ω + (∫ r in 0..t, U.stoppedDrift n r ω) + L.version n t.toNNReal ω :=
    (Lp.coeFn_add _ _).trans (((Lp.coeFn_add _ _).add EventuallyEq.rfl).trans
      ((hz.add hi).add (L.version_ae n t.toNNReal).symm))
  exact hstate.trans (he.trans hadd.symm)

/-- The literal initial stopped state is the actual original initial class. -/
theorem stateLp_zero (n : ℕ) : U.stateLp n 0 = U.initial_square.toLp (U.state 0) := by
  apply Lp.ext
  have hz := sectionLp_ae Q (U.stoppedState n)
    (U.stoppedState_memLp n 0 ⟨le_rfl,T.coe_nonneg⟩)
  exact (hz.trans (Eventually.of_forall (fun ω => by
    simp only [stoppedState, RawStoppingCoordinates.stoppedState,
      min_eq_left (L.stop n ω).coe_nonneg]))).trans U.initial_square.coeFn_toLp.symm

/-- The actual finite-column L² curve has exactly the original packed
spatial L² norm. This identity is proved from literal finite coordinates. -/
theorem sigmaCurve_norm_sq (n : ℕ) (r : ℝ)
    (hσ : MemLp (U.packedStoppedSigma n r) 2 Q) :
    ‖U.sigmaCurve n r‖ ^ 2 = ‖hσ.toLp (U.packedStoppedSigma n r)‖ ^ 2 := by
  have hc (i : I) : MemLp (L.stoppedSigma n i r) 2 Q := by
    have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : I => Z) i).comp_memLp' hσ
    exact hp
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i, ‖sectionLp Q (L.stoppedSigma n i) r‖ ^ 2) = _
  calc
    _ = ∑ i, ∫ ω, ‖L.stoppedSigma n i r ω‖ ^ 2 ∂Q :=
      Finset.sum_congr rfl (fun i _ => sectionLp_norm_sq Q _ (hc i))
    _ = ∫ ω, ∑ i, ‖L.stoppedSigma n i r ω‖ ^ 2 ∂Q :=
      (integral_finsetSum _ (fun i _ =>
        (memLp_two_iff_integrable_sq_norm (hc i).aestronglyMeasurable).mp (hc i))).symm
    _ = _ := by
      rw [toLp_norm_sq Q _ hσ]
      apply integral_congr_ae
      filter_upwards with ω
      simpa only [packedStoppedSigma, WithLp.ofLp_toLp] using
        (PiLp.norm_sq_eq_of_L2 (fun _ : I => Z) (U.packedStoppedSigma n r ω)).symm

/-- Primitive pointwise linear growth gives the actual stopped-curve
quadratic coefficient inequality needed by deterministic Volterra comparison. -/
theorem stoppedLp_growth (n : ℕ) (r : ℝ) (hr : r ∈ Ioc 0 (T : ℝ)) :
    ‖U.driftLp n r‖ ^ 2 + ‖U.sigmaCurve n r‖ ^ 2 ≤
      (3 * K ^ 2) * ((1 + P ^ 2) + ‖U.stateLp n r‖ ^ 2) := by
  obtain ⟨hb, hσ, hg⟩ := U.stopped_coefficients n r hr
  rw [U.sigmaCurve_norm_sq n r hσ]
  simpa only [driftLp, stateLp, sectionLp, dite_eq_left hb,
    dite_eq_left (U.stoppedState_memLp n r (Ioc_subset_Icc_self hr)), add_assoc] using hg

/-- Explicit global moment budget independent of the localization index. -/
def momentBudget : ℝ :=
  Real.exp ((3 * (T+1) * (3*K^2)) * T) *
    (3 * ‖U.initial_square.toLp (U.state 0)‖ ^ 2 + (1+P^2)) - (1+P^2)

/-- The actual localized process obeys a horizon-uniform moment bound with
no localization-dependent constant. All stochastic identities are derived. -/
theorem stateLp_uniform_moment (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ‖U.stateLp n t‖ ^ 2 ≤ U.momentBudget := by
  have hm := computed_uniform_moment_bound Q D (U.stateLp n) (U.driftLp n)
    (U.sigmaCurve n) T (by positivity : 0 ≤ (1+P^2 : ℝ)) (by positivity : 0 ≤ (3*K^2 : ℝ))
    (U.driftLp_square n) (U.sigmaCurve_square n) (U.sigmaCurve_adapted n)
    (U.stateLp_integral n) (U.stoppedLp_growth n) t ht
  rw [U.stateLp_zero n] at hm
  exact hm

theorem momentBudget_nonneg : 0 ≤ U.momentBudget :=
  (sq_nonneg ‖U.stateLp 0 0‖).trans (U.stateLp_uniform_moment 0 0 ⟨le_rfl,T.coe_nonneg⟩)

/-- The original raw state has its actual global second moment by Fatou
from the constructed horizon-exhausting stopped processes. -/
theorem globalState_moment (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ∃ hX : MemLp (U.state t) 2 Q, ‖hX.toLp (U.state t)‖ ^ 2 ≤ U.momentBudget := by
  have hb (n : ℕ) : ‖(U.stoppedState_memLp n t ht).toLp (U.stoppedState n t)‖ ^ 2 ≤
      U.momentBudget := by
    have hs := U.stateLp_uniform_moment n t ht
    simpa only [stateLp, sectionLp, dite_eq_left (U.stoppedState_memLp n t ht)] using hs
  apply localized_limit_memLp Q (fun n => U.stoppedState n t) (U.state t)
    U.momentBudget_nonneg (fun n => U.stoppedState_memLp n t ht) hb
  exact RawStoppingCoordinates.stoppedState_tendsto Q L.stop T U.state
    (Eventually.of_forall L.stop_eventually_horizon) t ht

theorem state_memLp (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : MemLp (U.state t) 2 Q :=
  (U.globalState_moment t ht).choose

theorem state_moment_le (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    ‖(U.state_memLp t ht).toLp (U.state t)‖ ^ 2 ≤ U.momentBudget :=
  (U.globalState_moment t ht).choose_spec

def packedSigma (U : Data L K P) (r : ℝ) (ω : Ω) : PiLp 2 (fun _ : I => Z) :=
  WithLp.toLp 2 (fun i => L.sigma i r ω)

theorem packedSigma_strong : StronglyMeasurable (Function.uncurry U.packedSigma) :=
  (PiLp.continuous_toLp 2 (fun _ : I => Z)).comp_stronglyMeasurable
    (measurable_pi_iff.mpr (fun i => (L.sigma_strong i).measurable)).stronglyMeasurable

/-- Spatial moments of the full original coefficients follow at every time,
including time zero; exceptional non-L² sections are not silently discarded. -/
theorem global_coefficients (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
    ∃ hb : MemLp (U.drift r) 2 Q, ∃ hσ : MemLp (U.packedSigma r) 2 Q,
      ‖hb.toLp (U.drift r)‖ ^ 2 + ‖hσ.toLp (U.packedSigma r)‖ ^ 2 ≤
        3 * K ^ 2 * (1 + P ^ 2 + ‖(U.state_memLp r hr).toLp (U.state r)‖ ^ 2) :=
  coefficients_of_linear_growth Q (U.state r) (U.drift r) (U.packedSigma r)
    (U.state_memLp r hr) U.drift_strong.of_uncurry_left.aestronglyMeasurable
    U.packedSigma_strong.of_uncurry_left.aestronglyMeasurable U.K_nonneg U.P_nonneg (U.growth r hr)

/-- The original drift and all finite physical diffusion columns have actual
global expected time-square integrability. This is a conclusion of primitive
linear growth and the original local strong equation. -/
theorem coefficients_square :
    Integrable (fun p : ℝ × Ω => ‖U.drift p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) ∧
    ∀ i, Integrable (fun p : ℝ × Ω => ‖L.sigma i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  have hglobal := coefficient_product_memLp Q U.state U.drift U.packedSigma T
    U.K_nonneg U.P_nonneg U.drift_strong U.packedSigma_strong
    (fun t ht => U.state_memLp t (Ioc_subset_Icc_self ht))
    (fun t ht => U.state_moment_le t (Ioc_subset_Icc_self ht))
    (fun t ht => U.growth t (Ioc_subset_Icc_self ht))
  refine ⟨(memLp_two_iff_integrable_sq_norm hglobal.1.aestronglyMeasurable).mp hglobal.1, ?_⟩
  intro i
  have hp := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : I => Z) i).comp_memLp' hglobal.2
  exact (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).mp hp

/-- The local integral in the original equation is the actual global raw
computed Brownian integral after linear-growth moment transfer. Equality is
derived by genuine stopped-integral identities and horizon exhaustion. -/
theorem localNoise_eq_global (t : ℝ≥0) (ht : t ≤ T) :
    L.localNoise t =ᵐ[Q] rawDiffusionIntegral Q D T L.sigma L.sigma_strong
      U.coefficients_square.2 L.sigma_adapted t := by
  obtain ⟨M, hMmart, hMcont, hM⟩ := rawDiffusionIntegral_exists_continuous_martingale Q D T
    L.sigma L.sigma_strong U.coefficients_square.2 L.sigma_adapted
  have hstop (n : ℕ) : ∀ᵐ ω ∂Q, ∀ s : ℝ≥0,
      L.version n s ω = M (min s (L.stop n ω)) ω :=
    rawDiffusionIntegral_stopped_version Q D T (L.stop n) (L.stop_bound n) (L.stop_stopping n)
      L.sigma (L.stoppedSigma n) L.sigma_strong U.coefficients_square.2 L.sigma_adapted
      (L.stoppedSigma_strong n) (L.stoppedSigma_square n) (L.stoppedSigma_adapted n)
      (fun _ _ _ => rfl) M (L.version n) hM (L.version_ae n) hMcont (L.version_continuous n)
  have heq : L.localNoise t =ᵐ[Q] M t := by
    filter_upwards [ae_all_iff.mpr hstop, L.version_eventually_localNoise] with ω hs hl
    obtain ⟨n, hn, hnl⟩ := ((L.stop_eventually_horizon ω).and (hl t ht)).exists
    exact hnl.symm.trans (by simpa only [hn, min_eq_left ht] using hs n t)
  exact heq.trans (hM t)

/-- The original raw state equation is now realized by the actual global
computed integral; no global-noise or L²-coordinate compatibility is assumed. -/
theorem global_equation (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    U.state t =ᵐ[Q] fun ω => U.state 0 ω + (∫ r in 0..t, U.drift r ω) +
      rawDiffusionIntegral Q D T L.sigma L.sigma_strong U.coefficients_square.2
        L.sigma_adapted t.toNNReal ω := by
  filter_upwards [U.equation, U.localNoise_eq_global t.toNNReal (by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1]; exact ht.2)] with ω he hn
  rw [he t ht, hn]

end Data
end PBGSO.RawLinearGrowthState
