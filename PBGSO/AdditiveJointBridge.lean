import PBGSO.MeanFieldContraction
import PBGSO.SeparatedCriteria
import PBGSO.WeakContraction

/-! # From source law monotonicity to constructed additive integral processes

The joint sampler law is the pushforward of the actual L² pair on the common
probability space. Its marginals, expectations, weighted work and quadratic
cost are identified explicitly. Source joint monotonicity therefore yields the
lifted drift dissipation; that lifted inequality is not an assumption.
The optimiser response is autonomous in this subclass, and diffusion columns
are constant. No conservative potential or equality of force types is used.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace Topology
namespace PBGSO

section L2Geometry
variable {Ω A Z : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Weighted L² pairing is the actual integral of the pointwise pairing. -/
theorem lp_weighted_pairing_eq_integral (W : Z →L[ℝ] Z) (X Y : Lp Z 2 Q) :
    ⟪X, W.compLpL 2 Q Y⟫_ℝ = ∫ ω, ⟪X ω, W (Y ω)⟫_ℝ ∂Q := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [W.coeFn_compLpL Y] with ω hω
  rw [hω]

/-- The displayed pointwise weighted work is integrable, as a product of
actual L² variables. -/
theorem lp_weighted_pairing_integrable (W : Z →L[ℝ] Z) (X Y : Lp Z 2 Q) :
    Integrable (fun ω ↦ ⟪X ω, W (Y ω)⟫_ℝ) Q := by
  have h := L2.integrable_inner (𝕜 := ℝ) X (W.compLpL 2 Q Y)
  apply h.congr
  filter_upwards [W.coeFn_compLpL Y] with ω hω
  rw [hω]

/-- The diagonal weighted bilinear form on deterministic optimiser states
and actual L² sampler states. It does not require a metric square-root map. -/
def liftedMetricBilinear (D : TwistedGeometry A Z) :
    (A × Lp Z 2 Q) →L[ℝ] (A × Lp Z 2 Q) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.fst ℝ A (Lp Z 2 Q))
    (D.optimizerWeight.comp (ContinuousLinearMap.fst ℝ A (Lp Z 2 Q))) +
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.snd ℝ A (Lp Z 2 Q))
    ((D.samplerWeight.compLpL 2 Q).comp (ContinuousLinearMap.snd ℝ A (Lp Z 2 Q)))

theorem liftedMetricBilinear_apply (D : TwistedGeometry A Z)
    (x y : A × Lp Z 2 Q) :
    liftedMetricBilinear Q D x y = ⟪x.1, D.optimizerWeight y.1⟫_ℝ +
      ∫ ω, ⟪x.2 ω, D.samplerWeight (y.2 ω)⟫_ℝ ∂Q := by
  change ⟪x.1, D.optimizerWeight y.1⟫_ℝ +
    ⟪x.2, D.samplerWeight.compLpL 2 Q y.2⟫_ℝ = _
  rw [lp_weighted_pairing_eq_integral]

theorem liftedMetricBilinear_symmetric (D : TwistedGeometry A Z)
    (x y : A × Lp Z 2 Q) :
    liftedMetricBilinear Q D x y = liftedMetricBilinear Q D y x := by
  rw [liftedMetricBilinear_apply, liftedMetricBilinear_apply]
  congr 1
  · exact (D.optimizer_symmetric _ _).trans (real_inner_comm _ _)
  · apply integral_congr_ae
    exact ae_of_all Q fun ω ↦ (D.sampler_symmetric _ _).trans (real_inner_comm _ _)

/-- The original Euclidean optimiser/sampler coupling energy. -/
def liftedEuclideanSq (x : A × Lp Z 2 Q) : ℝ := ‖x.1‖ ^ 2 + ‖x.2‖ ^ 2

theorem liftedMetricBilinear_lower (D : TwistedGeometry A Z) (x : A × Lp Z 2 Q) :
    D.lower * liftedEuclideanSq Q x ≤ liftedMetricBilinear Q D x x := by
  have hi := integral_mono
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x.2)).mp (Lp.memLp x.2)).const_mul D.lower)
    (lp_weighted_pairing_integrable Q D.samplerWeight x.2 x.2)
    (fun ω ↦ D.sampler_lower (x.2 ω))
  rw [integral_const_mul, ← ProximalLangevin.lp_norm_sq_eq_integral Q x.2] at hi
  rw [liftedMetricBilinear_apply]
  dsimp [liftedEuclideanSq]
  have ho := D.optimizer_lower x.1
  linarith

theorem liftedMetricBilinear_upper (D : TwistedGeometry A Z) (x : A × Lp Z 2 Q) :
    liftedMetricBilinear Q D x x ≤ D.upper * liftedEuclideanSq Q x := by
  have hi := integral_mono (lp_weighted_pairing_integrable Q D.samplerWeight x.2 x.2)
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable x.2)).mp (Lp.memLp x.2)).const_mul D.upper)
    (fun ω ↦ D.sampler_upper (x.2 ω))
  rw [integral_const_mul, ← ProximalLangevin.lp_norm_sq_eq_integral Q x.2] at hi
  rw [liftedMetricBilinear_apply]
  dsimp [liftedEuclideanSq]
  have ho := D.optimizer_upper x.1
  linarith

end L2Geometry

section JointLaw
variable {Ω A G Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Identities connecting the primitive independent Lipschitz maps to the
source model. Autonomous response and constant diffusion are explicit scope
restrictions of this constructed additive subclass. -/
structure AdditiveModelCompatibility (L : LipschitzDynamics A Z G) (M : Model A G Z X I) : Prop where
  observation : ∀ a z, M.observation (M.parameter a) (M.position z) = L.observation a z
  response : ∀ t, 0 ≤ t → ∀ a g, M.optimizer t a g = L.response (a, g)
  sampler : ∀ a z, M.drift (M.parameter a) z = L.sampler a z
  diffusion_constant : ∀ a b z w i,
    M.diffusion (M.parameter a) z i = M.diffusion (M.parameter b) w i

/-- Actual joint law on the common probability space. -/
def samplerPairLaw (U V : Lp Z 2 Q) : Measure (Z × Z) :=
  Q.map (fun ω ↦ (U ω, V ω))

theorem samplerPairLaw_coupling (U V : Lp Z 2 Q) :
    IsCoupling (samplerPairLaw Q U V) (Q.map U) (Q.map V) := by
  constructor
  · rw [samplerPairLaw, Measure.map_map measurable_fst
      ((Lp.stronglyMeasurable U).measurable.prodMk (Lp.stronglyMeasurable V).measurable)]
    rfl
  · rw [samplerPairLaw, Measure.map_map measurable_snd
      ((Lp.stronglyMeasurable U).measurable.prodMk (Lp.stronglyMeasurable V).measurable)]
    rfl

theorem lp_law_second_moment (U : Lp Z 2 Q) : HasFiniteSecondMoment (Q.map U) := by
  apply (integrable_map_measure (by fun_prop)
    (Lp.aestronglyMeasurable U).aemeasurable).mpr
  exact (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U)).mp (Lp.memLp U)

theorem model_meanGradient_eq_expectedObservation
    (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (a : A) (U : Lp Z 2 Q) :
    M.meanGradient (Q.map U) a = L.expectedObservation Q a U := by
  rw [Model.meanGradient, LipschitzDynamics.expectedObservation_eq_integral Q L a U]
  simp_rw [H.observation]
  exact integral_map (Lp.aestronglyMeasurable U).aemeasurable
    (L.observation_state a).continuous.aestronglyMeasurable

/-- Constant diffusion cancels exactly in the source coupling work. -/
theorem additive_sampler_work (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (D : TwistedGeometry A Z)
    (a b : A) (zz : Z × Z) :
    samplerCouplingWork M D a b zz =
      ⟪zz.1 - zz.2, D.samplerWeight (L.sampler a zz.1 - L.sampler b zz.2)⟫_ℝ := by
  have hz (i : I) : M.diffusion (M.parameter a) zz.1 i -
      M.diffusion (M.parameter b) zz.2 i = 0 :=
    sub_eq_zero.mpr (H.diffusion_constant a b zz.1 zz.2 i)
  simp only [samplerCouplingWork, hz, TwistedGeometry.samplerSq, map_zero,
    inner_zero_right, Finset.sum_const_zero, mul_zero, add_zero, H.sampler]

theorem samplerPairLaw_cost_integral (D : TwistedGeometry A Z) (U V : Lp Z 2 Q) :
    (∫ zz, D.samplerSq (zz.1 - zz.2) ∂samplerPairLaw Q U V) =
      ⟪U - V, D.samplerWeight.compLpL 2 Q (U - V)⟫_ℝ := by
  have hc : Continuous (fun zz : Z × Z ↦ D.samplerSq (zz.1 - zz.2)) := by
    dsimp [TwistedGeometry.samplerSq]
    fun_prop
  rw [samplerPairLaw, integral_map
    (((Lp.aestronglyMeasurable U).aemeasurable).prodMk
      (Lp.aestronglyMeasurable V).aemeasurable) hc.aestronglyMeasurable,
    lp_weighted_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub U V] with ω hω
  simp only [Pi.sub_apply] at hω
  rw [hω]
  rfl

theorem samplerPairLaw_cost_integrable (D : TwistedGeometry A Z) (U V : Lp Z 2 Q) :
    Integrable (fun zz ↦ D.samplerSq (zz.1 - zz.2)) (samplerPairLaw Q U V) := by
  have hc : Continuous (fun zz : Z × Z ↦ D.samplerSq (zz.1 - zz.2)) := by
    dsimp [TwistedGeometry.samplerSq]
    fun_prop
  apply (integrable_map_measure hc.aestronglyMeasurable
    (((Lp.aestronglyMeasurable U).aemeasurable).prodMk
      (Lp.aestronglyMeasurable V).aemeasurable)).mpr
  apply (lp_weighted_pairing_integrable Q D.samplerWeight (U - V) (U - V)).congr
  filter_upwards [Lp.coeFn_sub U V] with ω hω
  simp only [Pi.sub_apply] at hω
  rw [hω]
  rfl

/-- A true L² drift difference represents the pointwise sampler difference. -/
theorem sampler_drift_difference_coe (L : LipschitzDynamics A Z G)
    (a b : A) (U V : Lp Z 2 Q) :
    (liftMap Q (L.sampler a) (L.sampler_state a) U -
      liftMap Q (L.sampler b) (L.sampler_state b) V) =ᵐ[Q]
      fun ω ↦ L.sampler a (U ω) - L.sampler b (V ω) := by
  filter_upwards [Lp.coeFn_sub (liftMap Q (L.sampler a) (L.sampler_state a) U)
    (liftMap Q (L.sampler b) (L.sampler_state b) V),
    liftMap_coe Q (L.sampler a) (L.sampler_state a) U,
    liftMap_coe Q (L.sampler b) (L.sampler_state b) V] with ω hs hu hv
  simp only [Pi.sub_apply] at hs
  rw [hs, hu, hv]

theorem samplerPairLaw_work_integral (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (D : TwistedGeometry A Z)
    (a b : A) (U V : Lp Z 2 Q) :
    (∫ zz, samplerCouplingWork M D a b zz ∂samplerPairLaw Q U V) =
      ⟪U - V, D.samplerWeight.compLpL 2 Q
        (liftMap Q (L.sampler a) (L.sampler_state a) U -
          liftMap Q (L.sampler b) (L.sampler_state b) V)⟫_ℝ := by
  simp_rw [additive_sampler_work L M H D]
  have hc : Continuous (fun zz : Z × Z ↦
      ⟪zz.1 - zz.2, D.samplerWeight (L.sampler a zz.1 - L.sampler b zz.2)⟫_ℝ) := by
    exact (continuous_fst.sub continuous_snd).inner
      (D.samplerWeight.continuous.comp (((L.sampler_state a).continuous.comp continuous_fst).sub
        ((L.sampler_state b).continuous.comp continuous_snd)))
  rw [samplerPairLaw, integral_map
    (((Lp.aestronglyMeasurable U).aemeasurable).prodMk
      (Lp.aestronglyMeasurable V).aemeasurable) hc.aestronglyMeasurable,
    lp_weighted_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub U V, sampler_drift_difference_coe Q L a b U V] with ω hd hb
  simp only [Pi.sub_apply] at hd
  rw [hd, hb]

theorem samplerPairLaw_work_integrable (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (D : TwistedGeometry A Z)
    (a b : A) (U V : Lp Z 2 Q) :
    Integrable (samplerCouplingWork M D a b) (samplerPairLaw Q U V) := by
  have heq : samplerCouplingWork M D a b = fun zz ↦
      ⟪zz.1 - zz.2, D.samplerWeight (L.sampler a zz.1 - L.sampler b zz.2)⟫_ℝ :=
    funext (additive_sampler_work L M H D a b)
  rw [heq]
  have hc : Continuous (fun zz : Z × Z ↦
      ⟪zz.1 - zz.2, D.samplerWeight (L.sampler a zz.1 - L.sampler b zz.2)⟫_ℝ) := by
    exact (continuous_fst.sub continuous_snd).inner
      (D.samplerWeight.continuous.comp (((L.sampler_state a).continuous.comp continuous_fst).sub
        ((L.sampler_state b).continuous.comp continuous_snd)))
  apply (integrable_map_measure hc.aestronglyMeasurable
    (((Lp.aestronglyMeasurable U).aemeasurable).prodMk
      (Lp.aestronglyMeasurable V).aemeasurable)).mpr
  apply (lp_weighted_pairing_integrable Q D.samplerWeight (U - V)
    (liftMap Q (L.sampler a) (L.sampler_state a) U -
      liftMap Q (L.sampler b) (L.sampler_state b) V)).congr
  filter_upwards [Lp.coeFn_sub U V, sampler_drift_difference_coe Q L a b U V] with ω hd hb
  simp only [Pi.sub_apply] at hd
  rw [hd, hb]
  rfl

/-- Source A3 now implies the actual lifted quadratic drift inequality.
The law coupling and every expectation/work/cost identification are proved
from actual random variables and the primitive independent Lipschitz maps. -/
theorem lifted_joint_dissipation_of_model (L : LipschitzDynamics A Z G)
    (M : Model A G Z X I) (H : AdditiveModelCompatibility L M)
    (D : TwistedGeometry A Z) (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (x y : A × Lp Z 2 Q) :
    liftedMetricBilinear Q D (x - y) (L.field Q x - L.field Q y) ≤
      -ρ * liftedMetricBilinear Q D (x - y) (x - y) := by
  let U := x.2
  let V := y.2
  letI : IsProbabilityMeasure (Q.map U) :=
    (Measure.isProbabilityMeasure_map_iff (Lp.aestronglyMeasurable U).aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure (Q.map V) :=
    (Measure.isProbabilityMeasure_map_iff (Lp.aestronglyMeasurable V).aemeasurable).mpr inferInstance
  have hU := lp_law_second_moment Q U
  have hV := lp_law_second_moment Q V
  have hoU : Integrable
      (fun z ↦ M.observation (M.parameter x.1) (M.position z)) (Q.map U) := by
    simp_rw [H.observation]
    exact observation_integrable_of_lipschitz (Q.map U) _ (L.observation_state x.1) hU
  have hoV : Integrable
      (fun z ↦ M.observation (M.parameter y.1) (M.position z)) (Q.map V) := by
    simp_rw [H.observation]
    exact observation_integrable_of_lipschitz (Q.map V) _ (L.observation_state y.1) hV
  have h := hmono 0 le_rfl x.1 y.1 (Q.map U) (Q.map V) (samplerPairLaw Q U V)
    (samplerPairLaw_coupling Q U V) inferInstance inferInstance hU hV hoU hoV
    (samplerPairLaw_work_integrable Q L M H D x.1 y.1 U V)
    (samplerPairLaw_cost_integrable Q D U V)
  rw [samplerPairLaw_work_integral Q L M H D x.1 y.1 U V,
    samplerPairLaw_cost_integral Q D U V] at h
  have hf (a : A) (Z : Lp Z 2 Q) : M.optimizerField 0 a (Q.map Z) =
      L.response (a, L.expectedObservation Q a Z) := by
    rw [Model.optimizerField, H.response 0 le_rfl,
      model_meanGradient_eq_expectedObservation Q L M H a Z]
  rw [hf x.1 U, hf y.1 V] at h
  exact h

/-- Squared weighted contraction for actual integral solutions, now from
source model A3 rather than an assumed lifted monotonicity inequality. -/
theorem additive_model_integral_energy_decay
    (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (D : TwistedGeometry A Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (Y W : ℝ → A × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q)
    (hY : Continuous Y) (hW : Continuous W) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T,
      Y t - Y 0 = (∫ s in 0..t, L.field Q (Y s)) + (0, B t))
    (heW : ∀ t ∈ Icc 0 T,
      W t - W 0 = (∫ s in 0..t, L.field Q (W s)) + (0, B t))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    liftedMetricBilinear Q D (Y t - W t) (Y t - W t) ≤
      liftedMetricBilinear Q D (Y 0 - W 0) (Y 0 - W 0) * Real.exp (-2 * ρ * t) := by
  let Bq := liftedMetricBilinear Q D
  let F := fun r ↦ Bq (Y r - W r) (Y r - W r)
  let F' := fun r ↦ 2 * Bq (Y r - W r) (L.field Q (Y r) - L.field Q (W r))
  have hc : ContinuousOn F (Icc 0 T) := by
    apply Continuous.continuousOn
    exact (Bq.continuous.comp (hY.sub hW)).clm_apply (hY.sub hW)
  have hd : ∀ r ∈ Ico 0 T, HasDerivWithinAt F (F' r) (Ici r) r := by
    intro r hr
    have hg : LipschitzWith L.fieldLip (fun z ↦ -L.field Q z) := (L.field_lipschitz Q).neg
    have heY' : ∀ s ∈ Icc 0 T,
        Y s - Y 0 = -(∫ u in 0..s, -L.field Q (Y u)) + (0, B s) := by
      intro s hs
      simpa only [intervalIntegral.integral_neg, neg_neg] using heY s hs
    have heW' : ∀ s ∈ Icc 0 T,
        W s - W 0 = -(∫ u in 0..s, -L.field Q (W u)) + (0, B s) := by
      intro s hs
      simpa only [intervalIntegral.integral_neg, neg_neg] using heW s hs
    have hdiff := KineticLangevin.integral_difference_hasDerivWithinAt
      (fun z ↦ -L.field Q z) L.fieldLip hg Y W (fun s ↦ (0, B s)) hY hW T heY' heW' r hr
    have hd' : HasDerivWithinAt (fun s ↦ Y s - W s)
        (L.field Q (Y r) - L.field Q (W r)) (Ici r) r := by
      convert hdiff using 1 <;> module
    have hF := (quadratic_hasFDerivAt Bq (Y r - W r)).comp_hasDerivWithinAt r hd'
    have hsym := liftedMetricBilinear_symmetric Q D
      (L.field Q (Y r) - L.field Q (W r)) (Y r - W r)
    convert hF using 1
    · rfl
    · change 2 * Bq (Y r - W r) (L.field Q (Y r) - L.field Q (W r)) =
        Bq (Y r - W r) (L.field Q (Y r) - L.field Q (W r)) +
          Bq (L.field Q (Y r) - L.field Q (W r)) (Y r - W r)
      rw [hsym]
      ring
  have hm : ∀ r ∈ Ico 0 T, F' r ≤ -2 * ρ * F r := by
    intro r _
    have h := lifted_joint_dissipation_of_model Q L M H D ρ hmono (Y r) (W r)
    dsimp [F', F, Bq]
    linarith
  exact energy_decay hc hd hm t ht

/-- The exact source condition-number contraction for constructed additive
integral solutions in the optimiser-plus-L² Euclidean product metric. -/
theorem additive_model_integral_contraction
    (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (D : TwistedGeometry A Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (Y W : ℝ → A × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q)
    (hY : Continuous Y) (hW : Continuous W) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T,
      Y t - Y 0 = (∫ s in 0..t, L.field Q (Y s)) + (0, B t))
    (heW : ∀ t ∈ Icc 0 T,
      W t - W 0 = (∫ s in 0..t, L.field Q (W s)) + (0, B t))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Real.sqrt (liftedEuclideanSq Q (Y t - W t)) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
        Real.sqrt (liftedEuclideanSq Q (Y 0 - W 0)) := by
  have hd := additive_model_integral_energy_decay Q L M H D ρ hmono Y W B hY hW T heY heW t ht
  have hlo := liftedMetricBilinear_lower Q D (Y t - W t)
  have hup := liftedMetricBilinear_upper Q D (Y 0 - W 0)
  have hκ : 0 ≤ D.conditionNumber := le_trans (by norm_num : (0 : ℝ) ≤ 1) D.conditionNumber_ge_one
  have hn (x : A × Lp Z 2 Q) : 0 ≤ liftedEuclideanSq Q x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (hn _), mul_pow, mul_pow, Real.sq_sqrt hκ, Real.sq_sqrt (hn _)]
  have he : Real.exp (-ρ * t) ^ 2 = Real.exp (-2 * ρ * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  apply (mul_le_mul_iff_of_pos_left D.lower_pos).mp
  have hupper := mul_le_mul_of_nonneg_right hup (Real.exp_pos (-2 * ρ * t)).le
  have heq : D.lower * (D.conditionNumber * Real.exp (-2 * ρ * t) *
      liftedEuclideanSq Q (Y 0 - W 0)) =
      D.upper * liftedEuclideanSq Q (Y 0 - W 0) * Real.exp (-2 * ρ * t) := by
    dsimp [TwistedGeometry.conditionNumber]
    field_simp [ne_of_gt D.lower_pos]
  rw [heq]
  exact hlo.trans (hd.trans hupper)

/-- Picard constructs both actual mean-field trajectories, and source A3
then contracts them. The common continuous sampler input may be the actual
L² Brownian input; the optimiser coordinate receives zero noise. -/
theorem exists_additive_model_contracting_pair
    (L : LipschitzDynamics A Z G) (M : Model A G Z X I)
    (H : AdditiveModelCompatibility L M) (D : TwistedGeometry A Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (initial other : A × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q)
    (hB : Continuous B) (hB0 : B 0 = 0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y W : ℝ → A × Lp Z 2 Q,
      Continuous Y ∧ Continuous W ∧ Y 0 = initial ∧ W 0 = other ∧
      (∀ t ∈ Icc 0 T, Y t - initial = (∫ s in 0..t, L.field Q (Y s)) + (0, B t)) ∧
      (∀ t ∈ Icc 0 T, W t - other = (∫ s in 0..t, L.field Q (W s)) + (0, B t)) ∧
      (∀ t ∈ Icc 0 T, Real.sqrt (liftedEuclideanSq Q (Y t - W t)) ≤
        Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
          Real.sqrt (liftedEuclideanSq Q (initial - other))) := by
  obtain ⟨Y, hY, hiY, heY⟩ := L.exists_integral Q initial B hB hB0 T hT
  obtain ⟨W, hW, hiW, heW⟩ := L.exists_integral Q other B hB hB0 T hT
  refine ⟨Y, W, hY, hW, hiY, hiW, heY, heW, ?_⟩
  intro t ht
  have h := additive_model_integral_contraction Q L M H D ρ hmono Y W B hY hW T
    (fun s hs ↦ by simpa only [hiY] using heY s hs)
    (fun s hs ↦ by simpa only [hiW] using heW s hs) t ht
  simpa only [hiY, hiW] using h

end JointLaw
end PBGSO
