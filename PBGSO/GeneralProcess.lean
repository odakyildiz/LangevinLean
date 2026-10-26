import ProximalLangevin.MeanFieldProcess

/-! # Actual additive-input mean-field dynamics for general forces

The optimiser is a deterministic Banach-space coordinate, the sampler an L²
random variable. Observation, optimiser response and sampler drift are separate
globally Lipschitz maps. No potential or equality of coordinate dimensions is
required. This constructs norm-continuous integral solutions; it does not
assert an almost-surely continuous strong SDE or a state-dependent Itô integral.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace PBGSO

section Lift
variable {Ω E K : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedAddCommGroup K]
  (Q : Measure Ω) [IsFiniteMeasure Q]

/-- Centering a map between different normed spaces preserves its constant. -/
theorem centered_map_lipschitz (f : E → K) {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (fun x => f x - f 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hf.dist_le_mul x y

/-- Pointwise L² composition for a Lipschitz map between different spaces.
Subtracting its value at zero handles nonzero offsets. -/
def liftMap (f : E → K) {L : ℝ≥0} (hf : LipschitzWith L f)
    (X : Lp E 2 Q) : Lp K 2 Q :=
  (centered_map_lipschitz f hf).compLp (by simp) X + Lp.const 2 Q (f 0)

theorem liftMap_coe (f : E → K) {L : ℝ≥0} (hf : LipschitzWith L f)
    (X : Lp E 2 Q) : liftMap Q f hf X =ᵐ[Q] fun ω => f (X ω) := by
  unfold liftMap
  filter_upwards [Lp.coeFn_add ((centered_map_lipschitz f hf).compLp (by simp) X)
      (Lp.const 2 Q (f 0)),
    (centered_map_lipschitz f hf).coeFn_compLp (by simp) X,
    Lp.coeFn_const (μ := Q) (p := 2) (c := f 0)] with ω ha hc hz
  simp only [ha, hc, hz, Function.comp_apply, Pi.add_apply, Function.const_apply]
  exact sub_add_cancel _ _

theorem liftMap_lipschitz (f : E → K) {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (liftMap Q f hf) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  simp only [liftMap, dist_eq_norm, add_sub_add_right_eq_sub]
  exact (centered_map_lipschitz f hf).norm_compLp_sub_le (by simp) X Y
end Lift

section ParameterLift
variable {Ω A E K : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedAddCommGroup E] [NormedAddCommGroup K]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (f : A → E → K) (L : ℝ≥0)
  (hf : ∀ a, LipschitzWith L (f a))
  (ha : ∀ a b x, ‖f a x - f b x‖ ≤ (L : ℝ) * ‖a - b‖)

include ha

/-- The parameter dependence of the lift follows from the actual pointwise
force bound, rather than an assumed mean-field Lipschitz estimate. -/
theorem liftMap_parameter_bound (a b : A) (X : Lp E 2 Q) :
    ‖liftMap Q (f a) (hf a) X - liftMap Q (f b) (hf b) X‖ ≤
      (L : ℝ) * ‖a - b‖ := by
  have hbound : ∀ᵐ ω ∂Q,
      ‖(liftMap Q (f a) (hf a) X - liftMap Q (f b) (hf b) X) ω‖ ≤
        (L : ℝ) * ‖a - b‖ := by
    filter_upwards [Lp.coeFn_sub (liftMap Q (f a) (hf a) X)
      (liftMap Q (f b) (hf b) X), liftMap_coe Q (f a) (hf a) X,
      liftMap_coe Q (f b) (hf b) X] with ω hs hfa hfb
    simpa only [hs, hfa, hfb, Pi.sub_apply] using ha a b (X ω)
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound
    (show 0 ≤ (L : ℝ) * ‖a - b‖ by positivity) hbound

/-- Joint state dependence, in the product Banach norm. -/
theorem liftMap_joint_bound (a b : A) (X Y : Lp E 2 Q) :
    ‖liftMap Q (f a) (hf a) X - liftMap Q (f b) (hf b) Y‖ ≤
      2 * (L : ℝ) * ‖(a, X) - (b, Y)‖ := by
  have hsplit := norm_sub_le_norm_sub_add_norm_sub
    (liftMap Q (f a) (hf a) X) (liftMap Q (f b) (hf b) X)
    (liftMap Q (f b) (hf b) Y)
  have hp := liftMap_parameter_bound Q f L hf ha a b X
  have hx := (liftMap_lipschitz Q (f b) (hf b)).norm_sub_le X Y
  have hA : ‖a - b‖ ≤ ‖(a, X) - (b, Y)‖ := norm_fst_le ((a, X) - (b, Y))
  have hX : ‖X - Y‖ ≤ ‖(a, X) - (b, Y)‖ := norm_snd_le ((a, X) - (b, Y))
  nlinarith [mul_le_mul_of_nonneg_left hA L.coe_nonneg,
    mul_le_mul_of_nonneg_left hX L.coe_nonneg]
end ParameterLift

section Process
variable {Ω A Z G : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Regularity data for three independent maps. `observation` already includes
the parameter and position projections. `response` may contain auxiliary
optimiser variables; `sampler` may contain auxiliary sampling variables. -/
structure LipschitzDynamics (A Z G : Type*)
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] where
  observation : A → Z → G
  response : A × G → A
  sampler : A → Z → Z
  observationLip : ℝ≥0
  responseLip : ℝ≥0
  samplerLip : ℝ≥0
  observation_state : ∀ a, LipschitzWith observationLip (observation a)
  observation_parameter : ∀ a b z,
    ‖observation a z - observation b z‖ ≤ (observationLip : ℝ) * ‖a - b‖
  response_lipschitz : LipschitzWith responseLip response
  sampler_state : ∀ a, LipschitzWith samplerLip (sampler a)
  sampler_parameter : ∀ a b z,
    ‖sampler a z - sampler b z‖ ≤ (samplerLip : ℝ) * ‖a - b‖

namespace LipschitzDynamics
variable (D : LipschitzDynamics A Z G)

/-- The observation expectation is a genuine Bochner integral. -/
def expectedObservation (a : A) (X : Lp Z 2 Q) : G :=
  ProximalLangevin.lpExpectationCLM Q
    (liftMap Q (D.observation a) (D.observation_state a) X)

theorem expectedObservation_eq_integral (a : A) (X : Lp Z 2 Q) :
    D.expectedObservation Q a X = ∫ ω, D.observation a (X ω) ∂Q :=
  integral_congr_ae (liftMap_coe Q _ _ _)

theorem expectedObservation_bound (a b : A) (X Y : Lp Z 2 Q) :
    ‖D.expectedObservation Q a X - D.expectedObservation Q b Y‖ ≤
      2 * (D.observationLip : ℝ) * ‖(a, X) - (b, Y)‖ := by
  unfold expectedObservation
  rw [← map_sub]
  exact (ProximalLangevin.lpExpectationCLM_norm_le Q _).trans
    (liftMap_joint_bound Q D.observation D.observationLip
      D.observation_state D.observation_parameter a b X Y)

/-- The actual complete mean-field vector field. The optimiser coordinate is
deterministic and the sampler coordinate is an L² random variable. -/
def field (s : A × Lp Z 2 Q) : A × Lp Z 2 Q :=
  (D.response (s.1, D.expectedObservation Q s.1 s.2),
   liftMap Q (D.sampler s.1) (D.sampler_state s.1) s.2)

/-- An explicit global Lipschitz constant derived from the primitive maps. -/
def fieldLip : ℝ≥0 := D.responseLip * (1 + 2 * D.observationLip) + 2 * D.samplerLip

theorem field_lipschitz : LipschitzWith D.fieldLip (D.field Q) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [dist_eq_norm]
  change max ‖D.response (s.1, D.expectedObservation Q s.1 s.2) -
      D.response (t.1, D.expectedObservation Q t.1 t.2)‖
    ‖liftMap Q (D.sampler s.1) (D.sampler_state s.1) s.2 -
      liftMap Q (D.sampler t.1) (D.sampler_state t.1) t.2‖ ≤ _
  have hA : ‖s.1 - t.1‖ ≤ ‖s - t‖ := norm_fst_le (s - t)
  have hG := D.expectedObservation_bound Q s.1 t.1 s.2 t.2
  have hR := D.response_lipschitz.norm_sub_le
    (s.1, D.expectedObservation Q s.1 s.2) (t.1, D.expectedObservation Q t.1 t.2)
  have hB := liftMap_joint_bound Q D.sampler D.samplerLip
    D.sampler_state D.sampler_parameter s.1 t.1 s.2 t.2
  change ‖D.response _ - D.response _‖ ≤
    (D.responseLip : ℝ) * max ‖s.1 - t.1‖
      ‖D.expectedObservation Q s.1 s.2 - D.expectedObservation Q t.1 t.2‖ at hR
  have hc : max ‖s.1 - t.1‖
      ‖D.expectedObservation Q s.1 s.2 - D.expectedObservation Q t.1 t.2‖ ≤
      (1 + 2 * (D.observationLip : ℝ)) * ‖s - t‖ := by
    apply max_le
    · nlinarith [mul_nonneg D.observationLip.coe_nonneg (norm_nonneg (s - t))]
    · nlinarith [norm_nonneg (s - t)]
  have hr := hR.trans (mul_le_mul_of_nonneg_left hc D.responseLip.coe_nonneg)
  apply max_le
  · dsimp [fieldLip]
    nlinarith [mul_nonneg D.samplerLip.coe_nonneg (norm_nonneg (s - t))]
  · dsimp [fieldLip]
    nlinarith [mul_nonneg D.responseLip.coe_nonneg
      (mul_nonneg (show 0 ≤ 1 + 2 * (D.observationLip : ℝ) by positivity)
        (norm_nonneg (s - t)))]

/-- Picard constructs the actual general mean-field integral dynamics on
every finite horizon, from the three primitive Lipschitz maps. A continuous
L² Brownian input is one possible `B`; the optimiser receives zero input. -/
theorem exists_integral (initial : A × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q)
    (hB : Continuous B) (hB0 : B 0 = 0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → A × Lp Z 2 Q, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 T, Y t - initial =
        (∫ s in 0..t, D.field Q (Y s)) + (0, B t) := by
  have hg : LipschitzWith D.fieldLip (fun s => -D.field Q s) :=
    (D.field_lipschitz Q).neg
  obtain ⟨Y, hc, hi, he⟩ := ULA.exists_langevin_integral
    (fun s => -D.field Q s) D.fieldLip hg initial (fun t => (0, B t))
      (continuous_const.prodMk hB) (by simp [hB0]) T hT
  refine ⟨Y, hc, hi, ?_⟩
  intro t ht
  simpa only [intervalIntegral.integral_neg, neg_neg] using he t ht
end LipschitzDynamics
end Process
end PBGSO
