import PBGSO.GeneralProcess

/-! # Constructing the general interacting particle integral equation

The shared optimiser is a random coordinate of the particle state. Every
sampler particle uses this same optimiser and the actual finite-sum
observation. The construction has no potential assumption and no optimiser
noise. It gives norm-continuous L² solutions for additive input.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO.LipschitzDynamics

variable {A Z G : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  (D : PBGSO.LipschitzDynamics A Z G)

/-- The particle observation is the actual finite average. -/
def averageObservation (N : ℕ) (s : A × (Fin N → Z)) : G :=
  (N : ℝ)⁻¹ • ∑ i, D.observation s.1 (s.2 i)

theorem averageObservation_bound (N : ℕ) (hN : 0 < N)
    (s t : A × (Fin N → Z)) :
    ‖D.averageObservation N s - D.averageObservation N t‖ ≤
      2 * (D.observationLip : ℝ) * ‖s - t‖ := by
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hobs (i : Fin N) :
      ‖D.observation s.1 (s.2 i) - D.observation t.1 (t.2 i)‖ ≤
        2 * (D.observationLip : ℝ) * ‖s - t‖ := by
    have ha := D.observation_parameter s.1 t.1 (s.2 i)
    have hx := (D.observation_state t.1).norm_sub_le (s.2 i) (t.2 i)
    have hs := norm_sub_le_norm_sub_add_norm_sub
      (D.observation s.1 (s.2 i)) (D.observation t.1 (s.2 i))
      (D.observation t.1 (t.2 i))
    have hA : ‖s.1 - t.1‖ ≤ ‖s - t‖ := norm_fst_le (s - t)
    have hZ : ‖s.2 i - t.2 i‖ ≤ ‖s - t‖ :=
      (norm_le_pi_norm (s.2 - t.2) i).trans (norm_snd_le (s - t))
    nlinarith [mul_le_mul_of_nonneg_left hA D.observationLip.coe_nonneg,
      mul_le_mul_of_nonneg_left hZ D.observationLip.coe_nonneg]
  calc
    _ = (N : ℝ)⁻¹ * ‖∑ i,
        (D.observation s.1 (s.2 i) - D.observation t.1 (t.2 i))‖ := by
      simp only [averageObservation, ← smul_sub, ← Finset.sum_sub_distrib,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
    _ ≤ (N : ℝ)⁻¹ * ∑ i, ‖D.observation s.1 (s.2 i) -
        D.observation t.1 (t.2 i)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, 2 * (D.observationLip : ℝ) * ‖s - t‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hobs i)
        (inv_nonneg.mpr hn.le)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hn), one_mul]

/-- The actual interacting field, with a single shared optimiser coordinate. -/
def particleField (N : ℕ) (s : A × (Fin N → Z)) : A × (Fin N → Z) :=
  (D.response (s.1, D.averageObservation N s), fun i => D.sampler s.1 (s.2 i))

/-- The global field constant is independent of particle count. -/
theorem particleField_lipschitz (N : ℕ) (hN : 0 < N) :
    LipschitzWith D.fieldLip (D.particleField N) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  simp only [dist_eq_norm]
  change max ‖D.response (s.1, D.averageObservation N s) -
      D.response (t.1, D.averageObservation N t)‖
    ‖(fun i => D.sampler s.1 (s.2 i)) - (fun i => D.sampler t.1 (t.2 i))‖ ≤ _
  have hA : ‖s.1 - t.1‖ ≤ ‖s - t‖ := norm_fst_le (s - t)
  have hG := D.averageObservation_bound N hN s t
  have hmax : max ‖s.1 - t.1‖ ‖D.averageObservation N s - D.averageObservation N t‖ ≤
      (1 + 2 * (D.observationLip : ℝ)) * ‖s - t‖ := by
    apply max_le
    · nlinarith [mul_nonneg D.observationLip.coe_nonneg (norm_nonneg (s - t))]
    · nlinarith [norm_nonneg (s - t)]
  have hR := D.response_lipschitz.norm_sub_le
    (s.1, D.averageObservation N s) (t.1, D.averageObservation N t)
  have hr : ‖D.response (s.1, D.averageObservation N s) -
      D.response (t.1, D.averageObservation N t)‖ ≤
      (D.responseLip : ℝ) * ((1 + 2 * (D.observationLip : ℝ)) * ‖s - t‖) :=
    hR.trans (mul_le_mul_of_nonneg_left hmax D.responseLip.coe_nonneg)
  have hS : ‖(fun i => D.sampler s.1 (s.2 i)) - (fun i => D.sampler t.1 (t.2 i))‖ ≤
      2 * (D.samplerLip : ℝ) * ‖s - t‖ := by
    apply pi_norm_le_iff_of_nonneg (by positivity) |>.mpr
    intro i
    change ‖D.sampler s.1 (s.2 i) - D.sampler t.1 (t.2 i)‖ ≤ _
    have ha := D.sampler_parameter s.1 t.1 (s.2 i)
    have hx := (D.sampler_state t.1).norm_sub_le (s.2 i) (t.2 i)
    have hs := norm_sub_le_norm_sub_add_norm_sub
      (D.sampler s.1 (s.2 i)) (D.sampler t.1 (s.2 i)) (D.sampler t.1 (t.2 i))
    have hZ : ‖s.2 i - t.2 i‖ ≤ ‖s - t‖ :=
      (norm_le_pi_norm (s.2 - t.2) i).trans (norm_snd_le (s - t))
    nlinarith [mul_le_mul_of_nonneg_left hA D.samplerLip.coe_nonneg,
      mul_le_mul_of_nonneg_left hZ D.samplerLip.coe_nonneg]
  apply max_le
  · dsimp [fieldLip]
    nlinarith [mul_nonneg D.samplerLip.coe_nonneg (norm_nonneg (s - t))]
  · dsimp [fieldLip]
    nlinarith [mul_nonneg D.responseLip.coe_nonneg
      (mul_nonneg (show 0 ≤ 1 + 2 * (D.observationLip : ℝ) by positivity)
        (norm_nonneg (s - t)))]

/-- L² existence for the complete interacting state and an arbitrary
continuous additive input. The initial optimiser may be random. The
sampler-only wrapper below enforces zero optimiser noise explicitly. -/
theorem exists_particle_integral {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (N : ℕ) (hN : 0 < N)
    (initial : Lp (A × (Fin N → Z)) 2 Q)
    (B : ℝ → Lp (A × (Fin N → Z)) 2 Q)
    (hB : Continuous B) (hB0 : B 0 = 0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → Lp (A × (Fin N → Z)) 2 Q, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 T, Y t - initial =
        (∫ s in 0..t, ULA.lpDrift Q (D.particleField N)
          (D.particleField_lipschitz N hN) (Y s)) + B t := by
  let f := ULA.lpDrift Q (D.particleField N) (D.particleField_lipschitz N hN)
  have hf : LipschitzWith D.fieldLip f := ULA.lpDrift_lipschitz Q _ _
  obtain ⟨Y, hc, hi, he⟩ := ULA.exists_langevin_integral
    (fun s => -f s) D.fieldLip hf.neg initial B hB hB0 T hT
  refine ⟨Y, hc, hi, ?_⟩
  intro t ht
  simpa only [intervalIntegral.integral_neg, neg_neg] using he t ht

/-- Embed sampler noise with a definitionally zero optimiser coordinate. -/
def particleSamplerInput {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (N : ℕ) (B : Lp (Fin N → Z) 2 Q) :
    Lp (A × (Fin N → Z)) 2 Q :=
  (ContinuousLinearMap.inr ℝ A (Fin N → Z)).compLp B

theorem particleSamplerInput_optimizer_zero {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (N : ℕ) (B : Lp (Fin N → Z) 2 Q) :
    ∀ᵐ ω ∂Q, ((particleSamplerInput (A := A) Q N B) ω).1 = 0 := by
  filter_upwards [(ContinuousLinearMap.inr ℝ A (Fin N → Z)).coeFn_compLp B] with ω he
  simp only [particleSamplerInput] at *
  rw [he]
  rfl

/-- General interacting particle dynamics with sampler-only additive input.
This is the noise structure in the manuscript; the optimiser is random
through its interaction with the particles and has no Brownian forcing. -/
theorem exists_particle_sampler_integral {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (N : ℕ) (hN : 0 < N)
    (initial : Lp (A × (Fin N → Z)) 2 Q)
    (B : ℝ → Lp (Fin N → Z) 2 Q) (hB : Continuous B) (hB0 : B 0 = 0)
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ Y : ℝ → Lp (A × (Fin N → Z)) 2 Q, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 T, Y t - initial =
        (∫ s in 0..t, ULA.lpDrift Q (D.particleField N)
          (D.particleField_lipschitz N hN) (Y s)) + particleSamplerInput Q N (B t) := by
  apply D.exists_particle_integral Q N hN initial
    (fun t => particleSamplerInput Q N (B t))
  · exact ((ContinuousLinearMap.inr ℝ A (Fin N → Z)).compLpL 2 Q).continuous.comp hB
  · change ((ContinuousLinearMap.inr ℝ A (Fin N → Z)).compLpL 2 Q) (B 0) = 0
    rw [hB0, map_zero]
  · exact hT

end PBGSO.LipschitzDynamics
