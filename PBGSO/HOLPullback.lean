import PBGSO.GaussianMethodBounds
import PBGSO.LpPullback
import PBGSO.ParticleMethodLp
import PBGSO.NumericsTarget

/-! # HOL Gaussian innovations on actual initial/noise product spaces
Measure-preserving pullback transports the entire actual four-kernel Gaussian
array and its coupled Brownian increments. Both the full joint law and the
L² coupling budget are preserved. This permits a random initial particle
cloud on a product seed space, rather than fixing the probability space to
the canonical Brownian source used to construct the Wiener integrals.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace PBGSO.Methods
variable {Ω : Type*} [MeasurableSpace Ω]
  (I : Type*) [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {f : Ω → ULA.CanonicalBrownian.VectorSample I}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability I))

/-- The actual four coupled kernels pulled back from their common source. -/
def holPullbackVectorNoise (α γ : ℝ) (a h : ℝ≥0) (j : Fin 4) :
    Lp (EuclideanSpace ℝ I) 2 Q :=
  lpPullbackCLM hf (holVectorNoise I α γ a h j)

/-- The entire innovation array has exactly its original joint law.
Consequently spatial/temporal independence and every covariance relation
proved for the canonical construction survive this actual change of space. -/
theorem holPullbackVectorNoise_array_law (α γ : ℝ) (h : ℝ≥0) :
    Q.map (fun ω (k : ℕ) (j : Fin 4) ↦ holPullbackVectorNoise I hf α γ ((k : ℝ≥0) * h) h j ω) =
      (ULA.CanonicalBrownian.vectorProbability I).map
        (fun ω (k : ℕ) (j : Fin 4) ↦ holVectorNoise I α γ ((k : ℝ≥0) * h) h j ω) := by
  have he : ∀ᵐ ω ∂Q, ∀ k : ℕ, ∀ j : Fin 4,
      holPullbackVectorNoise I hf α γ ((k : ℝ≥0) * h) h j ω =
        holVectorNoise I α γ ((k : ℝ≥0) * h) h j (f ω) := by
    exact ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun j ↦ lpPullback_coe hf _
  have he' : (fun ω (k : ℕ) (j : Fin 4) ↦ holPullbackVectorNoise I hf α γ ((k : ℝ≥0) * h) h j ω) =ᵐ[Q]
      (fun ω (k : ℕ) (j : Fin 4) ↦ holVectorNoise I α γ ((k : ℝ≥0) * h) h j (f ω)) :=
    he.mono fun ω hω ↦ funext fun k ↦ funext (hω k)
  rw [Measure.map_congr he']
  have hm : Measurable (fun ω (k : ℕ) (j : Fin 4) ↦ holVectorNoise I α γ ((k : ℝ≥0) * h) h j ω) :=
    Measurable.of_eval fun k ↦ Measurable.of_eval fun j ↦ (Lp.stronglyMeasurable _).measurable
  have hmap := Measure.map_map (μ := Q) hm hf.measurable
  rw [hf.map_eq] at hmap
  exact hmap.symm

/-- The exact verified Gaussian coupling budget is unchanged by pullback. -/
theorem holPullbackVectorNoise_error_le (α γ : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (a h : ℝ≥0) (hh1 : (h : ℝ) ≤ 1) :
    ‖holPullbackVectorNoise I hf α γ a h 0‖ + ‖holPullbackVectorNoise I hf α γ a h 1‖ +
      ‖holPullbackVectorNoise I hf α γ a h 2 - holPullbackVectorNoise I hf α γ a h 3‖ ≤
      (Real.sqrt (Fintype.card I : ℝ) * holScalarNoiseConstant α γ) *
        (h : ℝ) * Real.sqrt (h : ℝ) := by
  unfold holPullbackVectorNoise
  rw [← map_sub, lpPullback_norm, lpPullback_norm, lpPullback_norm]
  exact holVectorNoise_error_le I α γ hα hγ a h hh1

/-- Three implementation innovations, jointly coupled to the fourth
Brownian reference innovation on the same actual sample. -/
def higherOrderPullbackGaussianNoise (α γ : ℝ) (h : ℝ≥0) (k : ℕ) :
    Lp (EuclideanSpace ℝ I) 2 Q × Lp (EuclideanSpace ℝ I) 2 Q × Lp (EuclideanSpace ℝ I) 2 Q :=
  (holPullbackVectorNoise I hf α γ ((k : ℝ≥0) * h) h 0,
   holPullbackVectorNoise I hf α γ ((k : ℝ≥0) * h) h 1,
   holPullbackVectorNoise I hf α γ ((k : ℝ≥0) * h) h 2)

def higherOrderPullbackGaussianIncrement (α γ : ℝ) (h : ℝ≥0) (k : ℕ) : Lp (EuclideanSpace ℝ I) 2 Q :=
  holPullbackVectorNoise I hf α γ ((k : ℝ≥0) * h) h 3

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
/-- The same explicit finite-horizon HOL rate holds on an actual random
initial-state/noise source, with no supplied Gaussian coupling-error budget. -/
theorem hol_mypgd_pullback_gaussian_finite_bound
    (Fbar : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Θ)
    (G : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Lp (EuclideanSpace ℝ I) 2 Q)
    (LF LG α γ Fθ FG U V C : ℝ) (h : ℝ≥0)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) (hFθ : 0 ≤ Fθ) (hFG : 0 ≤ FG)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hC : 0 ≤ C)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (r : ℕ → ℝ → HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) (n : ℕ)
    (hInt : ∀ k, k < n → IntervalIntegrable (fun t ↦ holDrift Fbar G α γ (r k t)) volume 0 h)
    (heq : ∀ k, k < n → r k h = r k 0 + (∫ t in 0..h, holDrift Fbar G α γ (r k t)) +
      holBrownianIncrement (higherOrderPullbackGaussianIncrement I hf α γ h k))
    (hcompat : ∀ k, k < n → r (k + 1) 0 = r k h)
    (hmod : ∀ k, k < n → ∀ t, t ∈ Icc 0 (h : ℝ) →
      ‖holDrift Fbar G α γ (r k t) - holDrift Fbar G α γ (r k 0)‖ ≤ C * Real.sqrt t)
    (hFbound : ∀ k, k < n → ‖Fbar (r k 0).1 (r k 0).2.1‖ ≤ Fθ)
    (hGbound : ∀ k, k < n →
      ‖G ((r k 0).1 - (h : ℝ) • Fbar (r k 0).1 (r k 0).2.1) (r k 0).2.1‖ ≤ FG)
    (hU : ∀ k, k < n → ‖(r k 0).2.2.1‖ ≤ U)
    (hV : ∀ k, k < n → ‖(r k 0).2.2.2‖ ≤ V)
    (z : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) :
    holError (trajectory (higherOrderStep Fbar G α γ h)
      (higherOrderPullbackGaussianNoise I hf α γ h) z n) (r n 0) ≤
      Real.exp (holStabilityConstant α γ LF LG * (h : ℝ) * n) *
        (holError z (r 0 0) +
          (holLocalConsistencyConstant (holRemainderConstants α γ) LG Fθ FG U V +
            Real.sqrt (Fintype.card I : ℝ) * holScalarNoiseConstant α γ +
            (8 / 3 : ℝ) * C) * (n * (h : ℝ)) * Real.sqrt (h : ℝ)) := by
  apply higherOrder_integral_reference_finite_sqrt_rate Fbar G LF LG α γ h Fθ FG U V C
    (Real.sqrt (Fintype.card I : ℝ) * holScalarNoiseConstant α γ)
    hα hγ hh hh1 hLF hLG hFθ hFG hU0 hV0 hC
    (by unfold holScalarNoiseConstant holRemainderConstants; positivity) hF hG
    r (higherOrderPullbackGaussianIncrement I hf α γ h) (higherOrderPullbackGaussianNoise I hf α γ h) n
    hInt heq hcompat hmod hFbound hGbound hU hV
  intro k _
  exact holPullbackVectorNoise_error_le I hf α γ hα hγ ((k : ℝ≥0) * h) h hh1

end PBGSO.Methods

namespace PBGSO
open Methods
section ParticleReference
variable {Ω A X : Type*} {N : ℕ} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  (I : Type*) [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  {f : Ω → ULA.CanonicalBrownian.VectorSample I}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability I))
  (D : ParticleForceData A X (EuclideanSpace ℝ I) N)

/-- Actual HOL implementation on the initial/noise source, with its original
empirical force lifts and actual pulled-back Gaussian innovations. -/
def higherOrderPullbackParticleIterate (α γ : ℝ) (h : ℝ≥0)
    (z : HOLState (Lp A 2 Q) (Lp (EuclideanSpace ℝ I) 2 Q)) (n : ℕ) :=
  trajectory (higherOrderStep (D.meanForceLp Q) (D.samplerForceLp Q) α γ h)
    (higherOrderPullbackGaussianNoise I hf α γ h) z n

/-- The actual HOL integral reference and finite-horizon regularity, now on
the same random initial/noise source as the constructed particle dynamics. -/
structure HigherOrderPullbackIntegralReference (α γ Fθ FG U V C : ℝ) (h : ℝ≥0) (n : ℕ) where
  auxiliary_friction_pos : 0 < α
  momentum_coupling_nonneg : 0 ≤ γ
  step_pos : 0 < (h : ℝ)
  step_le_one : (h : ℝ) ≤ 1
  optimizer_force_nonneg : 0 ≤ Fθ
  sampler_force_nonneg : 0 ≤ FG
  first_auxiliary_nonneg : 0 ≤ U
  second_auxiliary_nonneg : 0 ≤ V
  modulus_nonneg : 0 ≤ C
  r : ℕ → ℝ → HOLState (Lp A 2 Q) (Lp (EuclideanSpace ℝ I) 2 Q)
  drift_integrable : ∀ k, k < n → IntervalIntegrable
    (fun t ↦ holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (r k t)) volume 0 h
  equation : ∀ k, k < n → r k h = r k 0 +
    (∫ t in 0..h, holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (r k t)) +
    holBrownianIncrement (higherOrderPullbackGaussianIncrement I hf α γ h k)
  grid_compatible : ∀ k, k < n → r (k + 1) 0 = r k h
  drift_modulus : ∀ k, k < n → ∀ t, t ∈ Icc 0 (h : ℝ) →
    ‖holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (r k t) -
      holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ (r k 0)‖ ≤ C * Real.sqrt t
  optimizer_force_bound : ∀ k, k < n → ‖D.meanForceLp Q (r k 0).1 (r k 0).2.1‖ ≤ Fθ
  sampler_force_bound : ∀ k, k < n →
    ‖D.samplerForceLp Q ((r k 0).1 - (h : ℝ) • D.meanForceLp Q (r k 0).1 (r k 0).2.1)
      (r k 0).2.1‖ ≤ FG
  first_auxiliary_bound : ∀ k, k < n → ‖(r k 0).2.2.1‖ ≤ U
  second_auxiliary_bound : ∀ k, k < n → ‖(r k 0).2.2.2‖ ≤ V

/-- Concrete finite-particle HOL bound on the actual reference's sample
space, with all Gaussian noise constants derived by pullback. -/
theorem HigherOrderPullbackIntegralReference.finite_bound
    {α γ Fθ FG U V C : ℝ} {h : ℝ≥0} {n : ℕ}
    (Ref : HigherOrderPullbackIntegralReference I Q hf D α γ Fθ FG U V C h n)
    (z : HOLState (Lp A 2 Q) (Lp (EuclideanSpace ℝ I) 2 Q)) :
    holError (higherOrderPullbackParticleIterate I Q hf D α γ h z n) (Ref.r n 0) ≤
      higherOrderDiscretizationBudget I D α γ Fθ FG U V C h (holError z (Ref.r 0 0)) n := by
  exact hol_mypgd_pullback_gaussian_finite_bound I hf (D.meanForceLp Q) (D.samplerForceLp Q)
    D.meanLip D.samplerForceLip α γ Fθ FG U V C h
    Ref.auxiliary_friction_pos Ref.momentum_coupling_nonneg Ref.step_pos Ref.step_le_one
    D.meanLip.coe_nonneg D.samplerForceLip.coe_nonneg
    Ref.optimizer_force_nonneg Ref.sampler_force_nonneg Ref.first_auxiliary_nonneg
    Ref.second_auxiliary_nonneg Ref.modulus_nonneg (D.meanForceLp_bound Q) (D.samplerForceLp_bound Q)
    Ref.r n Ref.drift_integrable Ref.equation Ref.grid_compatible Ref.drift_modulus
    Ref.optimizer_force_bound Ref.sampler_force_bound Ref.first_auxiliary_bound Ref.second_auxiliary_bound z

end ParticleReference
end PBGSO
