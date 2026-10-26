import PBGSO.MomentumBrownian
import PBGSO.HOLNoiseRates

/-!
# Gaussian coordinate bounds for both proposed update maps

The innovations in this file are actual constructed Gaussian/Brownian inputs.
There is no unspecified noise-error premise in either final bound. Optimiser
and sampler forces remain independent maps on the displayed normed spaces.
For a stochastic optimiser, choose its parameter space as an L² space and
prove that these maps are the pointwise lifts of the intended raw forces.
That identification is not supplied by allowing arbitrary `Fbar` and `G`.
`particleMeanForce` and `particleSamplerForce` in MethodParticles define the
raw finite-particle forces; their pointwise L² identification remains separate.

The remaining assumptions are the original integral equations and explicit
reference moment/modulus bounds on the requested finite horizon. No statement
identifies the nonlinear sampler's target law or removes Moreau smoothing bias.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace PBGSO.Methods

/-- Lipschitz constant for the general non-potential coupled force in the
product max norm. -/
def coupledLipschitzConstant (LF LG : ℝ) : ℝ := 2 * max LF LG

variable {Θ X : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Separate force regularity suffices, without a joint potential. -/
theorem coupledForce_lipschitz (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (LF LG : ℝ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (z w : Θ × X) :
    ‖coupledForce Fbar G z - coupledForce Fbar G w‖ ≤
      coupledLipschitzConstant LF LG * ‖z - w‖ := by
  have hs : ‖z.1 - w.1‖ + ‖z.2 - w.2‖ ≤ 2 * ‖z - w‖ := by
    have h1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := norm_fst_le (z - w)
    have h2 : ‖z.2 - w.2‖ ≤ ‖z - w‖ := norm_snd_le (z - w)
    linarith
  change max _ _ ≤ _
  apply max_le
  · apply (hF _ _ _ _).trans
    calc
      _ ≤ LF * (2 * ‖z - w‖) := mul_le_mul_of_nonneg_left hs hLF
      _ ≤ (max LF LG) * (2 * ‖z - w‖) := by gcongr; exact le_max_left _ _
      _ = _ := by unfold coupledLipschitzConstant; ring
  · apply (hG _ _ _ _).trans
    calc
      _ ≤ LG * (2 * ‖z - w‖) := mul_le_mul_of_nonneg_left hs hLG
      _ ≤ (max LF LG) * (2 * ‖z - w‖) := by gcongr; exact le_max_right _ _
      _ = _ := by unfold coupledLipschitzConstant; ring

section MomentumGaussian
variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
variable [CompleteSpace Θ]

/-- Inject the actual sampler Gaussian innovations with optimiser coordinate
zero at both O stages. -/
def momentumGaussianNoise (h : ℝ) (k : ℕ) :
    (Θ × Lp (EuclideanSpace ℝ I) 2 Q) × (Θ × Lp (EuclideanSpace ℝ I) 2 Q) :=
  ((0, momentumHalfNoise Q W hW h (2 * k)),
    (0, momentumHalfNoise Q W hW h (2 * k + 1)))

/-- The reference's actual additive Brownian increment, coupled through the
two normalized half increments. -/
def momentumGaussianIncrement (γ h : ℝ) (k : ℕ) : Θ × Lp (EuclideanSpace ℝ I) 2 Q :=
  Real.sqrt (γ * h) • ((momentumGaussianNoise (Θ := Θ) Q W hW h k).1 +
    (momentumGaussianNoise (Θ := Θ) Q W hW h k).2)

/-- New explicit Gaussian-coordinate M-MFPO finite-horizon rate. The dimension factor
`sqrt(card I)` and all noise coupling constants are proved, not assumed.
The optimiser receives no Gaussian noise. Every reference hypothesis is
restricted to steps `k<n`. -/
theorem m_mfpo_gaussian_finite_bound
    (Fbar : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Θ)
    (G : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Lp (EuclideanSpace ℝ I) 2 Q)
    (LF LG γ h R P F : ℝ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) (hγ : 0 ≤ γ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hR : 0 ≤ R) (hP : 0 ≤ P) (hforce : 0 ≤ F)
    (hpaths : iIndepFun
      (fun i ω (j : ℕ) ↦ W i ((j : ℝ≥0) * (h / 2).toNNReal) ω) Q)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (p q : ℕ → ℝ → Θ × Lp (EuclideanSpace ℝ I) 2 Q) (n : ℕ)
    (hpInt : ∀ k, k < n → IntervalIntegrable (p k) volume 0 h)
    (hfInt : ∀ k, k < n → IntervalIntegrable
      (fun t ↦ coupledForce Fbar G (q k t) + γ • p k t) volume 0 h)
    (hp : ∀ k, k < n → p k h = p k 0 -
      (∫ t in 0..h, coupledForce Fbar G (q k t) + γ • p k t) +
      momentumGaussianIncrement (Θ := Θ) Q W hW γ h k)
    (hq : ∀ k, k < n → q k h = q k 0 + (∫ t in 0..h, p k t))
    (hcompat : ∀ k, k < n → p (k + 1) 0 = p k h ∧ q (k + 1) 0 = q k h)
    (hmod : ∀ k, k < n → ∀ t, t ∈ Set.Icc 0 h →
      ‖p k t - p k 0‖ ≤ R * Real.sqrt t ∧ ‖q k t - q k 0‖ ≤ R * Real.sqrt t)
    (hpbound : ∀ k, k < n → ‖p k 0‖ ≤ P)
    (hfbound : ∀ k, k < n → ‖coupledForce Fbar G (q k 0)‖ ≤ F)
    (z : (Θ × Lp (EuclideanSpace ℝ I) 2 Q) × (Θ × Lp (EuclideanSpace ℝ I) 2 Q)) :
    phaseError
      (trajectory (fun s r ↦ KineticLangevin.obaboStep (coupledForce Fbar G) h
        (Real.exp (-γ * h / 2)) (Real.sqrt (1 - Real.exp (-γ * h))) s r.1 r.2)
        (momentumGaussianNoise (Θ := Θ) Q W hW h) z n) (p n 0, q n 0) ≤
      Real.exp (momentumStabilityConstant (coupledLipschitzConstant LF LG) * h * n) *
        (phaseError z (p 0 0, q 0 0) +
          (momentumLocalConsistencyConstant (coupledLipschitzConstant LF LG) γ P F
              (Real.sqrt (Fintype.card I : ℝ)) +
            Real.sqrt γ * Real.sqrt (Fintype.card I : ℝ) +
            (3 / 2 : ℝ) * γ * Real.sqrt γ * Real.sqrt (Fintype.card I : ℝ) +
            (2 / 3 : ℝ) * (coupledLipschitzConstant LF LG + γ + 1) * R) *
              (n * h) * Real.sqrt h) := by
  have hGaussianLaw := momentumHalfNoise_pathLaw Q W hW h hh hpaths
  apply momentum_integral_reference_finite_sqrt_rate (coupledForce Fbar G)
    (coupledLipschitzConstant LF LG) γ h R P F (Real.sqrt (Fintype.card I : ℝ))
    (by unfold coupledLipschitzConstant; positivity) hγ hh hh1 hR hP hforce
    (Real.sqrt_nonneg _) (coupledForce_lipschitz Fbar G LF LG hLF hLG hF hG)
    p q (momentumGaussianIncrement (Θ := Θ) Q W hW γ h)
    (momentumGaussianNoise (Θ := Θ) Q W hW h) n hpInt hfInt hp hq hcompat hmod hpbound hfbound
  · intro k _
    constructor <;> dsimp [momentumGaussianNoise] <;>
      simp only [Prod.norm_def, sub_self, norm_zero, max_eq_right (norm_nonneg _)] <;>
      exact (momentumHalfNoise_norm Q W hW h hh _).le
  · intro _ _
    rfl

end MomentumGaussian

section HOLGaussian
variable (I : Type*) [Fintype I] [DecidableEq I] [CompleteSpace Θ]
abbrev HOLGaussianSpace :=
  Lp (EuclideanSpace ℝ I) 2 (ULA.CanonicalBrownian.vectorProbability I)

/-- The first three components of the actual correlated four-kernel Brownian
block; the fourth component is the coupled reference Brownian increment. -/
def higherOrderGaussianNoise (α γ : ℝ) (h : ℝ≥0) (k : ℕ) :
    HOLGaussianSpace I × HOLGaussianSpace I × HOLGaussianSpace I :=
  (holVectorNoise I α γ ((k : ℝ≥0) * h) h 0,
    holVectorNoise I α γ ((k : ℝ≥0) * h) h 1,
    holVectorNoise I α γ ((k : ℝ≥0) * h) h 2)

/-- The actual reference Brownian increment in the same four-kernel block. -/
def higherOrderGaussianIncrement (α γ : ℝ) (h : ℝ≥0) (k : ℕ) : HOLGaussianSpace I :=
  holVectorNoise I α γ ((k : ℝ≥0) * h) h 3

/-- New explicit Gaussian-coordinate HOL-MYPGD finite-horizon rate. The noise coefficient
is the verified canonical `sqrt(card I)*holScalarNoiseConstant`; there is no
unknown covariance, coupling remainder, or final numerical recurrence input. -/
theorem hol_mypgd_gaussian_finite_bound
    (Fbar : Θ → HOLGaussianSpace I → Θ) (G : Θ → HOLGaussianSpace I → HOLGaussianSpace I)
    (LF LG α γ Fθ FG U V C : ℝ) (h : ℝ≥0)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) (hFθ : 0 ≤ Fθ) (hFG : 0 ≤ FG)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hC : 0 ≤ C)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (r : ℕ → ℝ → HOLState Θ (HOLGaussianSpace I)) (n : ℕ)
    (hInt : ∀ k, k < n → IntervalIntegrable (fun t ↦ holDrift Fbar G α γ (r k t)) volume 0 h)
    (heq : ∀ k, k < n → r k h = r k 0 + (∫ t in 0..h, holDrift Fbar G α γ (r k t)) +
      holBrownianIncrement (higherOrderGaussianIncrement I α γ h k))
    (hcompat : ∀ k, k < n → r (k + 1) 0 = r k h)
    (hmod : ∀ k, k < n → ∀ t, t ∈ Set.Icc 0 (h : ℝ) →
      ‖holDrift Fbar G α γ (r k t) - holDrift Fbar G α γ (r k 0)‖ ≤ C * Real.sqrt t)
    (hFbound : ∀ k, k < n → ‖Fbar (r k 0).1 (r k 0).2.1‖ ≤ Fθ)
    (hGbound : ∀ k, k < n →
      ‖G ((r k 0).1 - (h : ℝ) • Fbar (r k 0).1 (r k 0).2.1) (r k 0).2.1‖ ≤ FG)
    (hU : ∀ k, k < n → ‖(r k 0).2.2.1‖ ≤ U)
    (hV : ∀ k, k < n → ‖(r k 0).2.2.2‖ ≤ V)
    (z : HOLState Θ (HOLGaussianSpace I)) :
    holError (trajectory (higherOrderStep Fbar G α γ h)
      (higherOrderGaussianNoise I α γ h) z n) (r n 0) ≤
      Real.exp (holStabilityConstant α γ LF LG * (h : ℝ) * n) *
        (holError z (r 0 0) +
          (holLocalConsistencyConstant (holRemainderConstants α γ) LG Fθ FG U V +
            Real.sqrt (Fintype.card I : ℝ) * holScalarNoiseConstant α γ +
            (8 / 3 : ℝ) * C) * (n * (h : ℝ)) * Real.sqrt (h : ℝ)) := by
  apply higherOrder_integral_reference_finite_sqrt_rate Fbar G LF LG α γ h Fθ FG U V C
    (Real.sqrt (Fintype.card I : ℝ) * holScalarNoiseConstant α γ)
    hα hγ hh hh1 hLF hLG hFθ hFG hU0 hV0 hC
    (by unfold holScalarNoiseConstant holRemainderConstants; positivity) hF hG
    r (higherOrderGaussianIncrement I α γ h) (higherOrderGaussianNoise I α γ h) n
    hInt heq hcompat hmod hFbound hGbound hU hV
  intro k _
  exact holVectorNoise_error_le I α γ hα hγ ((k : ℝ≥0) * h) h hh1

end HOLGaussian
end PBGSO.Methods
