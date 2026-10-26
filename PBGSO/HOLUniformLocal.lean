import PBGSO.HOLPullback

/-! # State-dependent local errors for the actual printed HOL implementation

Only global joint Lipschitz bounds on the two independent forces are used.
The parameter-first force correction is bounded absolutely; no false
`O(h²)` Lipschitz bound on a four-point force difference is assumed.
These local estimates are suitable for exact-flow contraction and absorption.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO.Methods

variable {Θ X : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [NormedSpace ℝ Θ] [CompleteSpace Θ] [NormedSpace ℝ X] [CompleteSpace X] in
/-- Global joint regularity gives linear force growth in the full raw phase
norm. The constants are obtained by comparison with the actual force at zero. -/
theorem hol_force_linear_growth
    (Fbar : Θ → X → Θ) (G : Θ → X → X) (LF LG : ℝ)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (z : HOLState Θ X) :
    ‖Fbar z.1 z.2.1‖ ≤ (‖Fbar 0 0‖ + 2 * LF) * (1 + ‖z‖) ∧
    ‖G z.1 z.2.1‖ ≤ (‖G 0 0‖ + 2 * LG) * (1 + ‖z‖) := by
  have hθ : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have hx : ‖z.2.1‖ ≤ ‖z‖ := (norm_fst_le z.2).trans (norm_snd_le z)
  have hf := norm_le_norm_add_norm_sub (Fbar 0 0) (Fbar z.1 z.2.1)
  rw [norm_sub_rev] at hf
  have hg := norm_le_norm_add_norm_sub (G 0 0) (G z.1 z.2.1)
  rw [norm_sub_rev] at hg
  have hf' := hF z.1 0 z.2.1 0
  have hg' := hG z.1 0 z.2.1 0
  simp only [sub_zero] at hf' hg'
  constructor
  · have ht := mul_le_mul_of_nonneg_left hθ hLF
    have hx := mul_le_mul_of_nonneg_left hx hLF
    nlinarith [mul_nonneg (norm_nonneg (Fbar 0 0)) (norm_nonneg z)]
  · have ht := mul_le_mul_of_nonneg_left hθ hLG
    have hx := mul_le_mul_of_nonneg_left hx hLG
    nlinarith [mul_nonneg (norm_nonneg (G 0 0)) (norm_nonneg z)]

/-- Explicit coefficient for the deterministic local error's linear growth. -/
def holLocalGrowthConstant (α γ LF LG f₀ g₀ : ℝ) : ℝ :=
  holLocalConsistencyConstant (holRemainderConstants α γ) LG
    (f₀ + 2 * LF) (g₀ + 2 * LG + LG * (f₀ + 2 * LF)) 1 1

/-- Actual printed HOL against Euler has a local defect growing at most
linearly in its initial state. No numerical Lipschitz contraction is a premise. -/
theorem higherOrder_euler_linear_growth_error
    (Fbar : Θ → X → Θ) (G : Θ → X → X) (LF LG α γ h : ℝ)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (z : HOLState Θ X) (ξ : X × X × X) (b : X) :
    holError (higherOrderStep Fbar G α γ h z ξ) (holEuler Fbar G α γ h z b) ≤
      holLocalGrowthConstant α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ *
        (1 + ‖z‖) * h ^ 2 + ‖ξ.1‖ + ‖ξ.2.1‖ + ‖ξ.2.2 - b‖ := by
  let A := ‖Fbar 0 0‖ + 2 * LF
  let B := ‖G 0 0‖ + 2 * LG + LG * A
  let R := 1 + ‖z‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hgθ : ∀ θ θ' x, ‖G θ x - G θ' x‖ ≤ LG * ‖θ - θ'‖ := by
    intro θ θ' x
    simpa only [sub_self, norm_zero, add_zero] using hG θ θ' x x
  obtain ⟨hf, hg⟩ := hol_force_linear_growth Fbar G LF LG hLF hLG hF hG z
  have hshift : ‖G (z.1 - h • Fbar z.1 z.2.1) z.2.1‖ ≤ B * R := by
    have hb := higherOrder_shifted_force_bound Fbar G LG h (A * R)
      ((‖G 0 0‖ + 2 * LG) * R) hLG (by simpa [abs_of_pos hh] using hh1)
      hgθ z.1 z.2.1 hf hg
    convert hb using 1
    dsimp [B, R]
    ring
  have hu : ‖z.2.2.1‖ ≤ R := by
    have hp := (norm_fst_le z.2.2).trans ((norm_snd_le z.2).trans (norm_snd_le z))
    dsimp [R]; linarith
  have hv : ‖z.2.2.2‖ ≤ R := by
    have hp := (norm_snd_le z.2.2).trans ((norm_snd_le z.2).trans (norm_snd_le z))
    dsimp [R]; linarith
  have he := higherOrder_euler_error Fbar G LG α γ h (A * R) (B * R) R R
    hLG hgθ z ξ b hf hshift hu hv
  have hb := holDeterministicBudget_quadratic α γ h LG (A * R) (B * R) R R
    hα hγ hh hh1 (mul_nonneg hB hR) hR hR
  have hid : holLocalConsistencyConstant (holRemainderConstants α γ) LG
      (A * R) (B * R) R R =
      holLocalGrowthConstant α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ * R := by
    dsimp [holLocalConsistencyConstant, holLocalGrowthConstant, A, B]; ring
  rw [hid] at hb
  dsimp only [holRemainderBudget, holDeterministicBudget] at he hb
  dsimp only [R] at hb
  linarith

/-- Nonnegativity of the explicit growth coefficient under physical parameter
and primitive Lipschitz assumptions. -/
theorem holLocalGrowthConstant_nonneg (α γ LF LG f₀ g₀ : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hf₀ : 0 ≤ f₀) (hg₀ : 0 ≤ g₀) :
    0 ≤ holLocalGrowthConstant α γ LF LG f₀ g₀ := by
  dsimp [holLocalGrowthConstant, holLocalConsistencyConstant, holRemainderConstants]
  positivity

/-- Direct local comparison with an actual integral trajectory. The sole
trajectory modulus is a drift regularity hypothesis to be derived from its
primitive equation, never a final numerical-error or contraction assumption. -/
theorem higherOrder_integral_linear_growth_error
    (Fbar : Θ → X → Θ) (G : Θ → X → X) (LF LG α γ h C : ℝ)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (r : ℝ → HOLState Θ X) (ξ : X × X × X) (b : X)
    (hInt : IntervalIntegrable (fun t ↦ holDrift Fbar G α γ (r t)) volume 0 h)
    (heq : r h = r 0 + (∫ t in 0..h, holDrift Fbar G α γ (r t)) + holBrownianIncrement b)
    (hmod : ∀ t ∈ Icc 0 h,
      ‖holDrift Fbar G α γ (r t) - holDrift Fbar G α γ (r 0)‖ ≤ C * Real.sqrt t) :
    holError (higherOrderStep Fbar G α γ h (r 0) ξ) (r h) ≤
      holLocalGrowthConstant α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ *
        (1 + ‖r 0‖) * h ^ 2 + ‖ξ.1‖ + ‖ξ.2.1‖ + ‖ξ.2.2 - b‖ +
        (8 / 3 : ℝ) * C * h * Real.sqrt h := by
  have he := higherOrder_euler_linear_growth_error Fbar G LF LG α γ h
    hLF hLG hα hγ hh hh1 hF hG (r 0) ξ b
  have hi := holEuler_integral_error Fbar G α γ h C hh.le r b hInt heq hmod
  have ht := holError_triangle (higherOrderStep Fbar G α γ h (r 0) ξ)
    (holEuler Fbar G α γ h (r 0) b) (r h)
  linarith

/-- A concrete global Lipschitz constant for the raw phase drift. -/
def holDriftGlobalLip (LF LG α γ : ℝ) : ℝ≥0 :=
  (4 * (LF + LG + 1 + 2 * |γ| + |α|)).toNNReal

/-- The restart Picard hypotheses follow directly from the primitive forces. -/
theorem holDrift_globally_lipschitz
    (Fbar : Θ → X → Θ) (G : Θ → X → X) (LF LG α γ : ℝ)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖)) :
    LipschitzWith (holDriftGlobalLip LF LG α γ) (holDrift Fbar G α γ) := by
  have hD : 0 ≤ LF + LG + 1 + 2 * |γ| + |α| := by positivity
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  calc
    _ ≤ (LF + LG + 1 + 2 * |γ| + |α|) * holError z w :=
      holDrift_error Fbar G LF LG α γ hLF hLG hF hG z w
    _ ≤ (LF + LG + 1 + 2 * |γ| + |α|) * (4 * ‖z - w‖) :=
      mul_le_mul_of_nonneg_left (holError_le_four_norm z w) hD
    _ = (holDriftGlobalLip LF LG α γ : ℝ) * ‖z - w‖ := by
      rw [holDriftGlobalLip, Real.coe_toNNReal _ (by positivity)]
      ring

end PBGSO.Methods

namespace PBGSO.Methods
section GaussianLocal
variable {Ω I Θ : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  {f : Ω → ULA.CanonicalBrownian.VectorSample I}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability I))

/-- Actual Gaussian local consistency for arbitrary L² random initial states.
The dimension factor and all printed-coefficient noise errors are derived.
Only a primitive integral solution's drift modulus remains to be instantiated
by the generic Lipschitz integral regularity theorem. -/
theorem higherOrder_pullback_integral_local_error
    (Fbar : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Θ)
    (G : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Lp (EuclideanSpace ℝ I) 2 Q)
    (LF LG α γ C : ℝ) (a h : ℝ≥0)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (r : ℝ → HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q))
    (hInt : IntervalIntegrable (fun t ↦ holDrift Fbar G α γ (r t)) volume 0 h)
    (heq : r h = r 0 + (∫ t in 0..h, holDrift Fbar G α γ (r t)) +
      holBrownianIncrement (holPullbackVectorNoise I hf α γ a h 3))
    (hmod : ∀ t ∈ Icc 0 (h : ℝ),
      ‖holDrift Fbar G α γ (r t) - holDrift Fbar G α γ (r 0)‖ ≤ C * Real.sqrt t) :
    holError (higherOrderStep Fbar G α γ h (r 0)
        (holPullbackVectorNoise I hf α γ a h 0,
         holPullbackVectorNoise I hf α γ a h 1,
         holPullbackVectorNoise I hf α γ a h 2)) (r h) ≤
      (holLocalGrowthConstant α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ * (1 + ‖r 0‖) +
        Real.sqrt (Fintype.card I : ℝ) * holScalarNoiseConstant α γ + (8 / 3 : ℝ) * C) *
          (h : ℝ) * Real.sqrt (h : ℝ) := by
  have he := higherOrder_integral_linear_growth_error Fbar G LF LG α γ h C
    hLF hLG hα hγ hh hh1 hF hG r
    (holPullbackVectorNoise I hf α γ a h 0,
     holPullbackVectorNoise I hf α γ a h 1,
     holPullbackVectorNoise I hf α γ a h 2)
    (holPullbackVectorNoise I hf α γ a h 3) hInt heq hmod
  have hn := holPullbackVectorNoise_error_le I hf α γ hα hγ a h hh1
  have hc := holLocalGrowthConstant_nonneg α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖
    hα hγ hLF hLG (norm_nonneg _) (norm_nonneg _)
  have hs : (h : ℝ) ≤ Real.sqrt (h : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith [h.coe_nonneg])
  have hp : (h : ℝ) ^ 2 ≤ (h : ℝ) * Real.sqrt (h : ℝ) := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left hs h.coe_nonneg
  have hb := mul_le_mul_of_nonneg_left hp
    (mul_nonneg hc (by positivity : 0 ≤ 1 + ‖r 0‖))
  dsimp only [Prod.fst, Prod.snd] at he
  nlinarith

end GaussianLocal
end PBGSO.Methods
