import PBGSO.HOLRestartLocal
import PBGSO.UniformDiscrete

/-! # Time-uniform strong error for the actual printed HOL scheme

The actual Gaussian update is compared with constructed exact Picard restarts.
Primitive weighted dissipativity contracts those restarts. Explicit local
errors grow linearly in the numerical input radius, which is absorbed under
an explicit small-step restriction. Uniform reference moments are derived
from the original integral equation. Numerical contractivity, local errors,
reference moments and final recurrences are not assumptions.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO.Methods

/-- The proved uniform exact-flow radius, expressed using primitive data. -/
def holUniformReferenceRadius
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : E → E) (L : ℝ≥0) (C : E →L[ℝ] H) (ρ Ξ : ℝ) (z : E) : ℝ :=
  let S := ‖C‖ * PBGSO.UniformIntegral.radius L ‖f 0‖ Ξ 0
  ‖C z‖ + S / (1 - Real.exp (-ρ)) + S

variable {Ω I Θ H : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  {f : Ω → ULA.CanonicalBrownian.VectorSample I}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability I))
  (Fbar : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Θ)
  (G : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Lp (EuclideanSpace ℝ I) 2 Q)
  (LF LG α γ : ℝ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
  (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
  (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))

include hLF hLG hF hG in
/-- Comprehensive time-uniform error against an actual continuous integral
trajectory, for every iteration. The only stability hypothesis is primitive
weighted dissipativity of the original drift; in the particle application it
is derived from source A3. The reference moment radius is a conclusion. -/
theorem higherOrder_time_uniform_of_integral
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (C : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q) →L[ℝ] H)
    (m ρ : ℝ) (hm : 0 < m) (hρ : 0 < ρ)
    (hcoerc : ∀ x, m * ‖x‖ ≤ ‖C x‖)
    (hmono : ∀ x y,
      inner ℝ (C (x - y)) (C (holDrift Fbar G α γ x - holDrift Fbar G α γ y)) ≤
        -ρ * ‖C (x - y)‖ ^ 2)
    (Y : ℝ → HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) (hY : Continuous Y)
    (heq : ∀ t, 0 ≤ t → Y t - Y 0 =
      (∫ s in 0..t, holDrift Fbar G α γ (Y s)) + higherOrderRestartInput Q hf α 0 t)
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (hρh : ρ * (h : ℝ) ≤ 1)
    (hsmall : (‖C‖ * holUniformLocalConstant1 α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ / m) *
      Real.sqrt (h : ℝ) ≤ ρ / 4) (n : ℕ) :
    let c₀ := holUniformLocalConstant0 I α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ ‖holDrift Fbar G α γ 0‖
    let c₁ := holUniformLocalConstant1 α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖
    let R := holUniformReferenceRadius (holDrift Fbar G α γ) (holDriftGlobalLip LF LG α γ)
      C ρ (holUniformNoiseRadius I α) (Y 0)
    ‖trajectory (higherOrderStep Fbar G α γ h)
        (higherOrderPullbackGaussianNoise I hf α γ h) (Y 0) n - Y ((n : ℝ) * (h : ℝ))‖ ≤
      ((4 * (‖C‖ * c₀ + (‖C‖ * c₁ / m) * R) / ρ) * Real.sqrt (h : ℝ)) / m := by
  let c₀ := holUniformLocalConstant0 I α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ ‖holDrift Fbar G α γ 0‖
  let c₁ := holUniformLocalConstant1 α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖
  let L := holDriftGlobalLip LF LG α γ
  let Ξ := holUniformNoiseRadius I α
  let R := holUniformReferenceRadius (holDrift Fbar G α γ) L C ρ Ξ (Y 0)
  let X := trajectory (higherOrderStep Fbar G α γ h)
    (higherOrderPullbackGaussianNoise I hf α γ h) (Y 0)
  let Z := fun k : ℕ ↦ Y ((k : ℝ) * (h : ℝ))
  let A := fun (k : ℕ) x ↦ higherOrderStep Fbar G α γ h x
    (higherOrderPullbackGaussianNoise I hf α γ h k)
  let Φ := fun (k : ℕ) x ↦ higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG x
    ((k : ℝ) * (h : ℝ)) h
  have hLip := holDrift_globally_lipschitz Fbar G LF LG α γ hLF hLG hF hG
  obtain ⟨hc₀, hc₁⟩ := holUniformLocalConstants_nonneg I α γ LF LG
    ‖Fbar 0 0‖ ‖G 0 0‖ ‖holDrift Fbar G α γ 0‖ hα hγ hLF hLG
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have hreference (k : ℕ) : ‖C (Z k)‖ ≤ R := by
    apply PBGSO.UniformIntegral.uniform_moment (holDrift Fbar G α γ) L hLip C ρ hρ hmono
      Y (higherOrderRestartInput Q hf α 0) hY
      (higherOrderRestartInput_continuous Q hf α 0) heq Ξ
      (by dsimp [Ξ, holUniformNoiseRadius]; positivity) ?_ ((k : ℝ) * (h : ℝ)) (by positivity)
    intro a s ha hs
    rw [higherOrderRestartInput_increment]
    exact higherOrderRestartInput_bound Q hf α a s ha hs.1
  have hR : 0 ≤ R := (norm_nonneg _).trans (hreference 0)
  have hX : ∀ k, X (k + 1) = A k (X k) := fun _ ↦ rfl
  have hZ : ∀ k, Z (k + 1) = Φ k (Z k) := by
    intro k
    have he := higherOrderRestart_agrees Q hf Fbar G LF LG α γ hLF hLG hF hG
      Y hY heq ((k : ℝ) * (h : ℝ)) h (by positivity) h.coe_nonneg
    dsimp only [Z, Φ]
    rw [show ((k + 1 : ℕ) : ℝ) * (h : ℝ) = (k : ℝ) * (h : ℝ) + (h : ℝ) by push_cast; ring]
    exact he.symm
  have hcontract : ∀ k x y, ‖C (Φ k x - Φ k y)‖ ≤
      Real.exp (-ρ * (h : ℝ)) * ‖C (x - y)‖ := by
    intro k x y
    exact higherOrderRestart_contracts Q hf Fbar G LF LG α γ hLF hLG hF hG
      ((k : ℝ) * (h : ℝ)) C ρ hmono x y h h.coe_nonneg
  have hdefect : ∀ k x, ‖C (A k x - Φ k x)‖ ≤
      ((h : ℝ) * Real.sqrt (h : ℝ)) * (‖C‖ * c₀ + (‖C‖ * c₁ / m) * ‖C x‖) := by
    intro k x
    have he := higherOrderRestart_local_error Q hf Fbar G LF LG α γ hLF hLG hF hG
      hα hγ ((k : ℝ≥0) * h) h hh hh1 x
    have hx : ‖x‖ ≤ ‖C x‖ / m := (le_div_iff₀ hm).mpr (by simpa [mul_comm] using hcoerc x)
    have hn : ‖A k x - Φ k x‖ ≤ (c₀ + c₁ * ‖x‖) * (h : ℝ) * Real.sqrt (h : ℝ) := by
      apply (norm_sub_le_holError _ _).trans
      convert he using 1
      simp only [A, Φ, higherOrderPullbackGaussianNoise, NNReal.coe_mul, NNReal.coe_natCast]
    calc
      _ ≤ ‖C‖ * ‖A k x - Φ k x‖ := C.le_opNorm _
      _ ≤ ‖C‖ * ((c₀ + c₁ * ‖x‖) * (h : ℝ) * Real.sqrt (h : ℝ)) :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
      _ ≤ ‖C‖ * ((c₀ + c₁ * (‖C x‖ / m)) * (h : ℝ) * Real.sqrt (h : ℝ)) := by
        gcongr
      _ = _ := by ring
  have hi : X 0 = Z 0 := by simp [X, Z, trajectory]
  exact PBGSO.UniformDiscrete.one_step_same_initial_uniform_norm C A Φ X Z
    ρ h (‖C‖ * c₀) (‖C‖ * c₁ / m) R m hρ hh
    (mul_nonneg (norm_nonneg _) hc₀) (by positivity) hR hm hcoerc hρh hsmall
    hX hZ hcontract hdefect hreference hi n

/-- Fully constructed exact-reference version of the uniform HOL theorem.
The reference process is the actual Picard solution on the same Brownian
source, so no compatible process or output-law identity is a premise. -/
theorem higherOrder_time_uniform
    (hα : 0 < α) (hγ : 0 ≤ γ)
    (C : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q) →L[ℝ] H)
    (m ρ : ℝ) (hm : 0 < m) (hρ : 0 < ρ)
    (hcoerc : ∀ x, m * ‖x‖ ≤ ‖C x‖)
    (hmono : ∀ x y,
      inner ℝ (C (x - y)) (C (holDrift Fbar G α γ x - holDrift Fbar G α γ y)) ≤
        -ρ * ‖C (x - y)‖ ^ 2)
    (z : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q))
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (hρh : ρ * (h : ℝ) ≤ 1)
    (hsmall : (‖C‖ * holUniformLocalConstant1 α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ / m) *
      Real.sqrt (h : ℝ) ≤ ρ / 4) (n : ℕ) :
    let c₀ := holUniformLocalConstant0 I α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ ‖holDrift Fbar G α γ 0‖
    let c₁ := holUniformLocalConstant1 α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖
    let R := holUniformReferenceRadius (holDrift Fbar G α γ) (holDriftGlobalLip LF LG α γ)
      C ρ (holUniformNoiseRadius I α) z
    ‖trajectory (higherOrderStep Fbar G α γ h)
        (higherOrderPullbackGaussianNoise I hf α γ h) z n -
      higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z 0 ((n : ℝ) * (h : ℝ))‖ ≤
      ((4 * (‖C‖ * c₀ + (‖C‖ * c₁ / m) * R) / ρ) * Real.sqrt (h : ℝ)) / m := by
  let Y := higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z 0
  have hY := higherOrderRestart_continuous Q hf Fbar G LF LG α γ hLF hLG hF hG z 0
  have heq : ∀ t, 0 ≤ t → Y t - Y 0 =
      (∫ s in 0..t, holDrift Fbar G α γ (Y s)) + higherOrderRestartInput Q hf α 0 t := by
    intro t ht
    rw [show Y 0 = z from higherOrderRestart_zero Q hf Fbar G LF LG α γ hLF hLG hF hG z 0]
    exact higherOrderRestart_equation Q hf Fbar G LF LG α γ hLF hLG hF hG z 0 t ht
  have he := higherOrder_time_uniform_of_integral Q hf Fbar G LF LG α γ hLF hLG hF hG
    hα hγ C m ρ hm hρ hcoerc hmono Y hY heq h hh hh1 hρh hsmall n
  simpa only [Y, higherOrderRestart_zero] using he

end PBGSO.Methods
