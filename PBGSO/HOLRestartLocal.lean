import PBGSO.HOLRestart
import PBGSO.UniformIntegralMoments

/-! # Explicit restarted HOL local error from primitive assumptions

The original integral equation, global force regularity and actual Brownian
increment moments derive every radius and temporal modulus used here.
The resulting error is affine in the arbitrary random initial state's norm.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO.Methods

/-- Actual final-auxiliary Brownian increment radius. -/
def holUniformNoiseRadius (I : Type*) [Fintype I] (α : ℝ) : ℝ :=
  Real.sqrt α * Real.sqrt (2 * (Fintype.card I : ℝ))

/-- State-independent part of the actual HOL local error coefficient. -/
def holUniformLocalConstant0 (I : Type*) [Fintype I]
    (α γ LF LG fzero gzero bzero : ℝ) : ℝ :=
  let L : ℝ := holDriftGlobalLip LF LG α γ
  let Ξ := holUniformNoiseRadius I α
  holLocalGrowthConstant α γ LF LG fzero gzero +
    Real.sqrt (Fintype.card I : ℝ) * holScalarNoiseConstant α γ +
    (8 / 3 : ℝ) * L * (bzero + L * Real.exp (L + 1) * (bzero + Ξ) + Ξ)

/-- Linear initial-state part of the actual HOL local error coefficient. -/
def holUniformLocalConstant1 (α γ LF LG fzero gzero : ℝ) : ℝ :=
  let L : ℝ := holDriftGlobalLip LF LG α γ
  holLocalGrowthConstant α γ LF LG fzero gzero +
    (8 / 3 : ℝ) * L ^ 2 * Real.exp (L + 1)

theorem holUniformLocalConstants_nonneg (I : Type*) [Fintype I]
    (α γ LF LG fzero gzero bzero : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hfzero : 0 ≤ fzero) (hgzero : 0 ≤ gzero) (hbzero : 0 ≤ bzero) :
    0 ≤ holUniformLocalConstant0 I α γ LF LG fzero gzero bzero ∧
    0 ≤ holUniformLocalConstant1 α γ LF LG fzero gzero := by
  have hc := holLocalGrowthConstant_nonneg α γ LF LG fzero gzero hα hγ hLF hLG hfzero hgzero
  have hn : 0 ≤ holScalarNoiseConstant α γ := by
    dsimp [holScalarNoiseConstant, holRemainderConstants]; positivity
  constructor <;>
    dsimp [holUniformLocalConstant0, holUniformLocalConstant1, holUniformNoiseRadius] <;> positivity

variable {Ω I Θ : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  {f : Ω → ULA.CanonicalBrownian.VectorSample I}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability I))
  (Fbar : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Θ)
  (G : Θ → Lp (EuclideanSpace ℝ I) 2 Q → Lp (EuclideanSpace ℝ I) 2 Q)
  (LF LG α γ : ℝ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
  (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
  (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))

/-- Genuine `h sqrt(h)` strong local consistency of the printed correlated
Gaussian update and its constructed exact restart. No reference, moment,
modulus, local-error, or numerical-contractivity premise is supplied. -/
theorem higherOrderRestart_local_error
    (hα : 0 < α) (hγ : 0 ≤ γ) (a h : ℝ≥0)
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    (z : HOLState Θ (Lp (EuclideanSpace ℝ I) 2 Q)) :
    holError (higherOrderStep Fbar G α γ h z
        (holPullbackVectorNoise I hf α γ a h 0,
         holPullbackVectorNoise I hf α γ a h 1,
         holPullbackVectorNoise I hf α γ a h 2))
      (higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a h) ≤
      (holUniformLocalConstant0 I α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖
          ‖holDrift Fbar G α γ 0‖ +
        holUniformLocalConstant1 α γ LF LG ‖Fbar 0 0‖ ‖G 0 0‖ * ‖z‖) *
          (h : ℝ) * Real.sqrt (h : ℝ) := by
  let r := higherOrderRestart Q hf Fbar G LF LG α γ hLF hLG hF hG z a
  let B := higherOrderRestartInput (Θ := Θ) Q hf α a
  let L := holDriftGlobalLip LF LG α γ
  let Ξ := holUniformNoiseRadius I α
  let P := PBGSO.UniformIntegral.radius L ‖holDrift Fbar G α γ 0‖ Ξ ‖z‖
  let M := ‖holDrift Fbar G α γ 0‖ + (L : ℝ) * P + Ξ
  have hr : Continuous r := higherOrderRestart_continuous Q hf Fbar G LF LG α γ hLF hLG hF hG z a
  have hB : Continuous B := higherOrderRestartInput_continuous Q hf α a
  have hr0 : r 0 = z := higherOrderRestart_zero Q hf Fbar G LF LG α γ hLF hLG hF hG z a
  have hLip := holDrift_globally_lipschitz Fbar G LF LG α γ hLF hLG hF hG
  have heq : ∀ t ∈ Icc 0 (h : ℝ), r t - r 0 =
      (∫ s in 0..t, holDrift Fbar G α γ (r s)) + B t := by
    intro t ht
    rw [hr0]
    exact higherOrderRestart_equation Q hf Fbar G LF LG α γ hLF hLG hF hG z a t ht.1
  have hinput : ∀ t ∈ Icc 0 (h : ℝ), ‖B t‖ ≤ Ξ * Real.sqrt t := by
    intro t ht
    exact higherOrderRestartInput_bound Q hf α a t a.coe_nonneg ht.1
  have hreg := PBGSO.UniformIntegral.local_regularity (holDrift Fbar G α γ) L hLip
    r B hr hB h Ξ h.coe_nonneg hh1 (by dsimp [Ξ, holUniformNoiseRadius]; positivity) heq hinput
  have hmod : ∀ t ∈ Icc 0 (h : ℝ),
      ‖holDrift Fbar G α γ (r t) - holDrift Fbar G α γ (r 0)‖ ≤
        ((L : ℝ) * M) * Real.sqrt t := by
    intro t ht
    have hi := (hreg t ht).2.2
    rw [hr0] at hi
    calc
      _ ≤ (L : ℝ) * ‖r t - r 0‖ := hLip.norm_sub_le _ _
      _ ≤ (L : ℝ) * (M * Real.sqrt t) := by
        apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
        simpa only [hr0, M, P] using hi
      _ = _ := by ring
  have hend : r h = r 0 + (∫ t in 0..h, holDrift Fbar G α γ (r t)) +
      holBrownianIncrement (holPullbackVectorNoise I hf α γ a h 3) := by
    have he := heq h ⟨h.coe_nonneg, le_rfl⟩
    dsimp only [B] at he
    rw [higherOrderRestartInput_endpoint Q hf α γ hα.le a h] at he
    rw [sub_eq_iff_eq_add] at he
    rw [he]
    abel
  have he := higherOrder_pullback_integral_local_error Q hf Fbar G LF LG α γ
    ((L : ℝ) * M) a h hLF hLG hα hγ hh hh1 hF hG r
    ((hLip.continuous.comp hr).intervalIntegrable _ _) hend hmod
  rw [hr0] at he
  apply he.trans_eq
  congr 1
  dsimp [holUniformLocalConstant0, holUniformLocalConstant1, M, P,
    PBGSO.UniformIntegral.radius, L, Ξ]
  ring

end PBGSO.Methods
