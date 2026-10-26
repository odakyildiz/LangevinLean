import PBGSO.HigherOrderMethod
import PBGSO.MomentumConsistency

/-!
# HOL-MYPGD versus its actual continuous higher-order integral equations

The error bound keeps the exact paper coefficients, the sequential parameter
update, and the mismatch between its correlated Gaussian triple and the
reference Brownian increment visible. No target-law or covariance identity is
assumed implicitly. A finite-horizon result follows from the map stability and
this derived local consistency estimate.
-/
noncomputable section
open MeasureTheory
namespace PBGSO.Methods
variable {Θ X : Type*}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The actual higher-order particle vector field, before discretisation. -/
def holDrift (Fbar : Θ → X → Θ) (G : Θ → X → X) (α γ : ℝ)
    (z : HOLState Θ X) : HOLState Θ X :=
  (-Fbar z.1 z.2.1, z.2.2.1,
    -G z.1 z.2.1 + γ • z.2.2.2, -γ • z.2.2.1 - α • z.2.2.2)

/-- Diffusion acts solely on the final auxiliary variable `v`. -/
def holBrownianIncrement (b : X) : HOLState Θ X := (0, 0, 0, b)

/-- Euler comparison, used only to connect the implemented map to the
continuous integral equation; this is not substituted for the implementation. -/
def holEuler (Fbar : Θ → X → Θ) (G : Θ → X → X) (α γ h : ℝ)
    (z : HOLState Θ X) (b : X) : HOLState Θ X :=
  z + h • holDrift Fbar G α γ z + holBrownianIncrement b

private theorem norm_four_hol (a b c d : X) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc
    _ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
    _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_add_le _ _

/-- The completely explicit local consistency budget. Scalar coefficient
errors are kept as exact expressions, so no small-step asymptotics or hidden
constants are required. -/
def holRemainderBudget (μ : HOLCoefficients) (α γ h LG Fθ FG U V : ℝ)
    (ξ : X × X × X) (b : X) : ℝ :=
  (h ^ 2 / 2 + |μ.μ31 * h|) * FG +
    (|μ.μ12 - h| + |μ.μ22 - 1| + |μ.μ32 + γ * h|) * U +
    (|μ.μ13| + |μ.μ23 - γ * h| + |μ.μ33 - 1 + α * h|) * V +
    h ^ 2 * LG * Fθ + ‖ξ.1‖ + ‖ξ.2.1‖ + ‖ξ.2.2 - b‖

/-- New local consistency bound for the actual sequential HOL-MYPGD map.
The term `h² LG Fθ` is the parameter/sampler Lie--Trotter splitting error. -/
theorem higherOrder_euler_error (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (LG α γ h Fθ FG U V : ℝ) (hLG : 0 ≤ LG)
    (hG : ∀ θ θ' x, ‖G θ x - G θ' x‖ ≤ LG * ‖θ - θ'‖)
    (z : HOLState Θ X) (ξ : X × X × X) (b : X)
    (hF : ‖Fbar z.1 z.2.1‖ ≤ Fθ)
    (hforce : ‖G (z.1 - h • Fbar z.1 z.2.1) z.2.1‖ ≤ FG)
    (hu : ‖z.2.2.1‖ ≤ U) (hv : ‖z.2.2.2‖ ≤ V) :
    holError (higherOrderStep Fbar G α γ h z ξ) (holEuler Fbar G α γ h z b) ≤
      holRemainderBudget (holCoefficients α γ h) α γ h LG Fθ FG U V ξ b := by
  let μ := holCoefficients α γ h
  let θ := z.1 - h • Fbar z.1 z.2.1
  let g := G θ z.2.1
  have hforce' : ‖g‖ ≤ FG := hforce
  have hdiff : ‖h • (G z.1 z.2.1 - g)‖ ≤ h ^ 2 * LG * Fθ := by
    have ht : ‖z.1 - θ‖ ≤ |h| * Fθ := by
      have he : z.1 - θ = h • Fbar z.1 z.2.1 := by dsimp [θ]; module
      rw [he, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hF (abs_nonneg h)
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |h| * (LG * ‖z.1 - θ‖) := by gcongr; exact hG _ _ _
      _ ≤ |h| * (LG * (|h| * Fθ)) := by gcongr
      _ = _ := by rw [show |h| * (LG * (|h| * Fθ)) = |h| ^ 2 * LG * Fθ by ring, sq_abs]
  have hx : ‖-(h ^ 2 / 2) • g + (μ.μ12 - h) • z.2.2.1 + μ.μ13 • z.2.2.2 + ξ.1‖ ≤
      h ^ 2 / 2 * FG + |μ.μ12 - h| * U + |μ.μ13| * V + ‖ξ.1‖ := by
    apply (norm_four_hol _ _ _ _).trans
    simp only [norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / 2)]
    gcongr
  have hu' : ‖h • (G z.1 z.2.1 - g) + (μ.μ22 - 1) • z.2.2.1 +
      (μ.μ23 - γ * h) • z.2.2.2 + ξ.2.1‖ ≤
      h ^ 2 * LG * Fθ + |μ.μ22 - 1| * U + |μ.μ23 - γ * h| * V + ‖ξ.2.1‖ := by
    apply (norm_four_hol _ _ _ _).trans
    simp only [norm_smul, Real.norm_eq_abs] at *
    gcongr
  have hv' : ‖(μ.μ31 * h) • g + (μ.μ32 + γ * h) • z.2.2.1 +
      (μ.μ33 - 1 + α * h) • z.2.2.2 + (ξ.2.2 - b)‖ ≤
      |μ.μ31 * h| * FG + |μ.μ32 + γ * h| * U +
      |μ.μ33 - 1 + α * h| * V + ‖ξ.2.2 - b‖ := by
    apply (norm_four_hol _ _ _ _).trans
    simp only [norm_smul, Real.norm_eq_abs]
    gcongr
  have hθeq : (higherOrderStep Fbar G α γ h z ξ).1 -
      (holEuler Fbar G α γ h z b).1 = 0 := by
    dsimp [higherOrderStep, holQuadratureStep, holResponse, holEuler, holDrift, holBrownianIncrement]
    module
  have hxeq : (higherOrderStep Fbar G α γ h z ξ).2.1 -
      (holEuler Fbar G α γ h z b).2.1 =
      -(h ^ 2 / 2) • g + (μ.μ12 - h) • z.2.2.1 + μ.μ13 • z.2.2.2 + ξ.1 := by
    dsimp [higherOrderStep, holQuadratureStep, holResponse, holEuler, holDrift,
      holBrownianIncrement, g, θ, μ]
    module
  have hueq : (higherOrderStep Fbar G α γ h z ξ).2.2.1 -
      (holEuler Fbar G α γ h z b).2.2.1 =
      h • (G z.1 z.2.1 - g) + (μ.μ22 - 1) • z.2.2.1 +
        (μ.μ23 - γ * h) • z.2.2.2 + ξ.2.1 := by
    dsimp [higherOrderStep, holQuadratureStep, holResponse, holEuler, holDrift,
      holBrownianIncrement, g, θ, μ]
    module
  have hveq : (higherOrderStep Fbar G α γ h z ξ).2.2.2 -
      (holEuler Fbar G α γ h z b).2.2.2 =
      (μ.μ31 * h) • g + (μ.μ32 + γ * h) • z.2.2.1 +
        (μ.μ33 - 1 + α * h) • z.2.2.2 + (ξ.2.2 - b) := by
    dsimp [higherOrderStep, holQuadratureStep, holResponse, holEuler, holDrift,
      holBrownianIncrement, g, θ, μ]
    module
  unfold holError
  rw [hθeq, hxeq, hueq, hveq, norm_zero, zero_add]
  dsimp [holRemainderBudget, μ] at *
  nlinarith

/-- Sum norm versus the product Banach norm. -/
theorem holError_le_four_norm (z w : HOLState Θ X) : holError z w ≤ 4 * ‖z - w‖ := by
  have h1 : ‖z.1 - w.1‖ ≤ ‖z - w‖ := norm_fst_le (z - w)
  have h2 : ‖z.2.1 - w.2.1‖ ≤ ‖z - w‖ := (norm_fst_le (z.2 - w.2)).trans (norm_snd_le (z - w))
  have h3 : ‖z.2.2.1 - w.2.2.1‖ ≤ ‖z - w‖ :=
    (norm_fst_le (z.2.2 - w.2.2)).trans ((norm_snd_le (z.2 - w.2)).trans (norm_snd_le (z - w)))
  have h4 : ‖z.2.2.2 - w.2.2.2‖ ≤ ‖z - w‖ :=
    (norm_snd_le (z.2.2 - w.2.2)).trans ((norm_snd_le (z.2 - w.2)).trans (norm_snd_le (z - w)))
  unfold holError
  linarith

/-- The product Banach norm is bounded by the coordinate sum used by the
numerical estimates. -/
theorem norm_sub_le_holError (z w : HOLState Θ X) : ‖z - w‖ ≤ holError z w := by
  change max ‖z.1 - w.1‖ (max ‖z.2.1 - w.2.1‖
    (max ‖z.2.2.1 - w.2.2.1‖ ‖z.2.2.2 - w.2.2.2‖)) ≤ _
  unfold holError
  have h1 := norm_nonneg (z.1 - w.1)
  have h2 := norm_nonneg (z.2.1 - w.2.1)
  have h3 := norm_nonneg (z.2.2.1 - w.2.2.1)
  have h4 := norm_nonneg (z.2.2.2 - w.2.2.2)
  exact max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (by linarith)))

/-- Original force regularity controls the full higher-order drift. Combined
with an integral-solution increment estimate, this discharges its temporal
modulus hypothesis without assuming a numerical-error inequality. -/
theorem holDrift_error (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (LF LG α γ : ℝ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (z w : HOLState Θ X) :
    ‖holDrift Fbar G α γ z - holDrift Fbar G α γ w‖ ≤
      (LF + LG + 1 + 2 * |γ| + |α|) * holError z w := by
  let e := holError z w
  have hab : ‖z.1 - w.1‖ + ‖z.2.1 - w.2.1‖ ≤ e := by
    dsimp [e, holError]
    nlinarith [norm_nonneg (z.2.2.1 - w.2.2.1), norm_nonneg (z.2.2.2 - w.2.2.2)]
  have hu : ‖z.2.2.1 - w.2.2.1‖ ≤ e := by
    dsimp [e, holError]
    nlinarith [norm_nonneg (z.1 - w.1), norm_nonneg (z.2.1 - w.2.1), norm_nonneg (z.2.2.2 - w.2.2.2)]
  have hv : ‖z.2.2.2 - w.2.2.2‖ ≤ e := by
    dsimp [e, holError]
    nlinarith [norm_nonneg (z.1 - w.1), norm_nonneg (z.2.1 - w.2.1), norm_nonneg (z.2.2.1 - w.2.2.1)]
  have hsampler : ‖(-G z.1 z.2.1 + γ • z.2.2.2) - (-G w.1 w.2.1 + γ • w.2.2.2)‖ ≤
      ‖G z.1 z.2.1 - G w.1 w.2.1‖ + |γ| * ‖z.2.2.2 - w.2.2.2‖ := by
    have he : (-G z.1 z.2.1 + γ • z.2.2.2) - (-G w.1 w.2.1 + γ • w.2.2.2) =
        -(G z.1 z.2.1 - G w.1 w.2.1) + γ • (z.2.2.2 - w.2.2.2) := by module
    rw [he]
    simpa only [norm_neg, norm_smul, Real.norm_eq_abs] using norm_add_le
      (-(G z.1 z.2.1 - G w.1 w.2.1)) (γ • (z.2.2.2 - w.2.2.2))
  have haux : ‖(-γ • z.2.2.1 - α • z.2.2.2) - (-γ • w.2.2.1 - α • w.2.2.2)‖ ≤
      |γ| * ‖z.2.2.1 - w.2.2.1‖ + |α| * ‖z.2.2.2 - w.2.2.2‖ := by
    have he : (-γ • z.2.2.1 - α • z.2.2.2) - (-γ • w.2.2.1 - α • w.2.2.2) =
        (-γ) • (z.2.2.1 - w.2.2.1) - α • (z.2.2.2 - w.2.2.2) := by module
    rw [he]
    simpa only [norm_smul, Real.norm_eq_abs, abs_neg] using norm_sub_le
      ((-γ) • (z.2.2.1 - w.2.2.1)) (α • (z.2.2.2 - w.2.2.2))
  calc
    _ ≤ holError (holDrift Fbar G α γ z) (holDrift Fbar G α γ w) := norm_sub_le_holError _ _
    _ ≤ (LF + LG) * (‖z.1 - w.1‖ + ‖z.2.1 - w.2.1‖) +
        (1 + |γ|) * ‖z.2.2.1 - w.2.2.1‖ +
        (|γ| + |α|) * ‖z.2.2.2 - w.2.2.2‖ := by
      dsimp [holError, holDrift]
      simp only [neg_sub_neg, norm_sub_rev]
      have hf := hF z.1 w.1 z.2.1 w.2.1
      have hg := hG z.1 w.1 z.2.1 w.2.1
      nlinarith
    _ ≤ (LF + LG) * e + (1 + |γ|) * e + (|γ| + |α|) * e := by gcongr
    _ = _ := by dsimp [e]; ring

/-- Bounding the original sampler force and the optimiser force bounds the
sampler force at the sequentially updated parameter. -/
theorem higherOrder_shifted_force_bound (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (LG h Fθ FG : ℝ) (hLG : 0 ≤ LG) (hh : |h| ≤ 1)
    (hG : ∀ θ θ' x, ‖G θ x - G θ' x‖ ≤ LG * ‖θ - θ'‖)
    (θ : Θ) (x : X) (hF : ‖Fbar θ x‖ ≤ Fθ) (hforce : ‖G θ x‖ ≤ FG) :
    ‖G (θ - h • Fbar θ x) x‖ ≤ FG + LG * Fθ := by
  have hn : ‖G (θ - h • Fbar θ x) x‖ ≤
      ‖G θ x‖ + ‖G (θ - h • Fbar θ x) x - G θ x‖ := by
    have he : G (θ - h • Fbar θ x) x = G θ x + (G (θ - h • Fbar θ x) x - G θ x) := by module
    conv_lhs => rw [he]
    exact norm_add_le _ _
  have hg := hG (θ - h • Fbar θ x) θ x
  have he : (θ - h • Fbar θ x) - θ = -(h • Fbar θ x) := by module
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs] at hg
  have hnorm : |h| * ‖Fbar θ x‖ ≤ Fθ := by
    have hp := norm_nonneg (Fbar θ x)
    calc
      _ ≤ 1 * ‖Fbar θ x‖ := mul_le_mul_of_nonneg_right hh hp
      _ ≤ Fθ := by simpa using hF
  have hb := mul_le_mul_of_nonneg_left hnorm hLG
  linarith

/-- The reference Euler defect is derived from its Banach-valued integral
equation and a square-root drift modulus, not from a numerical recurrence. -/
theorem holEuler_integral_error (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (α γ h C : ℝ) (hh : 0 ≤ h) (r : ℝ → HOLState Θ X) (b : X)
    (hInt : IntervalIntegrable (fun t ↦ holDrift Fbar G α γ (r t)) volume 0 h)
    (heq : r h = r 0 + (∫ t in 0..h, holDrift Fbar G α γ (r t)) + holBrownianIncrement b)
    (hmod : ∀ t ∈ Set.Icc 0 h,
      ‖holDrift Fbar G α γ (r t) - holDrift Fbar G α γ (r 0)‖ ≤ C * Real.sqrt t) :
    holError (holEuler Fbar G α γ h (r 0) b) (r h) ≤
      (8 / 3 : ℝ) * C * h * Real.sqrt h := by
  have hd := integral_deviation_sqrt (fun t ↦ holDrift Fbar G α γ (r t)) C h hh hmod
  have he : holEuler Fbar G α γ h (r 0) b - r h =
      -(∫ t in 0..h, holDrift Fbar G α γ (r t) - holDrift Fbar G α γ (r 0)) := by
    rw [intervalIntegral.integral_sub hInt intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero]
    rw [heq]
    dsimp [holEuler]
    module
  have hb := holError_le_four_norm (holEuler Fbar G α γ h (r 0) b) (r h)
  rw [he, norm_neg] at hb
  linarith

/-- The deterministic portion of the explicit HOL Euler remainder. -/
def holDeterministicBudget (μ : HOLCoefficients) (α γ h LG Fθ FG U V : ℝ) : ℝ :=
  (h ^ 2 / 2 + |μ.μ31 * h|) * FG +
    (|μ.μ12 - h| + |μ.μ22 - 1| + |μ.μ32 + γ * h|) * U +
    (|μ.μ13| + |μ.μ23 - γ * h| + |μ.μ33 - 1 + α * h|) * V +
    h ^ 2 * LG * Fθ

/-- New finite-horizon discretisation bound for the actual HOL-MYPGD
implementation against compatible solutions of its higher-order integral
system. All assumptions are on the original forces, reference solution, or
innovations; a numerical error recurrence is a derived conclusion.

The explicit coefficient budget does not assert a convergence order by itself.
The bounds `Fθ,FG,U,V,C,B` must be established on the intended time horizon.
For an L² application the ambient Banach spaces and supplied Gaussian/Brownian
coupling must implement the actual stochastic system. -/
theorem higherOrder_integral_reference_bound
    (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (LF LG α γ h Fθ FG U V C B : ℝ) (hh : 0 ≤ h) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (r : ℕ → ℝ → HOLState Θ X) (b : ℕ → X) (ξ : ℕ → X × X × X)
    (hInt : ∀ k, IntervalIntegrable (fun t ↦ holDrift Fbar G α γ (r k t)) volume 0 h)
    (heq : ∀ k, r k h = r k 0 + (∫ t in 0..h, holDrift Fbar G α γ (r k t)) +
      holBrownianIncrement (b k))
    (hcompat : ∀ k, r (k + 1) 0 = r k h)
    (hmod : ∀ k t, t ∈ Set.Icc 0 h →
      ‖holDrift Fbar G α γ (r k t) - holDrift Fbar G α γ (r k 0)‖ ≤ C * Real.sqrt t)
    (hFbound : ∀ k, ‖Fbar (r k 0).1 (r k 0).2.1‖ ≤ Fθ)
    (hGbound : ∀ k,
      ‖G ((r k 0).1 - h • Fbar (r k 0).1 (r k 0).2.1) (r k 0).2.1‖ ≤ FG)
    (hU : ∀ k, ‖(r k 0).2.2.1‖ ≤ U) (hV : ∀ k, ‖(r k 0).2.2.2‖ ≤ V)
    (hnoise : ∀ k, ‖(ξ k).1‖ + ‖(ξ k).2.1‖ + ‖(ξ k).2.2 - b k‖ ≤ B)
    (z : HOLState Θ X) (n : ℕ) :
    holError (trajectory (higherOrderStep Fbar G α γ h) ξ z n) (r n 0) ≤
      holAmplification (holCoefficients α γ h) LF LG h ^ n * holError z (r 0 0) +
        (holDeterministicBudget (holCoefficients α γ h) α γ h LG Fθ FG U V + B +
          (8 / 3 : ℝ) * C * h * Real.sqrt h) *
          amplificationSum (holAmplification (holCoefficients α γ h) LF LG h) n := by
  have hA : 0 ≤ holAmplification (holCoefficients α γ h) LF LG h := by
    unfold holAmplification
    positivity
  apply finite_accumulation _ _ _ hA _ n
  intro k
  dsimp only [trajectory]
  rw [hcompat k]
  let a := trajectory (higherOrderStep Fbar G α γ h) ξ z k
  have hs := higherOrder_error Fbar G LF LG α γ h hLF hLG hF hG a (r k 0) (ξ k) (ξ k)
  simp only [holNoiseError, sub_self, norm_zero, add_zero] at hs
  have hgθ : ∀ θ θ' x, ‖G θ x - G θ' x‖ ≤ LG * ‖θ - θ'‖ := by
    intro θ θ' x
    simpa only [sub_self, norm_zero, add_zero] using hG θ θ' x x
  have hl := higherOrder_euler_error Fbar G LG α γ h Fθ FG U V hLG hgθ
    (r k 0) (ξ k) (b k) (hFbound k) (hGbound k) (hU k) (hV k)
  have hbudget : holRemainderBudget (holCoefficients α γ h) α γ h LG Fθ FG U V (ξ k) (b k) ≤
      holDeterministicBudget (holCoefficients α γ h) α γ h LG Fθ FG U V + B := by
    unfold holRemainderBudget holDeterministicBudget
    linarith [hnoise k]
  have he := holEuler_integral_error Fbar G α γ h C hh (r k) (b k) (hInt k) (heq k) (hmod k)
  have ht1 := holError_triangle (higherOrderStep Fbar G α γ h a (ξ k))
    (higherOrderStep Fbar G α γ h (r k 0) (ξ k)) (r k h)
  have ht2 := holError_triangle (higherOrderStep Fbar G α γ h (r k 0) (ξ k))
    (holEuler Fbar G α γ h (r k 0) (b k)) (r k h)
  linarith

/-- Finite-horizon version: every reference, moment, and innovation premise
is required only for the first `n` steps. -/
theorem higherOrder_integral_reference_finite_bound
    (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (LF LG α γ h Fθ FG U V C B : ℝ) (hh : 0 ≤ h) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hF : ∀ θ θ' x x', ‖Fbar θ x - Fbar θ' x'‖ ≤ LF * (‖θ - θ'‖ + ‖x - x'‖))
    (hG : ∀ θ θ' x x', ‖G θ x - G θ' x'‖ ≤ LG * (‖θ - θ'‖ + ‖x - x'‖))
    (r : ℕ → ℝ → HOLState Θ X) (b : ℕ → X) (ξ : ℕ → X × X × X) (n : ℕ)
    (hInt : ∀ k, k < n → IntervalIntegrable (fun t ↦ holDrift Fbar G α γ (r k t)) volume 0 h)
    (heq : ∀ k, k < n → r k h = r k 0 + (∫ t in 0..h, holDrift Fbar G α γ (r k t)) +
      holBrownianIncrement (b k))
    (hcompat : ∀ k, k < n → r (k + 1) 0 = r k h)
    (hmod : ∀ k, k < n → ∀ t, t ∈ Set.Icc 0 h →
      ‖holDrift Fbar G α γ (r k t) - holDrift Fbar G α γ (r k 0)‖ ≤ C * Real.sqrt t)
    (hFbound : ∀ k, k < n → ‖Fbar (r k 0).1 (r k 0).2.1‖ ≤ Fθ)
    (hGbound : ∀ k, k < n →
      ‖G ((r k 0).1 - h • Fbar (r k 0).1 (r k 0).2.1) (r k 0).2.1‖ ≤ FG)
    (hU : ∀ k, k < n → ‖(r k 0).2.2.1‖ ≤ U) (hV : ∀ k, k < n → ‖(r k 0).2.2.2‖ ≤ V)
    (hnoise : ∀ k, k < n → ‖(ξ k).1‖ + ‖(ξ k).2.1‖ + ‖(ξ k).2.2 - b k‖ ≤ B)
    (z : HOLState Θ X) :
    holError (trajectory (higherOrderStep Fbar G α γ h) ξ z n) (r n 0) ≤
      holAmplification (holCoefficients α γ h) LF LG h ^ n * holError z (r 0 0) +
        (holDeterministicBudget (holCoefficients α γ h) α γ h LG Fθ FG U V + B +
          (8 / 3 : ℝ) * C * h * Real.sqrt h) *
          amplificationSum (holAmplification (holCoefficients α γ h) LF LG h) n := by
  have hA : 0 ≤ holAmplification (holCoefficients α γ h) LF LG h := by
    unfold holAmplification
    positivity
  apply finite_accumulation_upto _ _ _ hA n
  intro k hk
  dsimp only [trajectory]
  rw [hcompat k hk]
  let a := trajectory (higherOrderStep Fbar G α γ h) ξ z k
  have hs := higherOrder_error Fbar G LF LG α γ h hLF hLG hF hG a (r k 0) (ξ k) (ξ k)
  simp only [holNoiseError, sub_self, norm_zero, add_zero] at hs
  have hgθ : ∀ θ θ' x, ‖G θ x - G θ' x‖ ≤ LG * ‖θ - θ'‖ := by
    intro θ θ' x
    simpa only [sub_self, norm_zero, add_zero] using hG θ θ' x x
  have hl := higherOrder_euler_error Fbar G LG α γ h Fθ FG U V hLG hgθ
    (r k 0) (ξ k) (b k) (hFbound k hk) (hGbound k hk) (hU k hk) (hV k hk)
  have hbudget : holRemainderBudget (holCoefficients α γ h) α γ h LG Fθ FG U V (ξ k) (b k) ≤
      holDeterministicBudget (holCoefficients α γ h) α γ h LG Fθ FG U V + B := by
    unfold holRemainderBudget holDeterministicBudget
    linarith [hnoise k hk]
  have he := holEuler_integral_error Fbar G α γ h C hh (r k) (b k) (hInt k hk) (heq k hk) (hmod k hk)
  have ht1 := holError_triangle (higherOrderStep Fbar G α γ h a (ξ k))
    (higherOrderStep Fbar G α γ h (r k 0) (ξ k)) (r k h)
  have ht2 := holError_triangle (higherOrderStep Fbar G α γ h (r k 0) (ξ k))
    (holEuler Fbar G α γ h (r k 0) (b k)) (r k h)
  linarith

end PBGSO.Methods
