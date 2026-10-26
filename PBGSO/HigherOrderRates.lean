import PBGSO.HigherOrderConsistency
import KineticLangevin.Recurrence

/-! # Explicit small-step consistency constants for HOL-MYPGD
These estimates use only the elementary exponential remainder and the exact
seven implementation coefficients. In particular the paper's affine response
is not misidentified with the exponential of the complete linear subsystem.
-/
noncomputable section
namespace PBGSO.Methods

/-- Explicit constants controlling all seven coefficient remainders for
`0<h≤1`, `α>0`, and `γ≥0`. The `μ31` slot bounds `|μ31*h|`. -/
def holRemainderConstants (α γ : ℝ) : HOLCoefficients where
  μ12 := γ ^ 2 / (2 * α)
  μ13 := γ / 2
  μ22 := γ ^ 2 / 2
  μ23 := γ * α / 2
  μ31 := γ / 2
  μ32 := γ ^ 3 / α +
    (γ ^ 3 / α ^ 2 + 2 * γ ^ 3 / α ^ 3 + γ / α) * α ^ 2 / 2
  μ33 := γ ^ 2 + (1 + γ ^ 2 / α + γ ^ 2 / α ^ 2) * α ^ 2 / 2

/-- All needed implementation coefficient estimates, including the
cancellation of the first-order terms. -/
structure HOLCoefficientBounds (μ c : HOLCoefficients) (α γ h : ℝ) : Prop where
  bound12 : |μ.μ12 - h| ≤ c.μ12 * h ^ 2
  bound13 : |μ.μ13| ≤ c.μ13 * h ^ 2
  bound22 : |μ.μ22 - 1| ≤ c.μ22 * h ^ 2
  bound23 : |μ.μ23 - γ * h| ≤ c.μ23 * h ^ 2
  bound31 : |μ.μ31 * h| ≤ c.μ31 * h ^ 2
  bound31' : |μ.μ31| ≤ c.μ31 * h
  bound32 : |μ.μ32 + γ * h| ≤ c.μ32 * h ^ 2
  bound33 : |μ.μ33 - 1 + α * h| ≤ c.μ33 * h ^ 2

/-- New verified `O(h²)` coefficient remainder bounds. -/
theorem holCoefficient_bounds (α γ h : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    HOLCoefficientBounds (holCoefficients α γ h) (holRemainderConstants α γ) α γ h := by
  let r := Real.exp (-α * h) - 1 + α * h
  have hr : 0 ≤ r := by
    have he := Real.add_one_le_exp (-α * h)
    dsimp [r]
    linarith
  have hr' : r ≤ α ^ 2 * h ^ 2 / 2 := by
    have he := KineticLangevin.exp_neg_le_quadratic (α * h) (by positivity)
    rw [← neg_mul] at he
    dsimp [r]
    nlinarith
  have he : Real.exp (-α * h) = 1 - α * h + r := by dsimp [r]; ring
  have e12 : (holCoefficients α γ h).μ12 - h =
      -(γ ^ 2 / (2 * α) * h ^ 2) + (γ ^ 2 / α ^ 3) * r := by
    dsimp [holCoefficients]; rw [he]; field_simp; ring
  have e13 : (holCoefficients α γ h).μ13 = γ / α ^ 2 * r := by
    dsimp [holCoefficients]; rw [he]; field_simp; ring
  have e22 : (holCoefficients α γ h).μ22 - 1 = -(γ ^ 2 / α ^ 2 * r) := by
    dsimp [holCoefficients]; rw [he]; field_simp; ring
  have e23 : (holCoefficients α γ h).μ23 - γ * h = -(γ / α * r) := by
    dsimp [holCoefficients]; rw [he]; field_simp; ring
  have e31 : (holCoefficients α γ h).μ31 * h = γ / α ^ 2 * r := by
    dsimp [holCoefficients]; rw [he]; field_simp; ring
  have e32 : (holCoefficients α γ h).μ32 + γ * h =
      -(γ ^ 3 / α * h ^ 2) +
        (γ ^ 3 / α ^ 2 * h + 2 * γ ^ 3 / α ^ 3 + γ / α) * r := by
    dsimp [holCoefficients]; rw [he]; field_simp; ring
  have e33 : (holCoefficients α γ h).μ33 - 1 + α * h =
      -(γ ^ 2 * h ^ 2) + (1 + γ ^ 2 / α * h + γ ^ 2 / α ^ 2) * r := by
    dsimp [holCoefficients]; rw [he]; field_simp; ring
  have b12 : (γ ^ 2 / α ^ 3) * r ≤ γ ^ 2 / (2 * α) * h ^ 2 := by
    convert mul_le_mul_of_nonneg_left hr' (by positivity : 0 ≤ γ ^ 2 / α ^ 3) using 1 <;>
      field_simp <;> ring
  have b13 : (γ / α ^ 2) * r ≤ γ / 2 * h ^ 2 := by
    convert mul_le_mul_of_nonneg_left hr' (by positivity : 0 ≤ γ / α ^ 2) using 1 <;>
      field_simp <;> ring
  have b22 : (γ ^ 2 / α ^ 2) * r ≤ γ ^ 2 / 2 * h ^ 2 := by
    convert mul_le_mul_of_nonneg_left hr' (by positivity : 0 ≤ γ ^ 2 / α ^ 2) using 1 <;>
      field_simp <;> ring
  have b23 : (γ / α) * r ≤ γ * α / 2 * h ^ 2 := by
    convert mul_le_mul_of_nonneg_left hr' (by positivity : 0 ≤ γ / α) using 1 <;>
      field_simp <;> ring
  have b32 : (γ ^ 3 / α ^ 2 * h + 2 * γ ^ 3 / α ^ 3 + γ / α) * r ≤
      (γ ^ 3 / α ^ 2 + 2 * γ ^ 3 / α ^ 3 + γ / α) * (α ^ 2 * h ^ 2 / 2) := by
    apply mul_le_mul _ hr' hr (by positivity)
    have hb : γ ^ 3 / α ^ 2 * h ≤ γ ^ 3 / α ^ 2 := by
      simpa using mul_le_mul_of_nonneg_left hh1 (by positivity : 0 ≤ γ ^ 3 / α ^ 2)
    linarith only [hb]
  have b33 : (1 + γ ^ 2 / α * h + γ ^ 2 / α ^ 2) * r ≤
      (1 + γ ^ 2 / α + γ ^ 2 / α ^ 2) * (α ^ 2 * h ^ 2 / 2) := by
    apply mul_le_mul _ hr' hr (by positivity)
    have hb : γ ^ 2 / α * h ≤ γ ^ 2 / α := by
      simpa using mul_le_mul_of_nonneg_left hh1 (by positivity : 0 ≤ γ ^ 2 / α)
    linarith only [hb]
  have b31 : |(holCoefficients α γ h).μ31 * h| ≤ γ / 2 * h ^ 2 := by
    rw [e31, abs_of_nonneg (by positivity)]
    exact b13
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e12]; dsimp [holRemainderConstants]
    apply abs_le.mpr
    constructor
    · have hn : 0 ≤ γ ^ 2 / α ^ 3 * r := by positivity
      linarith
    · have hn : 0 ≤ γ ^ 2 / (2 * α) * h ^ 2 := by positivity
      linarith
  · rw [e13, abs_of_nonneg (by positivity)]
    exact b13
  · rw [e22, abs_neg, abs_of_nonneg (by positivity)]
    exact b22
  · rw [e23, abs_neg, abs_of_nonneg (by positivity)]
    exact b23
  · exact b31
  · dsimp [holRemainderConstants]
    rw [abs_mul, abs_of_pos hh] at b31
    exact (mul_le_mul_iff_left₀ hh).mp (by convert b31 using 1 <;> ring)
  · rw [e32]
    dsimp [holRemainderConstants]
    apply abs_le.mpr
    constructor
    · have hn : 0 ≤ (γ ^ 3 / α ^ 2 * h + 2 * γ ^ 3 / α ^ 3 + γ / α) * r := by positivity
      have hc : 0 ≤ (γ ^ 3 / α ^ 2 + 2 * γ ^ 3 / α ^ 3 + γ / α) * α ^ 2 / 2 * h ^ 2 := by positivity
      nlinarith only [hn, hc]
    · have hn : 0 ≤ γ ^ 3 / α * h ^ 2 := by positivity
      nlinarith only [b32, hn]
  · rw [e33]
    dsimp [holRemainderConstants]
    apply abs_le.mpr
    constructor
    · have hn : 0 ≤ (1 + γ ^ 2 / α * h + γ ^ 2 / α ^ 2) * r := by positivity
      have hc : 0 ≤ (1 + γ ^ 2 / α + γ ^ 2 / α ^ 2) * α ^ 2 / 2 * h ^ 2 := by positivity
      nlinarith only [hn, hc]
    · have hn : 0 ≤ γ ^ 2 * h ^ 2 := by positivity
      nlinarith only [b33, hn]

/-- Explicit coefficient of the deterministic `h²` local consistency budget. -/
def holLocalConsistencyConstant (c : HOLCoefficients) (LG Fθ FG U V : ℝ) : ℝ :=
  (1 / 2 + c.μ31) * FG + (c.μ12 + c.μ22 + c.μ32) * U +
    (c.μ13 + c.μ23 + c.μ33) * V + LG * Fθ

/-- The preceding cancellation estimates give a genuine quadratic local
consistency bound for the exact implementation coefficients. -/
theorem holDeterministicBudget_quadratic
    (α γ h LG Fθ FG U V : ℝ) (hα : 0 < α) (hγ : 0 ≤ γ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hFG : 0 ≤ FG) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    holDeterministicBudget (holCoefficients α γ h) α γ h LG Fθ FG U V ≤
      holLocalConsistencyConstant (holRemainderConstants α γ) LG Fθ FG U V * h ^ 2 := by
  have hc := holCoefficient_bounds α γ h hα hγ hh hh1
  unfold holDeterministicBudget
  calc
    _ ≤ (h ^ 2 / 2 + (holRemainderConstants α γ).μ31 * h ^ 2) * FG +
        ((holRemainderConstants α γ).μ12 * h ^ 2 +
          (holRemainderConstants α γ).μ22 * h ^ 2 +
          (holRemainderConstants α γ).μ32 * h ^ 2) * U +
        ((holRemainderConstants α γ).μ13 * h ^ 2 +
          (holRemainderConstants α γ).μ23 * h ^ 2 +
          (holRemainderConstants α γ).μ33 * h ^ 2) * V + h ^ 2 * LG * Fθ := by
      gcongr
      exact hc.bound31
      exact hc.bound12
      exact hc.bound22
      exact hc.bound32
      exact hc.bound13
      exact hc.bound23
      exact hc.bound33
    _ = _ := by unfold holLocalConsistencyConstant; ring

/-- Explicit stability exponent for the higher-order implementation. -/
def holStabilityConstant (α γ LF LG : ℝ) : ℝ :=
  let c := holRemainderConstants α γ
  max (LF + ((3 + γ) / 2) * LG * (1 + LF))
    (max (1 + γ + c.μ12 + c.μ22 + c.μ32) (γ + α + c.μ13 + c.μ23 + c.μ33))

private theorem abs_le_remainder_add (x y c : ℝ) (hb : |x - y| ≤ c) : |x| ≤ c + |y| := by
  calc
    |x| = |(x - y) + y| := by congr 1; ring
    _ ≤ |x - y| + |y| := abs_add_le _ _
    _ ≤ _ := by gcongr

/-- The sharp-column stability coefficient is `1+O(h)`, with a fully explicit
constant, rather than a per-step constant bounded away from one. -/
theorem holAmplification_linear_bound (α γ LF LG h : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    holAmplification (holCoefficients α γ h) LF LG h ≤
      1 + holStabilityConstant α γ LF LG * h := by
  let μ := holCoefficients α γ h
  let c := holRemainderConstants α γ
  let K := holStabilityConstant α γ LF LG
  have hc := holCoefficient_bounds α γ h hα hγ hh hh1
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have h12 := abs_le_remainder_add μ.μ12 h (c.μ12 * h ^ 2) hc.bound12
  have h22 := abs_le_remainder_add μ.μ22 1 (c.μ22 * h ^ 2) hc.bound22
  have h32 := abs_le_remainder_add μ.μ32 (-γ * h) (c.μ32 * h ^ 2) (by
    simpa only [sub_neg_eq_add, neg_mul] using hc.bound32)
  have h23 := abs_le_remainder_add μ.μ23 (γ * h) (c.μ23 * h ^ 2) hc.bound23
  have h33 := abs_le_remainder_add μ.μ33 (1 - α * h) (c.μ33 * h ^ 2) (by
    convert hc.bound33 using 1 <;> dsimp [μ] <;> congr 1 <;> ring)
  have he33 : |1 - α * h| ≤ 1 + α * h := by
    apply (abs_sub _ _).trans
    simp [abs_of_nonneg (by positivity : 0 ≤ α * h)]
  have hKu : 1 + γ + c.μ12 + c.μ22 + c.μ32 ≤ K :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hKv : γ + α + c.μ13 + c.μ23 + c.μ33 ≤ K :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hKc : LF + ((3 + γ) / 2) * LG * (1 + LF) ≤ K := le_max_left _ _
  have hcu : 0 ≤ c.μ12 + c.μ22 + c.μ32 := by dsimp [c, holRemainderConstants]; positivity
  have hcv : 0 ≤ c.μ13 + c.μ23 + c.μ33 := by dsimp [c, holRemainderConstants]; positivity
  have hU : |μ.μ12| + |μ.μ22| + |μ.μ32| ≤ 1 + K * h := by
    simp only [abs_of_pos hh, abs_one, abs_mul, abs_neg, abs_of_nonneg hγ,
      abs_of_pos hh] at h12 h22 h32
    have hb := mul_le_mul_of_nonneg_left hh2 hcu
    have hk := mul_le_mul_of_nonneg_right hKu hh.le
    nlinarith
  have hV : |μ.μ13| + |μ.μ23| + |μ.μ33| ≤ 1 + K * h := by
    simp only [abs_mul, abs_of_nonneg hγ, abs_of_pos hh] at h23
    have hb := mul_le_mul_of_nonneg_left hh2 hcv
    have hk := mul_le_mul_of_nonneg_right hKv hh.le
    nlinarith [hc.bound13]
  have hW : h / 2 + 1 + |μ.μ31| ≤ (3 + γ) / 2 := by
    have hb := hc.bound31'
    change |μ.μ31| ≤ γ / 2 * h at hb
    nlinarith [mul_le_mul_of_nonneg_left hh1 (by positivity : 0 ≤ γ / 2)]
  have hC : (1 + h * LF) * (1 + (h / 2 + 1 + |μ.μ31|) * h * LG) ≤ 1 + K * h := by
    calc
      _ ≤ (1 + h * LF) * (1 + ((3 + γ) / 2) * h * LG) := by gcongr
      _ ≤ 1 + (LF + ((3 + γ) / 2) * LG * (1 + LF)) * h := by
        have hb := mul_le_mul_of_nonneg_left hh2 (by positivity : 0 ≤ LF * ((3 + γ) / 2) * LG)
        nlinarith
      _ ≤ _ := by gcongr
  unfold holAmplification
  rw [abs_of_pos hh]
  exact max_le hC (max_le hU hV)

/-- Exponential finite-horizon control of the geometric amplification. -/
theorem amplification_exponential_bound (a K h : ℝ) (ha : 0 ≤ a)
    (hK : 0 ≤ K) (hh : 0 ≤ h) (hA : a ≤ 1 + K * h) (n : ℕ) :
    a ^ n ≤ Real.exp (K * h * n) ∧
      amplificationSum a n ≤ n * Real.exp (K * h * n) := by
  have hp (k : ℕ) : a ^ k ≤ Real.exp (K * h * k) := by
    have hb : a ≤ Real.exp (K * h) := hA.trans (by simpa [add_comm] using Real.add_one_le_exp (K * h))
    calc
      _ ≤ Real.exp (K * h) ^ k := pow_le_pow_left₀ ha hb k
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  constructor
  · exact hp n
  · unfold amplificationSum
    calc
      _ ≤ ∑ _k ∈ Finset.range n, Real.exp (K * h * n) := by
        apply Finset.sum_le_sum
        intro k hk
        exact (hp k).trans (Real.exp_le_exp.mpr (by
          have hk' : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hk).le
          exact mul_le_mul_of_nonneg_left hk' (mul_nonneg hK hh)))
      _ = _ := by simp

/-- Translating a proved exact-budget estimate into a finite-horizon
`O(sqrt h)` statement. The inputs concern scalar coefficient/local budgets,
not an assumed numerical error recurrence. -/
theorem finite_budget_sqrt_rate (e e0 a D N C K h : ℝ) (n : ℕ)
    (he0 : 0 ≤ e0) (ha : 0 ≤ a) (hD : 0 ≤ D) (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hh : 0 < h) (hh1 : h ≤ 1) (hA : a ≤ 1 + K * h)
    (hbudget : e ≤ a ^ n * e0 +
      (D * h ^ 2 + (N + (8 / 3 : ℝ) * C) * h * Real.sqrt h) * amplificationSum a n) :
    e ≤ Real.exp (K * h * n) *
      (e0 + (D + N + (8 / 3 : ℝ) * C) * (n * h) * Real.sqrt h) := by
  have hp := amplification_exponential_bound a K h ha hK hh.le hA n
  have hpow : h ^ 2 ≤ h := by nlinarith
  have hs : h ^ 2 ≤ h * Real.sqrt h := by
    have hroot := Real.le_sqrt_of_sq_le hpow
    nlinarith
  have hb : D * h ^ 2 + (N + (8 / 3 : ℝ) * C) * h * Real.sqrt h ≤
      (D + N + (8 / 3 : ℝ) * C) * h * Real.sqrt h := by
    have hd := mul_le_mul_of_nonneg_left hs hD
    nlinarith
  have hsum : 0 ≤ amplificationSum a n := by unfold amplificationSum; positivity
  calc
    e ≤ a ^ n * e0 +
      (D * h ^ 2 + (N + (8 / 3 : ℝ) * C) * h * Real.sqrt h) * amplificationSum a n := hbudget
    _ ≤ Real.exp (K * h * n) * e0 +
        ((D + N + (8 / 3 : ℝ) * C) * h * Real.sqrt h) *
          (n * Real.exp (K * h * n)) := by
      gcongr
      exact hp.1
      exact hp.2
    _ = _ := by ring

section ReferenceRate
variable {Θ X : Type*}
variable [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
open MeasureTheory

/-- New explicit finite-horizon square-root-step discretisation rate for the
actual higher-order method. `K` and `D` are the displayed computable stability
and coefficient consistency constants. The innovation input is an explicit
`N*h*sqrt(h)` coupling bound, and the reference is the original integral
system. No error recurrence is assumed. -/
theorem higherOrder_integral_reference_sqrt_rate
    (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (LF LG α γ h Fθ FG U V C N : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) (hFθ : 0 ≤ Fθ) (hFG : 0 ≤ FG)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hC : 0 ≤ C) (hN : 0 ≤ N)
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
    (hnoise : ∀ k, ‖(ξ k).1‖ + ‖(ξ k).2.1‖ + ‖(ξ k).2.2 - b k‖ ≤ N * h * Real.sqrt h)
    (z : HOLState Θ X) (n : ℕ) :
    holError (trajectory (higherOrderStep Fbar G α γ h) ξ z n) (r n 0) ≤
      Real.exp (holStabilityConstant α γ LF LG * h * n) *
        (holError z (r 0 0) +
          (holLocalConsistencyConstant (holRemainderConstants α γ) LG Fθ FG U V + N +
            (8 / 3 : ℝ) * C) * (n * h) * Real.sqrt h) := by
  let A := holAmplification (holCoefficients α γ h) LF LG h
  let D := holLocalConsistencyConstant (holRemainderConstants α γ) LG Fθ FG U V
  let K := holStabilityConstant α γ LF LG
  have hA0 : 0 ≤ A := by dsimp [A, holAmplification]; positivity
  have hD : 0 ≤ D := by dsimp [D, holLocalConsistencyConstant, holRemainderConstants]; positivity
  have hK : 0 ≤ K := by dsimp [K, holStabilityConstant, holRemainderConstants]; positivity
  have hA : A ≤ 1 + K * h := holAmplification_linear_bound α γ LF LG h hα hγ hLF hLG hh hh1
  have hbase := higherOrder_integral_reference_bound Fbar G LF LG α γ h Fθ FG U V C
    (N * h * Real.sqrt h) hh.le hLF hLG hF hG r b ξ hInt heq hcompat hmod
    hFbound hGbound hU hV hnoise z n
  have hdet := holDeterministicBudget_quadratic α γ h LG Fθ FG U V hα hγ hh hh1 hFG hU0 hV0
  have hsum : 0 ≤ amplificationSum A n := by unfold amplificationSum; positivity
  apply finite_budget_sqrt_rate _ _ A D N C K h n
    (by unfold holError; positivity) hA0 hD hN hC hK hh hh1 hA
  have hb := mul_le_mul_of_nonneg_right hdet hsum
  dsimp [A, D] at *
  nlinarith only [hbase, hb]

/-- Finite-horizon square-root-step rate, with no reference assumptions
beyond the first `n` steps. -/
theorem higherOrder_integral_reference_finite_sqrt_rate
    (Fbar : Θ → X → Θ) (G : Θ → X → X)
    (LF LG α γ h Fθ FG U V C N : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) (hFθ : 0 ≤ Fθ) (hFG : 0 ≤ FG)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hC : 0 ≤ C) (hN : 0 ≤ N)
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
    (hnoise : ∀ k, k < n → ‖(ξ k).1‖ + ‖(ξ k).2.1‖ + ‖(ξ k).2.2 - b k‖ ≤ N * h * Real.sqrt h)
    (z : HOLState Θ X) :
    holError (trajectory (higherOrderStep Fbar G α γ h) ξ z n) (r n 0) ≤
      Real.exp (holStabilityConstant α γ LF LG * h * n) *
        (holError z (r 0 0) +
          (holLocalConsistencyConstant (holRemainderConstants α γ) LG Fθ FG U V + N +
            (8 / 3 : ℝ) * C) * (n * h) * Real.sqrt h) := by
  let A := holAmplification (holCoefficients α γ h) LF LG h
  let D := holLocalConsistencyConstant (holRemainderConstants α γ) LG Fθ FG U V
  let K := holStabilityConstant α γ LF LG
  have hA0 : 0 ≤ A := by dsimp [A, holAmplification]; positivity
  have hD : 0 ≤ D := by dsimp [D, holLocalConsistencyConstant, holRemainderConstants]; positivity
  have hK : 0 ≤ K := by dsimp [K, holStabilityConstant, holRemainderConstants]; positivity
  have hA : A ≤ 1 + K * h := holAmplification_linear_bound α γ LF LG h hα hγ hLF hLG hh hh1
  have hbase := higherOrder_integral_reference_finite_bound Fbar G LF LG α γ h Fθ FG U V C
    (N * h * Real.sqrt h) hh.le hLF hLG hF hG r b ξ n hInt heq hcompat hmod
    hFbound hGbound hU hV hnoise z
  have hdet := holDeterministicBudget_quadratic α γ h LG Fθ FG U V hα hγ hh hh1 hFG hU0 hV0
  have hsum : 0 ≤ amplificationSum A n := by unfold amplificationSum; positivity
  apply finite_budget_sqrt_rate _ _ A D N C K h n
    (by unfold holError; positivity) hA0 hD hN hC hK hh hh1 hA
  have hb := mul_le_mul_of_nonneg_right hdet hsum
  dsimp [A, D] at *
  nlinarith only [hbase, hb]

end ReferenceRate

end PBGSO.Methods
