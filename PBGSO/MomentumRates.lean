import PBGSO.HigherOrderRates

/-! # Explicit finite-horizon square-root-step rate for M-MFPO OBABO -/
noncomputable section
namespace PBGSO.Methods

/-- A conservative exponential stability rate for `0<h≤1`. -/
def momentumStabilityConstant (L : ℝ) : ℝ := 1 + 2 * L + L ^ 2 / 2

/-- The deterministic quadratic consistency coefficient. -/
def momentumLocalConsistencyConstant (L γ P F Ξ : ℝ) : ℝ :=
  (γ ^ 2 / 2 + γ / 2) * P + (γ / 2 + 1 / 2) * F +
    L / 2 * (P + Ξ + F / 2)

/-- The actual BAB amplification grows at most linearly in the step size. -/
theorem momentumAmplification_linear_bound (L h : ℝ) (hL : 0 ≤ L)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    momentumAmplification L h ≤ 1 + momentumStabilityConstant L * h := by
  have hh2 : h ^ 2 ≤ h := by nlinarith
  have hh3 : h ^ 3 ≤ h := by nlinarith [mul_le_mul_of_nonneg_left hh2 hh]
  have hb1 := mul_le_mul_of_nonneg_left hh2 hL
  have hb2 := mul_le_mul_of_nonneg_left hh2 (by positivity : 0 ≤ L ^ 2 / 4)
  have hb3 := mul_le_mul_of_nonneg_left hh3 (by positivity : 0 ≤ L ^ 2 / 4)
  unfold momentumAmplification momentumStabilityConstant
  rw [abs_of_nonneg hh]
  nlinarith only [hb1, hb2, hb3]

/-- The physical damping and noise coefficients give a quadratic deterministic
remainder plus an `h*sqrt(h)` innovation response. -/
theorem momentumRemainderBudget_small_step (L γ h P F Ξ : ℝ)
    (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hP : 0 ≤ P) (hF : 0 ≤ F) (hΞ : 0 ≤ Ξ) :
    momentumRemainderBudget L γ h (Real.exp (-γ * h / 2))
      (Real.sqrt (1 - Real.exp (-γ * h))) P F Ξ ≤
      momentumLocalConsistencyConstant L γ P F Ξ * h ^ 2 +
        (Real.sqrt γ * Ξ) * h * Real.sqrt h := by
  let η := Real.exp (-γ * h / 2)
  let σ := Real.sqrt (1 - Real.exp (-γ * h))
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hηsq : η ^ 2 = Real.exp (-γ * h) := by
    dsimp [η]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have he := Real.add_one_le_exp (-γ * h / 2)
  have hhalf : 1 - η ≤ γ * h / 2 := by dsimp [η]; linarith
  have hfull : 0 ≤ η ^ 2 - 1 + γ * h := by
    rw [hηsq]
    have hx := Real.add_one_le_exp (-γ * h)
    linarith
  have hquad : η ^ 2 - 1 + γ * h ≤ γ ^ 2 * h ^ 2 / 2 := by
    rw [hηsq]
    have hx := KineticLangevin.exp_neg_le_quadratic (γ * h) (by positivity)
    rw [← neg_mul] at hx
    nlinarith
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hv : 0 ≤ 1 - Real.exp (-γ * h) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
  have hσ1 : σ ≤ 1 := Real.sqrt_le_one.mpr (by
    have hx := Real.exp_pos (-γ * h)
    linarith)
  have hσroot : σ ≤ Real.sqrt γ * Real.sqrt h := by
    have hv' : 1 - Real.exp (-γ * h) ≤ γ * h := by
      have hx := Real.add_one_le_exp (-γ * h)
      linarith
    exact (Real.sqrt_le_sqrt hv').trans_eq (Real.sqrt_mul hγ _)
  have hb0 : |η ^ 2 - 1 + γ * h| * P ≤ (γ ^ 2 / 2 * P) * h ^ 2 := by
    rw [abs_of_nonneg hfull]
    convert mul_le_mul_of_nonneg_right hquad hP using 1 <;> ring
  have hb1 : |h * (1 - η)| ≤ γ * h ^ 2 / 2 := by
    rw [abs_of_nonneg (mul_nonneg hh.le (sub_nonneg.mpr hη1))]
    have hx := mul_le_mul_of_nonneg_left hhalf hh.le
    nlinarith
  have hb1' : |h * (η - 1)| ≤ γ * h ^ 2 / 2 := by
    have heq : h * (η - 1) = -(h * (1 - η)) := by ring
    rw [heq, abs_neg]
    exact hb1
  have hb2 : |η * h / 2| ≤ h / 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hη1 hh.le]
  have hb3 : |h| * (|η| * P + |σ| * Ξ + |h| / 2 * F) ≤
      h * (P + Ξ + F / 2) := by
    rw [abs_of_pos hh, abs_of_nonneg hη0, abs_of_nonneg hσ0]
    gcongr
    nlinarith [mul_le_mul_of_nonneg_right hη1 hP]
    nlinarith [mul_le_mul_of_nonneg_right hσ1 hΞ]
    nlinarith [mul_le_mul_of_nonneg_right hh1 hF]
  have hbn : |h * σ| * Ξ ≤ (Real.sqrt γ * Ξ) * h * Real.sqrt h := by
    rw [abs_of_nonneg (mul_nonneg hh.le hσ0)]
    have hx := mul_le_mul_of_nonneg_left hσroot (mul_nonneg hh.le hΞ)
    nlinarith
  unfold momentumRemainderBudget
  change _ ≤ momentumLocalConsistencyConstant L γ P F Ξ * h ^ 2 + (Real.sqrt γ * Ξ) * h * Real.sqrt h
  calc
    _ ≤ (γ ^ 2 / 2 * P) * h ^ 2 + (γ * h ^ 2 / 2) * F +
        (h / 2) * L * (h * (P + Ξ + F / 2)) +
        (γ * h ^ 2 / 2) * P + h ^ 2 / 2 * F +
        (Real.sqrt γ * Ξ) * h * Real.sqrt h := by
      gcongr
    _ = _ := by unfold momentumLocalConsistencyConstant; ring

/-- The square root of the OU variance differs from the Brownian coefficient
by at most a cubic-half-order term. -/
theorem sqrt_exponential_variance_error (t : ℝ) (ht : 0 ≤ t) :
    |Real.sqrt (1 - Real.exp (-t)) - Real.sqrt t| ≤ t * Real.sqrt t / 2 := by
  let s := Real.sqrt (1 - Real.exp (-t))
  have hv : 0 ≤ 1 - Real.exp (-t) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - Real.exp (-t) := Real.sq_sqrt hv
  have ht2 := Real.sq_sqrt ht
  have hvle : 1 - Real.exp (-t) ≤ t := by linarith [Real.add_one_le_exp (-t)]
  have hsle : s ≤ Real.sqrt t := Real.sqrt_le_sqrt hvle
  have hrem : t - s ^ 2 ≤ t ^ 2 / 2 := by
    rw [hs2]
    linarith [KineticLangevin.exp_neg_le_quadratic t ht]
  rw [abs_of_nonpos (sub_nonpos.mpr hsle)]
  change -(s - Real.sqrt t) ≤ t * Real.sqrt t / 2
  rcases eq_or_lt_of_le ht with hzero | hpos
  · subst t
    norm_num [s]
  · have hroot : 0 < Real.sqrt t := Real.sqrt_pos.mpr hpos
    apply (mul_le_mul_iff_left₀ hroot).mp
    have hcross : 0 ≤ (Real.sqrt t - s) * s := mul_nonneg (sub_nonneg.mpr hsle) hs0
    nlinarith only [hrem, hcross, ht2]

section NoiseComparison
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual two-half-step innovation comparison. If `ξ,ξ'` are normalized
Brownian half increments, `sqrt(γh)*(ξ+ξ')` is the reference full Brownian
increment. The bound is pathwise, and also valid in L². -/
theorem momentum_noise_coupling_bound (γ h Ξ : ℝ) (hγ : 0 ≤ γ) (hh : 0 ≤ h)
    (hΞ : 0 ≤ Ξ) (ξ ξ' : E) (hξ : ‖ξ‖ ≤ Ξ) (hξ' : ‖ξ'‖ ≤ Ξ) :
    ‖Real.sqrt (1 - Real.exp (-γ * h)) •
        (Real.exp (-γ * h / 2) • ξ + ξ') -
      Real.sqrt (γ * h) • (ξ + ξ')‖ ≤
      ((3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ) * h * Real.sqrt h := by
  let t := γ * h
  let η := Real.exp (-t / 2)
  let σ := Real.sqrt (1 - Real.exp (-t))
  have ht : 0 ≤ t := mul_nonneg hγ hh
  have hη0 : 0 ≤ η := (Real.exp_pos _).le
  have hη1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by dsimp [t]; nlinarith)
  have hhalf : |η - 1| ≤ t / 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hη1)]
    have he := Real.add_one_le_exp (-t / 2)
    dsimp [η]
    linarith
  have hs := sqrt_exponential_variance_error t ht
  have hfirst : |σ * η - Real.sqrt t| ≤ t * Real.sqrt t := by
    calc
      _ = |η * (σ - Real.sqrt t) + (η - 1) * Real.sqrt t| := by congr 1; ring
      _ ≤ |η * (σ - Real.sqrt t)| + |(η - 1) * Real.sqrt t| := abs_add_le _ _
      _ = η * |σ - Real.sqrt t| + |η - 1| * Real.sqrt t := by
        rw [abs_mul, abs_mul, abs_of_nonneg hη0, abs_of_nonneg (Real.sqrt_nonneg t)]
      _ ≤ 1 * (t * Real.sqrt t / 2) + (t / 2) * Real.sqrt t := by gcongr
      _ = _ := by ring
  have heq : σ • (η • ξ + ξ') - Real.sqrt t • (ξ + ξ') =
      (σ * η - Real.sqrt t) • ξ + (σ - Real.sqrt t) • ξ' := by module
  have hb : ‖σ • (η • ξ + ξ') - Real.sqrt t • (ξ + ξ')‖ ≤
      (3 / 2 : ℝ) * t * Real.sqrt t * Ξ := by
    rw [heq]
    calc
      _ ≤ ‖(σ * η - Real.sqrt t) • ξ‖ + ‖(σ - Real.sqrt t) • ξ'‖ := norm_add_le _ _
      _ = |σ * η - Real.sqrt t| * ‖ξ‖ + |σ - Real.sqrt t| * ‖ξ'‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ (t * Real.sqrt t) * Ξ + (t * Real.sqrt t / 2) * Ξ := by gcongr
      _ = _ := by ring
  dsimp [η, σ, t] at hb
  rw [show -(γ * h) = -γ * h by ring] at hb
  convert hb using 1
  rw [Real.sqrt_mul hγ]
  ring

end NoiseComparison

section ReferenceRate
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
open MeasureTheory

/-- New explicit finite-horizon square-root-step error bound for the actual
M-MFPO OBABO coefficients, coupled to normalized Brownian half increments.
The optimiser remains noise-free when `E=Θ×X` and all innovations have first
coordinate zero. Gaussianity is not needed for this pathwise theorem; a
Brownian implementation supplies the displayed increment identity. -/
theorem momentum_integral_reference_sqrt_rate
    (G : E → E) (L γ h R P F Ξ : ℝ)
    (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hR : 0 ≤ R) (hP : 0 ≤ P) (hF : 0 ≤ F) (hΞ : 0 ≤ Ξ)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (p q : ℕ → ℝ → E) (b : ℕ → E) (ξ : ℕ → E × E)
    (hpInt : ∀ k, IntervalIntegrable (p k) volume 0 h)
    (hfInt : ∀ k, IntervalIntegrable (fun t ↦ G (q k t) + γ • p k t) volume 0 h)
    (hp : ∀ k, p k h = p k 0 - (∫ t in 0..h, G (q k t) + γ • p k t) + b k)
    (hq : ∀ k, q k h = q k 0 + (∫ t in 0..h, p k t))
    (hcompat : ∀ k, p (k + 1) 0 = p k h ∧ q (k + 1) 0 = q k h)
    (hmod : ∀ k t, t ∈ Set.Icc 0 h →
      ‖p k t - p k 0‖ ≤ R * Real.sqrt t ∧ ‖q k t - q k 0‖ ≤ R * Real.sqrt t)
    (hpbound : ∀ k, ‖p k 0‖ ≤ P) (hfbound : ∀ k, ‖G (q k 0)‖ ≤ F)
    (hξbound : ∀ k, ‖(ξ k).1‖ ≤ Ξ ∧ ‖(ξ k).2‖ ≤ Ξ)
    (hbrown : ∀ k, b k = Real.sqrt (γ * h) • ((ξ k).1 + (ξ k).2))
    (z : E × E) (n : ℕ) :
    phaseError
      (trajectory (fun s r ↦ KineticLangevin.obaboStep G h (Real.exp (-γ * h / 2))
        (Real.sqrt (1 - Real.exp (-γ * h))) s r.1 r.2) ξ z n)
      (p n 0, q n 0) ≤
      Real.exp (momentumStabilityConstant L * h * n) *
        (phaseError z (p 0 0, q 0 0) +
          (momentumLocalConsistencyConstant L γ P F Ξ + Real.sqrt γ * Ξ +
            (3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ +
            (2 / 3 : ℝ) * (L + γ + 1) * R) * (n * h) * Real.sqrt h) := by
  let η := Real.exp (-γ * h / 2)
  let σ := Real.sqrt (1 - Real.exp (-γ * h))
  let A := momentumAmplification L h
  let D := momentumLocalConsistencyConstant L γ P F Ξ
  let K := momentumStabilityConstant L
  let N := Real.sqrt γ * Ξ + (3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ +
    (2 / 3 : ℝ) * (L + γ + 1) * R
  have hη : |η| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hnoise (k : ℕ) : ‖σ • (η • (ξ k).1 + (ξ k).2) - b k‖ ≤
      ((3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ * h * Real.sqrt h) := by
    rw [hbrown k]
    exact momentum_noise_coupling_bound γ h Ξ hγ hh.le hΞ _ _ (hξbound k).1 (hξbound k).2
  have hbase := obabo_integral_reference_bound G L γ h η σ R P F Ξ
    ((3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ * h * Real.sqrt h)
    hh.le hL hγ hη hLip p q b ξ hpInt hfInt hp hq hcompat hmod hpbound hfbound
    (fun k ↦ (hξbound k).1) hnoise z n
  have hrem := momentumRemainderBudget_small_step L γ h P F Ξ hL hγ hh hh1 hP hF hΞ
  have hA0 : 0 ≤ A := by dsimp [A, momentumAmplification]; positivity
  have hD : 0 ≤ D := by dsimp [D, momentumLocalConsistencyConstant]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hK : 0 ≤ K := by dsimp [K, momentumStabilityConstant]; positivity
  have hA : A ≤ 1 + K * h := momentumAmplification_linear_bound L h hL hh.le hh1
  have hsum : 0 ≤ amplificationSum A n := by unfold amplificationSum; positivity
  have hbudget : phaseError
      (trajectory (fun s r ↦ KineticLangevin.obaboStep G h η σ s r.1 r.2) ξ z n) (p n 0, q n 0) ≤
      A ^ n * phaseError z (p 0 0, q 0 0) +
        (D * h ^ 2 + (N + (8 / 3 : ℝ) * 0) * h * Real.sqrt h) * amplificationSum A n := by
    have hb := mul_le_mul_of_nonneg_right hrem hsum
    dsimp [η, σ, A, D, N] at *
    nlinarith only [hbase, hb]
  have hr := finite_budget_sqrt_rate _ (phaseError z (p 0 0, q 0 0)) A D N 0 K h n
    (by unfold phaseError; positivity) hA0 hD hN (by norm_num) hK hh hh1 hA hbudget
  dsimp [η, σ, A, D, N, K] at hr
  simpa only [mul_zero, add_zero, add_assoc] using hr

/-- Finite-horizon square-root-step rate: every reference and innovation
premise is restricted to the first `n` steps. -/
theorem momentum_integral_reference_finite_sqrt_rate
    (G : E → E) (L γ h R P F Ξ : ℝ)
    (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hR : 0 ≤ R) (hP : 0 ≤ P) (hF : 0 ≤ F) (hΞ : 0 ≤ Ξ)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (p q : ℕ → ℝ → E) (b : ℕ → E) (ξ : ℕ → E × E) (n : ℕ)
    (hpInt : ∀ k, k < n → IntervalIntegrable (p k) volume 0 h)
    (hfInt : ∀ k, k < n → IntervalIntegrable (fun t ↦ G (q k t) + γ • p k t) volume 0 h)
    (hp : ∀ k, k < n → p k h = p k 0 - (∫ t in 0..h, G (q k t) + γ • p k t) + b k)
    (hq : ∀ k, k < n → q k h = q k 0 + (∫ t in 0..h, p k t))
    (hcompat : ∀ k, k < n → p (k + 1) 0 = p k h ∧ q (k + 1) 0 = q k h)
    (hmod : ∀ k, k < n → ∀ t, t ∈ Set.Icc 0 h →
      ‖p k t - p k 0‖ ≤ R * Real.sqrt t ∧ ‖q k t - q k 0‖ ≤ R * Real.sqrt t)
    (hpbound : ∀ k, k < n → ‖p k 0‖ ≤ P) (hfbound : ∀ k, k < n → ‖G (q k 0)‖ ≤ F)
    (hξbound : ∀ k, k < n → ‖(ξ k).1‖ ≤ Ξ ∧ ‖(ξ k).2‖ ≤ Ξ)
    (hbrown : ∀ k, k < n → b k = Real.sqrt (γ * h) • ((ξ k).1 + (ξ k).2))
    (z : E × E) :
    phaseError
      (trajectory (fun s r ↦ KineticLangevin.obaboStep G h (Real.exp (-γ * h / 2))
        (Real.sqrt (1 - Real.exp (-γ * h))) s r.1 r.2) ξ z n)
      (p n 0, q n 0) ≤
      Real.exp (momentumStabilityConstant L * h * n) *
        (phaseError z (p 0 0, q 0 0) +
          (momentumLocalConsistencyConstant L γ P F Ξ + Real.sqrt γ * Ξ +
            (3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ +
            (2 / 3 : ℝ) * (L + γ + 1) * R) * (n * h) * Real.sqrt h) := by
  let η := Real.exp (-γ * h / 2)
  let σ := Real.sqrt (1 - Real.exp (-γ * h))
  let A := momentumAmplification L h
  let D := momentumLocalConsistencyConstant L γ P F Ξ
  let K := momentumStabilityConstant L
  let N := Real.sqrt γ * Ξ + (3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ +
    (2 / 3 : ℝ) * (L + γ + 1) * R
  have hη : |η| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith)
  have hnoise (k : ℕ) (hk : k < n) : ‖σ • (η • (ξ k).1 + (ξ k).2) - b k‖ ≤
      ((3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ * h * Real.sqrt h) := by
    rw [hbrown k hk]
    exact momentum_noise_coupling_bound γ h Ξ hγ hh.le hΞ _ _ (hξbound k hk).1 (hξbound k hk).2
  have hbase := obabo_integral_reference_finite_bound G L γ h η σ R P F Ξ
    ((3 / 2 : ℝ) * γ * Real.sqrt γ * Ξ * h * Real.sqrt h)
    hh.le hL hγ hη hLip p q b ξ n hpInt hfInt hp hq hcompat hmod hpbound hfbound
    (fun k hk ↦ (hξbound k hk).1) hnoise z
  have hrem := momentumRemainderBudget_small_step L γ h P F Ξ hL hγ hh hh1 hP hF hΞ
  have hA0 : 0 ≤ A := by dsimp [A, momentumAmplification]; positivity
  have hD : 0 ≤ D := by dsimp [D, momentumLocalConsistencyConstant]; positivity
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hK : 0 ≤ K := by dsimp [K, momentumStabilityConstant]; positivity
  have hA : A ≤ 1 + K * h := momentumAmplification_linear_bound L h hL hh.le hh1
  have hsum : 0 ≤ amplificationSum A n := by unfold amplificationSum; positivity
  have hbudget : phaseError
      (trajectory (fun s r ↦ KineticLangevin.obaboStep G h η σ s r.1 r.2) ξ z n) (p n 0, q n 0) ≤
      A ^ n * phaseError z (p 0 0, q 0 0) +
        (D * h ^ 2 + (N + (8 / 3 : ℝ) * 0) * h * Real.sqrt h) * amplificationSum A n := by
    have hb := mul_le_mul_of_nonneg_right hrem hsum
    dsimp [η, σ, A, D, N] at *
    nlinarith only [hbase, hb]
  have hr := finite_budget_sqrt_rate _ (phaseError z (p 0 0, q 0 0)) A D N 0 K h n
    (by unfold phaseError; positivity) hA0 hD hN (by norm_num) hK hh hh1 hA hbudget
  dsimp [η, σ, A, D, N, K] at hr
  simpa only [mul_zero, add_zero, add_assoc] using hr

end ReferenceRate

end PBGSO.Methods
