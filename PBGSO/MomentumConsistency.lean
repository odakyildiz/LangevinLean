import PBGSO.Methods
import UnadjustedLangevin.LocalError

/-!
# A finite-horizon discretisation bound against an additive integral solution

The reference is specified by its integral equations, not by an assumed error
recurrence. Moment/modulus and innovation-coupling assumptions are stated at the
point of use. In particular a Brownian law, its existence, and a coupling of the
two Gaussian O stages to a Brownian increment are not inferred from these
pathwise equations. The ambient Banach norm can equally be an L² norm.
-/
noncomputable section
open MeasureTheory
namespace PBGSO.Methods
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Euler comparison with noise only in momentum. -/
def momentumEuler (G : E → E) (γ h : ℝ) (z : E × E) (b : E) : E × E :=
  (z.1 - h • G z.2 - (γ * h) • z.1 + b, z.2 + h • z.1)

/-- Explicit algebraic remainder budget for OBABO relative to Euler. The
coefficient of `‖ξ‖` accounts for the position's response to the first O stage. -/
def momentumRemainderBudget (L γ h η σ P F Ξ : ℝ) : ℝ :=
  |η ^ 2 - 1 + γ * h| * P + |h * (1 - η)| * F +
    |η * h / 2| * L * (|h| * (|η| * P + |σ| * Ξ + |h| / 2 * F)) +
    |h * (η - 1)| * P + h ^ 2 / 2 * F + |h * σ| * Ξ

/-- New local algebraic consistency estimate for the actual OBABO map. All
force and noise errors are derived from the expanded scheme. -/
theorem obabo_euler_error (G : E → E) (L γ h η σ P F Ξ : ℝ)
    (hL : 0 ≤ L) (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (z : E × E) (ξ ξ' : E) (hp : ‖z.1‖ ≤ P) (hf : ‖G z.2‖ ≤ F)
    (hξ : ‖ξ‖ ≤ Ξ) :
    phaseError (KineticLangevin.obaboStep G h η σ z ξ ξ')
      (momentumEuler G γ h z (σ • (η • ξ + ξ'))) ≤
      momentumRemainderBudget L γ h η σ P F Ξ := by
  let v := η • z.1 + σ • ξ - (h / 2) • G z.2
  let q := z.2 + h • v
  have hv : ‖v‖ ≤ |η| * P + |σ| * Ξ + |h| / 2 * F := by
    calc
      ‖v‖ ≤ ‖η • z.1 + σ • ξ‖ + ‖(h / 2) • G z.2‖ := norm_sub_le _ _
      _ ≤ (‖η • z.1‖ + ‖σ • ξ‖) + ‖(h / 2) • G z.2‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by simp only [norm_smul, Real.norm_eq_abs, abs_div]; norm_num; gcongr
  have hq : ‖q - z.2‖ ≤ |h| * (|η| * P + |σ| * Ξ + |h| / 2 * F) := by
    dsimp [q]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hv (abs_nonneg h)
  have heqv : η • (v - (h / 2) • G q) + σ • ξ' -
      (z.1 - h • G z.2 - (γ * h) • z.1 + σ • (η • ξ + ξ')) =
      (η ^ 2 - 1 + γ * h) • z.1 + (h * (1 - η)) • G z.2 -
        (η * h / 2) • (G q - G z.2) := by dsimp [v]; module
  have heqx : q - (z.2 + h • z.1) =
      (h * (η - 1)) • z.1 - (h ^ 2 / 2) • G z.2 + (h * σ) • ξ := by
    dsimp [q, v]; module
  have hvel : ‖η • (v - (h / 2) • G q) + σ • ξ' -
      (z.1 - h • G z.2 - (γ * h) • z.1 + σ • (η • ξ + ξ'))‖ ≤
      |η ^ 2 - 1 + γ * h| * P + |h * (1 - η)| * F +
      |η * h / 2| * L * (|h| * (|η| * P + |σ| * Ξ + |h| / 2 * F)) := by
    rw [heqv]
    calc
      _ ≤ ‖(η ^ 2 - 1 + γ * h) • z.1 + (h * (1 - η)) • G z.2‖ +
          ‖(η * h / 2) • (G q - G z.2)‖ := norm_sub_le _ _
      _ ≤ (‖(η ^ 2 - 1 + γ * h) • z.1‖ + ‖(h * (1 - η)) • G z.2‖) +
          ‖(η * h / 2) • (G q - G z.2)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_smul, Real.norm_eq_abs]
        have hg := mul_le_mul_of_nonneg_left
          ((hLip q z.2).trans (mul_le_mul_of_nonneg_left hq hL))
          (abs_nonneg (η * h / 2))
        have hab := add_le_add
          (mul_le_mul_of_nonneg_left hp (abs_nonneg (η ^ 2 - 1 + γ * h)))
          (mul_le_mul_of_nonneg_left hf (abs_nonneg (h * (1 - η))))
        convert add_le_add hab hg using 1 <;> ring
  have hpos : ‖q - (z.2 + h • z.1)‖ ≤
      |h * (η - 1)| * P + h ^ 2 / 2 * F + |h * σ| * Ξ := by
    rw [heqx]
    calc
      _ ≤ ‖(h * (η - 1)) • z.1 - (h ^ 2 / 2) • G z.2‖ + ‖(h * σ) • ξ‖ := norm_add_le _ _
      _ ≤ (‖(h * (η - 1)) • z.1‖ + ‖(h ^ 2 / 2) • G z.2‖) + ‖(h * σ) • ξ‖ := by
        gcongr; exact norm_sub_le _ _
      _ ≤ _ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / 2)]; gcongr
  change ‖η • (v - (h / 2) • G q) + σ • ξ' - _‖ + ‖q - _‖ ≤ _
  exact (add_le_add hvel hpos).trans_eq (by unfold momentumRemainderBudget; ring)

/-- Integral square-root modulus estimate used for the reference drift. -/
theorem integral_deviation_sqrt (f : ℝ → E) (C h : ℝ) (hh : 0 ≤ h)
    (hbound : ∀ t ∈ Set.Icc 0 h, ‖f t - f 0‖ ≤ C * Real.sqrt t) :
    ‖∫ t in 0..h, f t - f 0‖ ≤ (2 / 3 : ℝ) * C * h * Real.sqrt h := by
  calc
    _ ≤ ∫ t in 0..h, C * Real.sqrt t :=
      intervalIntegral.norm_integral_le_of_norm_le hh
        (Filter.Eventually.of_forall (fun t ht ↦ hbound t ⟨ht.1.le, ht.2⟩))
        ((by fun_prop : Continuous (fun t : ℝ ↦ C * Real.sqrt t)).intervalIntegrable _ _)
    _ = _ := by rw [intervalIntegral.integral_const_mul, ULA.integral_sqrt_zero h hh]; ring

/-- New Euler comparison derived from the kinetic integral equations. The
square-root modulus is suitable for an L² Brownian-driven reference. -/
theorem momentumEuler_integral_error (G : E → E) (L γ h R : ℝ)
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hγ : 0 ≤ γ)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (p q : ℝ → E) (b : E)
    (hpInt : IntervalIntegrable p volume 0 h)
    (hfInt : IntervalIntegrable (fun t ↦ G (q t) + γ • p t) volume 0 h)
    (hp : p h = p 0 - (∫ t in 0..h, G (q t) + γ • p t) + b)
    (hq : q h = q 0 + (∫ t in 0..h, p t))
    (hmod : ∀ t ∈ Set.Icc 0 h,
      ‖p t - p 0‖ ≤ R * Real.sqrt t ∧ ‖q t - q 0‖ ≤ R * Real.sqrt t) :
    phaseError (momentumEuler G γ h (p 0, q 0) b) (p h, q h) ≤
      (2 / 3 : ℝ) * (L + γ + 1) * R * h * Real.sqrt h := by
  have hf (t : ℝ) (ht : t ∈ Set.Icc 0 h) :
      ‖(G (q t) + γ • p t) - (G (q 0) + γ • p 0)‖ ≤
        ((L + γ) * R) * Real.sqrt t := by
    calc
      _ ≤ ‖G (q t) - G (q 0)‖ + ‖γ • p t - γ • p 0‖ := by
        have he : (G (q t) + γ • p t) - (G (q 0) + γ • p 0) =
            (G (q t) - G (q 0)) + (γ • p t - γ • p 0) := by module
        rw [he]
        exact norm_add_le _ _
      _ ≤ L * (R * Real.sqrt t) + γ * (R * Real.sqrt t) := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]
        exact add_le_add
          ((hLip _ _).trans (mul_le_mul_of_nonneg_left (hmod t ht).2 hL))
          (mul_le_mul_of_nonneg_left (hmod t ht).1 hγ)
      _ = _ := by ring
  have hv := integral_deviation_sqrt (fun t ↦ G (q t) + γ • p t) ((L + γ) * R) h hh hf
  have hx := integral_deviation_sqrt p R h hh (fun t ht ↦ (hmod t ht).1)
  have hev : (momentumEuler G γ h (p 0, q 0) b).1 - p h =
      ∫ t in 0..h, (G (q t) + γ • p t) - (G (q 0) + γ • p 0) := by
    rw [intervalIntegral.integral_sub hfInt intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero]
    dsimp [momentumEuler]
    rw [hp]
    module
  have hex : (momentumEuler G γ h (p 0, q 0) b).2 - q h =
      -(∫ t in 0..h, p t - p 0) := by
    rw [intervalIntegral.integral_sub hpInt intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero]
    dsimp [momentumEuler]
    rw [hq]
    module
  unfold phaseError
  rw [hev, hex, norm_neg]
  nlinarith

/-- Changing only the additive momentum increment has exactly this effect. -/
theorem momentumEuler_noise_error (G : E → E) (γ h : ℝ) (z : E × E) (b c : E) :
    phaseError (momentumEuler G γ h z b) (momentumEuler G γ h z c) = ‖b - c‖ := by
  unfold phaseError momentumEuler
  have he : (z.1 - h • G z.2 - (γ * h) • z.1 + b) -
      (z.1 - h • G z.2 - (γ * h) • z.1 + c) = b - c := by module
  rw [he, sub_self, norm_zero, add_zero]

/-- New finite-horizon bound for OBABO against compatible kinetic integral
solution segments. It is derived from the actual map and integral equations.

`R` controls the reference square-root modulus, `P,F` its grid-point moments,
`Ξ` the first O innovation norm, and `B` the error coupling the net O increment
to the reference additive increment. These can be deterministic norms or L²
norms. Establishing these assumptions for a particular stochastic construction
is a separate obligation; no stationary target is assumed or concluded. -/
theorem obabo_integral_reference_bound
    (G : E → E) (L γ h η σ R P F Ξ B : ℝ)
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hη : |η| ≤ 1)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (p q : ℕ → ℝ → E) (b : ℕ → E) (ξ : ℕ → E × E)
    (hpInt : ∀ k, IntervalIntegrable (p k) volume 0 h)
    (hfInt : ∀ k, IntervalIntegrable (fun t ↦ G (q k t) + γ • p k t) volume 0 h)
    (hp : ∀ k, p k h = p k 0 - (∫ t in 0..h, G (q k t) + γ • p k t) + b k)
    (hq : ∀ k, q k h = q k 0 + (∫ t in 0..h, p k t))
    (hcompat : ∀ k, p (k + 1) 0 = p k h ∧ q (k + 1) 0 = q k h)
    (hmod : ∀ k t, t ∈ Set.Icc 0 h →
      ‖p k t - p k 0‖ ≤ R * Real.sqrt t ∧
      ‖q k t - q k 0‖ ≤ R * Real.sqrt t)
    (hpbound : ∀ k, ‖p k 0‖ ≤ P) (hfbound : ∀ k, ‖G (q k 0)‖ ≤ F)
    (hξbound : ∀ k, ‖(ξ k).1‖ ≤ Ξ)
    (hnoise : ∀ k, ‖σ • (η • (ξ k).1 + (ξ k).2) - b k‖ ≤ B)
    (z : E × E) (n : ℕ) :
    phaseError
      (trajectory (fun s r ↦ KineticLangevin.obaboStep G h η σ s r.1 r.2) ξ z n)
      (p n 0, q n 0) ≤
      momentumAmplification L h ^ n * phaseError z (p 0 0, q 0 0) +
        (momentumRemainderBudget L γ h η σ P F Ξ + B +
          (2 / 3 : ℝ) * (L + γ + 1) * R * h * Real.sqrt h) *
            amplificationSum (momentumAmplification L h) n := by
  have hA : 0 ≤ momentumAmplification L h := by unfold momentumAmplification; positivity
  apply finite_accumulation _ _ _ hA _ n
  intro k
  dsimp only [trajectory]
  rw [(hcompat k).1, (hcompat k).2]
  let s := trajectory (fun s r ↦ KineticLangevin.obaboStep G h η σ s r.1 r.2) ξ z k
  let r : E × E := (p k 0, q k 0)
  let c := σ • (η • (ξ k).1 + (ξ k).2)
  have hs := obabo_error G L h η σ hL hη hLip s r
    (ξ k).1 (ξ k).2 (ξ k).1 (ξ k).2
  simp only [sub_self, norm_zero, mul_zero, zero_add, add_zero] at hs
  have hl := obabo_euler_error G L γ h η σ P F Ξ hL hLip r
    (ξ k).1 (ξ k).2 (hpbound k) (hfbound k) (hξbound k)
  have hn : phaseError (momentumEuler G γ h r c) (momentumEuler G γ h r (b k)) ≤ B := by
    rw [momentumEuler_noise_error]
    exact hnoise k
  have he := momentumEuler_integral_error G L γ h R hh hL hγ hLip
    (p k) (q k) (b k) (hpInt k) (hfInt k) (hp k) (hq k) (hmod k)
  have ht1 := phaseError_triangle
    (KineticLangevin.obaboStep G h η σ s (ξ k).1 (ξ k).2)
    (KineticLangevin.obaboStep G h η σ r (ξ k).1 (ξ k).2) (p k h, q k h)
  have ht2 := phaseError_triangle
    (KineticLangevin.obaboStep G h η σ r (ξ k).1 (ξ k).2)
    (momentumEuler G γ h r c) (p k h, q k h)
  have ht3 := phaseError_triangle (momentumEuler G γ h r c)
    (momentumEuler G γ h r (b k)) (p k h, q k h)
  dsimp only [s, r, c] at *
  linarith

/-- Finite-horizon version, with hypotheses only on the first `n` steps. -/
theorem obabo_integral_reference_finite_bound
    (G : E → E) (L γ h η σ R P F Ξ B : ℝ)
    (hh : 0 ≤ h) (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hη : |η| ≤ 1)
    (hLip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (p q : ℕ → ℝ → E) (b : ℕ → E) (ξ : ℕ → E × E) (n : ℕ)
    (hpInt : ∀ k, k < n → IntervalIntegrable (p k) volume 0 h)
    (hfInt : ∀ k, k < n → IntervalIntegrable (fun t ↦ G (q k t) + γ • p k t) volume 0 h)
    (hp : ∀ k, k < n → p k h = p k 0 - (∫ t in 0..h, G (q k t) + γ • p k t) + b k)
    (hq : ∀ k, k < n → q k h = q k 0 + (∫ t in 0..h, p k t))
    (hcompat : ∀ k, k < n → p (k + 1) 0 = p k h ∧ q (k + 1) 0 = q k h)
    (hmod : ∀ k, k < n → ∀ t, t ∈ Set.Icc 0 h →
      ‖p k t - p k 0‖ ≤ R * Real.sqrt t ∧
      ‖q k t - q k 0‖ ≤ R * Real.sqrt t)
    (hpbound : ∀ k, k < n → ‖p k 0‖ ≤ P) (hfbound : ∀ k, k < n → ‖G (q k 0)‖ ≤ F)
    (hξbound : ∀ k, k < n → ‖(ξ k).1‖ ≤ Ξ)
    (hnoise : ∀ k, k < n → ‖σ • (η • (ξ k).1 + (ξ k).2) - b k‖ ≤ B)
    (z : E × E) :
    phaseError
      (trajectory (fun s r ↦ KineticLangevin.obaboStep G h η σ s r.1 r.2) ξ z n)
      (p n 0, q n 0) ≤
      momentumAmplification L h ^ n * phaseError z (p 0 0, q 0 0) +
        (momentumRemainderBudget L γ h η σ P F Ξ + B +
          (2 / 3 : ℝ) * (L + γ + 1) * R * h * Real.sqrt h) *
            amplificationSum (momentumAmplification L h) n := by
  have hA : 0 ≤ momentumAmplification L h := by unfold momentumAmplification; positivity
  apply finite_accumulation_upto _ _ _ hA n
  intro k hk
  dsimp only [trajectory]
  rw [(hcompat k hk).1, (hcompat k hk).2]
  let s := trajectory (fun s r ↦ KineticLangevin.obaboStep G h η σ s r.1 r.2) ξ z k
  let r : E × E := (p k 0, q k 0)
  let c := σ • (η • (ξ k).1 + (ξ k).2)
  have hs := obabo_error G L h η σ hL hη hLip s r
    (ξ k).1 (ξ k).2 (ξ k).1 (ξ k).2
  simp only [sub_self, norm_zero, mul_zero, zero_add, add_zero] at hs
  have hl := obabo_euler_error G L γ h η σ P F Ξ hL hLip r
    (ξ k).1 (ξ k).2 (hpbound k hk) (hfbound k hk) (hξbound k hk)
  have hn : phaseError (momentumEuler G γ h r c) (momentumEuler G γ h r (b k)) ≤ B := by
    rw [momentumEuler_noise_error]
    exact hnoise k hk
  have he := momentumEuler_integral_error G L γ h R hh hL hγ hLip
    (p k) (q k) (b k) (hpInt k hk) (hfInt k hk) (hp k hk) (hq k hk) (hmod k hk)
  have ht1 := phaseError_triangle
    (KineticLangevin.obaboStep G h η σ s (ξ k).1 (ξ k).2)
    (KineticLangevin.obaboStep G h η σ r (ξ k).1 (ξ k).2) (p k h, q k h)
  have ht2 := phaseError_triangle
    (KineticLangevin.obaboStep G h η σ r (ξ k).1 (ξ k).2)
    (momentumEuler G γ h r c) (p k h, q k h)
  have ht3 := phaseError_triangle (momentumEuler G γ h r c)
    (momentumEuler G γ h r (b k)) (p k h, q k h)
  dsimp only [s, r, c] at *
  linarith

end PBGSO.Methods
