import AverageLMC.Recurrence

set_option linter.style.header false

/-!
# Conditional scalar iteration bounds for averaged LMC

This file resolves the normalized one-step recurrence, including Proposition 1's
warmup, decreasing steps and ceiling in its iteration count. It has no
stochastic conclusion without the
one-step recurrence supplied as an explicit hypothesis.
-/

namespace AverageLMC

/-- The `log_+` convention used by the paper. -/
noncomputable def positiveLog (x : ℝ) : ℝ := max (Real.log x) 0

/-- The exact warmup length in Proposition 1, with `a = κav + 1`. -/
noncomputable def warmup (κ a ε₀ : ℝ) : ℕ :=
  ⌈κ / 2 * positiveLog (2 * κ * ε₀ ^ 2 / a)⌉₊

/-- The dimensionless form `m h_k` of Proposition 1's schedule. -/
noncomputable def variableStep (κ : ℝ) (k₀ k : ℕ) : ℝ :=
  1 / (κ + ((k - k₀ : ℕ) : ℝ))

/-- The proposed schedule always respects the maximal smoothness restriction. -/
theorem variableStep_le {κ : ℝ} (hκ : 0 < κ) (k₀ k : ℕ) :
    0 < variableStep κ k₀ k ∧ variableStep κ k₀ k ≤ 1 / κ := by
  have hn := Nat.cast_nonneg (α := ℝ) (k - k₀)
  constructor
  · unfold variableStep
    positivity
  · unfold variableStep
    exact one_div_le_one_div_of_le hκ (by linarith)

/-- The ceiling chosen in the paper reduces the initial-error term by the
required factor, including the case where the positive logarithm is zero. -/
theorem warmup_decay {κ a ε₀ : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hε₀ : 0 < ε₀) :
    Real.exp (-2 * (warmup κ a ε₀ : ℝ) / κ) * ε₀ ^ 2 ≤ a / (2 * κ) := by
  have hr : 0 < 2 * κ * ε₀ ^ 2 / a := by positivity
  have hc : κ / 2 * positiveLog (2 * κ * ε₀ ^ 2 / a) ≤
      (warmup κ a ε₀ : ℝ) := Nat.le_ceil _
  have hl : Real.log (2 * κ * ε₀ ^ 2 / a) ≤ positiveLog (2 * κ * ε₀ ^ 2 / a) :=
    le_max_left _ _
  have hexp : -2 * (warmup κ a ε₀ : ℝ) / κ ≤
      -Real.log (2 * κ * ε₀ ^ 2 / a) := by
    apply (div_le_iff₀ hκ).2
    nlinarith
  calc
    _ ≤ Real.exp (-Real.log (2 * κ * ε₀ ^ 2 / a)) * ε₀ ^ 2 :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (sq_nonneg _)
    _ = a / (2 * κ) := by
      rw [Real.exp_neg, Real.exp_log hr]
      field_simp

/-- Proposition 1, for the normalized scalar error and its explicit recurrence. -/
theorem variable_step_normalized (r : ℕ → ℝ) (a κ ε₀ : ℝ)
    (ha : 0 < a) (hκ : 1 ≤ κ) (hε₀ : 0 < ε₀)
    (hr0 : 0 ≤ r 0) (hinit : r 0 ≤ ε₀ ^ 2)
    (hstep : ∀ k, r (k + 1) ≤
      (1 - variableStep κ (warmup κ a ε₀) k) /
        (1 + variableStep κ (warmup κ a ε₀) k) * r k +
      a * variableStep κ (warmup κ a ε₀) k ^ 2 /
        (1 + variableStep κ (warmup κ a ε₀) k))
    (k : ℕ) (hk : warmup κ a ε₀ ≤ k) :
    r k ≤ a / (κ + ((k - warmup κ a ε₀ : ℕ) : ℝ)) := by
  let k₀ := warmup κ a ε₀
  have hκ0 : 0 < κ := by linarith
  have hfirst := constant_step_normalized_up_to r a (1 / κ) ha.le
    (by positivity) ((div_le_one hκ0).mpr hκ) hr0 k₀ (by
      intro j hj
      have hj0 : j - k₀ = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hj)
      change j - warmup κ a ε₀ = 0 at hj0
      simpa only [variableStep, hj0, Nat.cast_zero, add_zero] using hstep j)
  have hdecay := warmup_decay hκ0 ha hε₀
  have heq : -2 * (1 / κ) * (k₀ : ℝ) = -2 * (k₀ : ℝ) / κ := by ring
  rw [heq] at hfirst
  have hmul := mul_le_mul_of_nonneg_left hinit (Real.exp_nonneg (-2 * (k₀ : ℝ) / κ))
  have hwarm : r k₀ ≤ a / κ := by
    change Real.exp (-2 * (k₀ : ℝ) / κ) * ε₀ ^ 2 ≤ a / (2 * κ) at hdecay
    have heq₂ : a * (1 / κ) / 2 = a / (2 * κ) := by ring
    rw [heq₂] at hfirst
    have hadd : a / (2 * κ) + a / (2 * κ) = a / κ := by ring
    linarith
  have htail := variable_step_tail (fun n ↦ r (k₀ + n)) a κ ha.le hκ
    (by simpa using hwarm) (by
      intro n
      have heq₃ : (k₀ + n - warmup κ a ε₀ : ℕ) = n := by
        dsimp only [k₀]
        omega
      simpa only [variableStep, heq₃, Nat.add_assoc] using hstep (k₀ + n)) (k - k₀)
  change k₀ ≤ k at hk
  change r k ≤ a / (κ + ((k - k₀ : ℕ) : ℝ))
  simpa only [Nat.add_sub_of_le hk] using htail

/-- The exact number of iterations in Proposition 1. -/
noncomputable def variableIterations (κ a ε₀ ε : ℝ) : ℕ :=
  warmup κ a ε₀ + ⌈max (a / ε ^ 2 - κ) 0⌉₊

/-- The ceiling in Proposition 1 ensures that its error envelope is at most
`ε²`. This is purely the arithmetic of the iteration count. -/
theorem variable_iterations_envelope {κ a ε₀ ε : ℝ}
    (hκ : 0 < κ) (_ha : 0 < a) (hε : 0 < ε)
    {k : ℕ} (hk : variableIterations κ a ε₀ ε ≤ k) :
    warmup κ a ε₀ ≤ k ∧
      a / (κ + ((k - warmup κ a ε₀ : ℕ) : ℝ)) ≤ ε ^ 2 := by
  have hk₀ : warmup κ a ε₀ ≤ k := by
    unfold variableIterations at hk
    omega
  have hnat : ⌈max (a / ε ^ 2 - κ) 0⌉₊ ≤ k - warmup κ a ε₀ := by
    unfold variableIterations at hk
    omega
  have hc : max (a / ε ^ 2 - κ) 0 ≤ ((k - warmup κ a ε₀ : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hnat)
  have hden : 0 < κ + ((k - warmup κ a ε₀ : ℕ) : ℝ) := by positivity
  refine ⟨hk₀, (div_le_iff₀ hden).2 ?_⟩
  have h := (le_max_left (a / ε ^ 2 - κ) 0).trans hc
  have he : 0 < ε ^ 2 := by positivity
  have hq : a / ε ^ 2 ≤ κ + ((k - warmup κ a ε₀ : ℕ) : ℝ) := by linarith
  have := (div_le_iff₀ he).1 hq
  nlinarith

/-- The accuracy consequence of the scalar Proposition 1. -/
theorem variable_step_accuracy (r : ℕ → ℝ) (a κ ε₀ ε : ℝ)
    (ha : 0 < a) (hκ : 1 ≤ κ) (hε₀ : 0 < ε₀) (hε : 0 < ε)
    (hr0 : 0 ≤ r 0) (hinit : r 0 ≤ ε₀ ^ 2)
    (hstep : ∀ k, r (k + 1) ≤
      (1 - variableStep κ (warmup κ a ε₀) k) /
        (1 + variableStep κ (warmup κ a ε₀) k) * r k +
      a * variableStep κ (warmup κ a ε₀) k ^ 2 /
        (1 + variableStep κ (warmup κ a ε₀) k))
    (k : ℕ) (hk : variableIterations κ a ε₀ ε ≤ k) : r k ≤ ε ^ 2 := by
  have he := variable_iterations_envelope (by linarith) ha hε hk
  exact (variable_step_normalized r a κ ε₀ ha hκ hε₀ hr0 hinit hstep k he.1).trans he.2

end AverageLMC
