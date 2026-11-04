import WassersteinMixing.Complexity

set_option linter.style.header false

/-! # Exact scaling and accuracy arithmetic for the IPLA application

The Wasserstein bias is linear in the IPLA step after the particle/time
rescaling. These scalar lemmas do not postulate a stochastic comparison:
the actual-law application supplies that bound separately.
-/

noncomputable section

namespace WassersteinMixing

/-- The dimension remaining after the particle/time rescaling. -/
def iplaEffectiveDimension (N dθ dx : ℕ) : ℝ :=
  (dx : ℝ) + (dθ : ℝ) / N

/-- The sharp linear-step discretization term after the IPLA lift. -/
def iplaLinearBias (m L γ D : ℝ) : ℝ :=
  6 * γ * Real.sqrt ((L / m) * L * D)

/-- The square-root-step discretization term in Project 03. -/
def iplaProject03Bias (m L γ D : ℝ) : ℝ :=
  (33 / 20 : ℝ) * (L / m) * Real.sqrt D * Real.sqrt γ

/-- A normalized-accuracy step, positive for positive smoothness, including dimension zero. -/
def iplaAccuracyStep (L D ε : ℝ) : ℝ :=
  1 / (L * max 1 (18 * Real.sqrt D / ε))

/-- Reciprocal of the dimensionless IPLA step. -/
def iplaAccuracyPrefactor (m L D ε : ℝ) : ℝ :=
  (L / m) * max 1 (18 * Real.sqrt D / ε)

/-- A conservative step for the coarser doubled-bias, exact-target estimate. -/
def iplaTargetAccuracyStep (L D ε : ℝ) : ℝ :=
  iplaAccuracyStep L D (ε / 2)

/-- The iteration prefactor for the conservative doubled-bias estimate. -/
def iplaTargetAccuracyPrefactor (m L D ε : ℝ) : ℝ :=
  iplaAccuracyPrefactor m L D (ε / 2)

theorem iplaEffectiveDimension_nonneg (N dθ dx : ℕ) :
    0 ≤ iplaEffectiveDimension N dθ dx := by
  unfold iplaEffectiveDimension
  positivity

/-- The factors in the lifted bias cancel exactly, including the particle number. -/
theorem ipla_lifted_bias_eq (N dθ dx : ℕ) (hN : 0 < N) (m L γ : ℝ) :
    6 * (γ / (N : ℝ)) *
      Real.sqrt ((((N : ℝ) * L) / ((N : ℝ) * m)) *
        ((N : ℝ) * L) * (dθ + N * dx : ℕ)) =
      iplaLinearBias m L γ (iplaEffectiveDimension N dθ dx) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [mul_div_mul_left _ _ hn.ne']
  have heq : (L / m) * ((N : ℝ) * L) * (dθ + N * dx : ℕ) =
      (N : ℝ) ^ 2 * ((L / m) * L * iplaEffectiveDimension N dθ dx) := by
    unfold iplaEffectiveDimension
    push_cast
    field_simp
    ring
  rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn.le]
  unfold iplaLinearBias
  field_simp

/-- Multiplication by the square root of strong convexity removes its scale. -/
theorem ipla_linear_bias_scale (m L γ D : ℝ) (hm : 0 < m)
    (hL : 0 ≤ L) (hD : 0 ≤ D) :
    Real.sqrt m * iplaLinearBias m L γ D = 6 * L * γ * Real.sqrt D := by
  have hs := sqrt_curvature_scale m L D hm hL hD
  unfold iplaLinearBias
  calc
    _ = 6 * γ * (Real.sqrt m * Real.sqrt ((L / m) * L * D)) := by ring
    _ = _ := by rw [hs]; ring

/-- The same normalization removes strong convexity from the equilibrium radius. -/
theorem ipla_concentration_scale (N dθ : ℕ) (hN : 0 < N) (m : ℝ) (hm : 0 < m) :
    Real.sqrt m * Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m)) =
      Real.sqrt (2 * (dθ : ℝ) / N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.sqrt_mul hm.le]
  congr 1
  field_simp

theorem iplaAccuracyStep_pos (L D ε : ℝ) (hL : 0 < L) :
    0 < iplaAccuracyStep L D ε := by
  unfold iplaAccuracyStep
  exact one_div_pos.mpr (mul_pos hL (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

theorem iplaAccuracyStep_mul_L_le (L D ε : ℝ) (hL : 0 < L) :
    iplaAccuracyStep L D ε * L ≤ 1 := by
  have hM : 0 < max 1 (18 * Real.sqrt D / ε) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have heq : iplaAccuracyStep L D ε * L = 1 / max 1 (18 * Real.sqrt D / ε) := by
    unfold iplaAccuracyStep
    field_simp
  rw [heq]
  exact (div_le_one hM).mpr (le_max_left _ _)

/-- The step and iteration prefactor are exact reciprocals. -/
theorem ipla_step_mul_prefactor (m L D ε : ℝ) (hm : 0 < m) (hL : 0 < L) :
    (m * iplaAccuracyStep L D ε) * iplaAccuracyPrefactor m L D ε = 1 := by
  have hM : max 1 (18 * Real.sqrt D / ε) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  unfold iplaAccuracyStep iplaAccuracyPrefactor
  field_simp

/-- A third of the accuracy is reserved for the sharp stationary bias. -/
theorem ipla_step_bias_budget (m L D ε : ℝ) (hm : 0 < m) (hL : 0 < L)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    Real.sqrt m * iplaLinearBias m L (iplaAccuracyStep L D ε) D ≤ ε / 3 := by
  rw [ipla_linear_bias_scale m L _ D hm hL.le hD]
  have hM : 0 < max 1 (18 * Real.sqrt D / ε) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb : 18 * Real.sqrt D ≤ ε * max 1 (18 * Real.sqrt D / ε) := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp
      (le_max_right (1 : ℝ) (18 * Real.sqrt D / ε))
  have heq : 6 * L * iplaAccuracyStep L D ε * Real.sqrt D =
      6 * Real.sqrt D / max 1 (18 * Real.sqrt D / ε) := by
    unfold iplaAccuracyStep
    field_simp
  rw [heq]
  apply (div_le_iff₀ hM).mpr
  nlinarith

/-- The exact particle-number budget for a third of normalized RMS error. -/
theorem ipla_concentration_budget (N dθ : ℕ) (hN : 0 < N) (ε : ℝ) (hε : 0 < ε)
    (hparticles : 18 * (dθ : ℝ) ≤ (N : ℝ) * ε ^ 2) :
    Real.sqrt (2 * (dθ : ℝ) / (N : ℝ)) ≤ ε / 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  apply (div_le_iff₀ hn).mpr
  nlinarith

/-- The selected logarithmic iteration count gives a third of normalized error. -/
theorem ipla_transient_budget (m L D R ε : ℝ) (hm : 0 < m)
    (hmL : m ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) (k : ℕ)
    (hk : iplaAccuracyPrefactor m L D ε *
      Real.log (1 + 3 * Real.sqrt m * R / ε) ≤ (k : ℝ)) :
    Real.sqrt m * ((1 - m * iplaAccuracyStep L D ε) ^ k * R) ≤ ε / 3 := by
  have hL : 0 < L := hm.trans_le hmL
  have hγ := iplaAccuracyStep_pos L D ε hL
  have ht : 0 < m * iplaAccuracyStep L D ε := mul_pos hm hγ
  have ht1 : m * iplaAccuracyStep L D ε ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hmL hγ.le
    linarith [iplaAccuracyStep_mul_L_le L D ε hL]
  have hi := ipla_step_mul_prefactor m L D ε hm hL
  have hlog : Real.log (1 + 2 * (Real.sqrt m * R) / (2 * ε / 3)) ≤
      (m * iplaAccuracyStep L D ε) * k := by
    have h := mul_le_mul_of_nonneg_left hk ht.le
    rw [← mul_assoc, hi, one_mul] at h
    convert h using 1
    congr 1
    field_simp
  have h := geometric_transient_le (m * iplaAccuracyStep L D ε)
    (Real.sqrt m * R) (2 * ε / 3) ht ht1 (by positivity) (by positivity) k hlog
  nlinarith

/-- Explicit accuracy arithmetic for the actual IPLA parameter bound. -/
theorem ipla_accuracy_arithmetic (N dθ : ℕ) (hN : 0 < N) (m L D R ε : ℝ)
    (hm : 0 < m) (hmL : m ≤ L) (hD : 0 ≤ D) (hR : 0 ≤ R) (hε : 0 < ε)
    (hparticles : 18 * (dθ : ℝ) ≤ (N : ℝ) * ε ^ 2) (k : ℕ)
    (hk : iplaAccuracyPrefactor m L D ε *
      Real.log (1 + 3 * Real.sqrt m * R / ε) ≤ (k : ℝ)) :
    Real.sqrt (2 * (dθ : ℝ) / (N : ℝ)) +
      Real.sqrt m * ((1 - m * iplaAccuracyStep L D ε) ^ k * R +
        iplaLinearBias m L (iplaAccuracyStep L D ε) D) ≤ ε := by
  have hc := ipla_concentration_budget N dθ hN ε hε hparticles
  have ht := ipla_transient_budget m L D R ε hm hmL hR hε k hk
  have hb := ipla_step_bias_budget m L D ε hm (hm.trans_le hmL) hD hε
  nlinarith

/-- The conservative doubled-bias step has coefficient thirty-six. -/
theorem iplaTargetAccuracyStep_eq (L D ε : ℝ) :
    iplaTargetAccuracyStep L D ε =
      1 / (L * max 1 (36 * Real.sqrt D / ε)) := by
  unfold iplaTargetAccuracyStep iplaAccuracyStep
  congr 3
  field_simp
  ring

/-- The conservative doubled-bias iteration prefactor has coefficient thirty-six. -/
theorem iplaTargetAccuracyPrefactor_eq (m L D ε : ℝ) :
    iplaTargetAccuracyPrefactor m L D ε =
      (L / m) * max 1 (36 * Real.sqrt D / ε) := by
  unfold iplaTargetAccuracyPrefactor iplaAccuracyPrefactor
  congr 2
  field_simp
  ring

/-- The target-based initialization has the same logarithmic transient budget. -/
theorem ipla_target_transient_budget (m L D R ε : ℝ) (hm : 0 < m)
    (hmL : m ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) (k : ℕ)
    (hk : iplaTargetAccuracyPrefactor m L D ε *
      Real.log (1 + 3 * Real.sqrt m * R / ε) ≤ (k : ℝ)) :
    Real.sqrt m * ((1 - m * iplaTargetAccuracyStep L D ε) ^ k * R) ≤ ε / 3 := by
  have hL : 0 < L := hm.trans_le hmL
  have hγ := iplaAccuracyStep_pos L D (ε / 2) hL
  have ht : 0 < m * iplaAccuracyStep L D (ε / 2) := mul_pos hm hγ
  have ht1 : m * iplaAccuracyStep L D (ε / 2) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hmL hγ.le
    linarith [iplaAccuracyStep_mul_L_le L D (ε / 2) hL]
  have hi := ipla_step_mul_prefactor m L D (ε / 2) hm hL
  have hlog : Real.log (1 + 2 * (Real.sqrt m * R) / (2 * ε / 3)) ≤
      (m * iplaAccuracyStep L D (ε / 2)) * k := by
    have h := mul_le_mul_of_nonneg_left hk ht.le
    unfold iplaTargetAccuracyPrefactor at h
    rw [← mul_assoc, hi, one_mul] at h
    convert h using 1
    congr 1
    field_simp
  have h := geometric_transient_le (m * iplaAccuracyStep L D (ε / 2))
    (Real.sqrt m * R) (2 * ε / 3) ht ht1 (by positivity) (by positivity) k hlog
  unfold iplaTargetAccuracyStep
  nlinarith

/-- Explicit normalized accuracy using the same target-based initialization as Project 03. -/
theorem ipla_accuracy_target_arithmetic (N dθ : ℕ) (hN : 0 < N) (m L D R ε : ℝ)
    (hm : 0 < m) (hmL : m ≤ L) (hD : 0 ≤ D) (hR : 0 ≤ R) (hε : 0 < ε)
    (hparticles : 18 * (dθ : ℝ) ≤ (N : ℝ) * ε ^ 2) (k : ℕ)
    (hk : iplaTargetAccuracyPrefactor m L D ε *
      Real.log (1 + 3 * Real.sqrt m * R / ε) ≤ (k : ℝ)) :
    Real.sqrt (2 * (dθ : ℝ) / (N : ℝ)) +
      Real.sqrt m * ((1 - m * iplaTargetAccuracyStep L D ε) ^ k * R +
        2 * iplaLinearBias m L (iplaTargetAccuracyStep L D ε) D) ≤ ε := by
  have hc := ipla_concentration_budget N dθ hN ε hε hparticles
  have ht := ipla_target_transient_budget m L D R ε hm hmL hR hε k hk
  have hb := ipla_step_bias_budget m L D (ε / 2) hm (hm.trans_le hmL) hD
    (by positivity)
  unfold iplaTargetAccuracyStep at ht ⊢
  nlinarith

/-- The exact step regime in which the new scalar coefficient improves the old one. -/
theorem ipla_bias_coefficient_le_old (m γ : ℝ) (hm : 0 < m) (hγ : 0 ≤ γ)
    (hsmall : m * γ ≤ (121 / 1600 : ℝ)) :
    6 * γ * Real.sqrt m ≤ (33 / 20 : ℝ) * Real.sqrt γ := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt hm.le, Real.sq_sqrt hγ]
  have h := mul_le_mul_of_nonneg_right hsmall hγ
  nlinarith

/-- The doubled bias used for the original-target initialization has an explicit regime too. -/
theorem ipla_doubled_bias_coefficient_le_old (m γ : ℝ) (hm : 0 < m) (hγ : 0 ≤ γ)
    (hsmall : m * γ ≤ (121 / 6400 : ℝ)) :
    12 * γ * Real.sqrt m ≤ (33 / 20 : ℝ) * Real.sqrt γ := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt hm.le, Real.sq_sqrt hγ]
  have h := mul_le_mul_of_nonneg_right hsmall hγ
  nlinarith

/-- Factorization in the form shared with the old IPLA discretization bound. -/
theorem ipla_linear_bias_factorization (m L γ D : ℝ) (hm : 0 < m)
    (hL : 0 ≤ L) (hD : 0 ≤ D) :
    iplaLinearBias m L γ D =
      (6 * γ * Real.sqrt m) * ((L / m) * Real.sqrt D) := by
  have hs : Real.sqrt ((L / m) * L * D) =
      (L / m) * Real.sqrt m * Real.sqrt D := by
    apply mul_left_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hm))
    rw [sqrt_curvature_scale m L D hm hL hD]
    calc
      L * Real.sqrt D = (L / m) * m * Real.sqrt D := by field_simp
      _ = (L / m) * (Real.sqrt m * Real.sqrt m) * Real.sqrt D := by
        rw [Real.mul_self_sqrt hm.le]
      _ = _ := by ring
  unfold iplaLinearBias
  rw [hs]
  ring

/-- With matching invariant-law initialization, the new discretization term is smaller
than Project 03's term throughout the stated step regime. -/
theorem ipla_linear_bias_le_project03 (m L γ D : ℝ) (hm : 0 < m)
    (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hD : 0 ≤ D)
    (hsmall : m * γ ≤ (121 / 1600 : ℝ)) :
    iplaLinearBias m L γ D ≤ iplaProject03Bias m L γ D := by
  rw [ipla_linear_bias_factorization m L γ D hm hL hD]
  have h := mul_le_mul_of_nonneg_right
    (ipla_bias_coefficient_le_old m γ hm hγ hsmall)
    (show 0 ≤ (L / m) * Real.sqrt D by positivity)
  unfold iplaProject03Bias
  nlinarith

/-- The coarser invariant-triangle argument uses twice the bias; even this
weaker estimate improves Project 03 for sufficiently small steps. The sharp
target-initialization bound retains a single copy of the bias. -/
theorem ipla_doubled_bias_le_project03 (m L γ D : ℝ) (hm : 0 < m)
    (hL : 0 ≤ L) (hγ : 0 ≤ γ) (hD : 0 ≤ D)
    (hsmall : m * γ ≤ (121 / 6400 : ℝ)) :
    2 * iplaLinearBias m L γ D ≤ iplaProject03Bias m L γ D := by
  rw [ipla_linear_bias_factorization m L γ D hm hL hD]
  have h := mul_le_mul_of_nonneg_right
    (ipla_doubled_bias_coefficient_le_old m γ hm hγ hsmall)
    (show 0 ≤ (L / m) * Real.sqrt D by positivity)
  unfold iplaProject03Bias
  nlinarith

end WassersteinMixing
