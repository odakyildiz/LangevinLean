import UnadjustedLangevin.EulerLimit

set_option linter.style.header false

/-!
# Uniform control of all Euler grid points

Endpoint convergence alone does not control the accumulated weak residuals
in Dynkin's formula. These deterministic results upgrade the existing Euler
argument to simultaneous convergence at every point of the refining grid.
They apply directly in the Banach space of square-integrable random variables.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

namespace AverageLMC

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- A single compact drift modulus controls every Euler grid point. -/
theorem additiveEulerChain_grid_error_le_of_drift_modulus
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T h ε : ℝ) (hT : 0 ≤ T) (hh : 0 ≤ h) (hε : 0 ≤ ε) (n : ℕ)
    (hpartition : (n : ℝ) * h = T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (hmod : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t ≤ h →
      ‖g (Y s) - g (Y t)‖ ≤ ε) (k : ℕ) (hk : k ≤ n) :
    ‖ULA.additiveEulerChain g h x B k - Y ((k : ℝ) * h)‖ ≤
      T * ε * Real.exp ((L : ℝ) * T) := by
  have hkh : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
  have hkT : (k : ℝ) * h ≤ T := by
    rw [← hpartition]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hh
  have hb := ULA.additiveEulerChain_error_le_of_drift_modulus g L hLip x B Y hB0 hY
    ((k : ℝ) * h) h ε hkh hh hε k rfl
    (fun t ht ↦ hYe t ⟨ht.1, ht.2.trans hkT⟩)
    (fun s hs t ht hst ↦ hmod s ⟨hs.1, hs.2.trans hkT⟩ t
      ⟨ht.1, ht.2.trans hkT⟩ hst)
  apply hb.trans
  apply mul_le_mul
    (mul_le_mul_of_nonneg_right hkT hε)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkT L.coe_nonneg))
    (Real.exp_nonneg _) (mul_nonneg hT hε)

/-- Simultaneous convergence of every matching-noise Euler mesh point to the
actual integral solution. This is a theorem of the supplied integral equation,
not a convergence premise on the stochastic reference. -/
theorem additiveEulerChain_grid_uniform_tendsto
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ n + 1,
      ‖ULA.additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B k -
        Y ((k : ℝ) * (T / ((n + 1 : ℕ) : ℝ)))‖ < ε := by
  intro ε hε
  let C := T * Real.exp ((L : ℝ) * T)
  let η := ε / (C + 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hη : 0 < η := div_pos hε (by positivity)
  have hscale : η * (C + 1) = ε := div_mul_cancel₀ ε (by positivity)
  have hsmall : T * η * Real.exp ((L : ℝ) * T) < ε := by
    have he : T * η * Real.exp ((L : ℝ) * T) = C * η := by dsimp [C]; ring
    rw [he]
    nlinarith
  have huc : UniformContinuousOn (fun t ↦ g (Y t)) (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hLip.continuous.comp hY).continuousOn
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff_le.mp huc η hη
  have hmesh : Tendsto (fun n : ℕ ↦ T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat T)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmesh.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn k hk ↦ ?_⟩
  have hh : 0 ≤ T / ((n + 1 : ℕ) : ℝ) := div_nonneg hT (by positivity)
  have hpartition : (((n + 1 : ℕ) : ℝ)) * (T / ((n + 1 : ℕ) : ℝ)) = T := by field_simp
  have hb := additiveEulerChain_grid_error_le_of_drift_modulus g L hLip x B Y hB0 hY
    T (T / ((n + 1 : ℕ) : ℝ)) η hT hh hη.le (n + 1) hpartition hYe
    (fun s hs t ht hst ↦ by
      simpa only [dist_eq_norm] using hosc s hs t ht (hst.trans (hN n hn).le)) k hk
  exact hb.trans_lt hsmall

/-- Every Euler grid point in all sufficiently fine partitions lies in one
fixed norm ball. In `L²` this is the uniform second-moment bound used to sum
the weak Gaussian residuals. -/
theorem additiveEulerChain_grid_eventually_bounded
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ n + 1,
      ‖ULA.additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B k‖ ≤ R := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hY.continuousOn
  obtain ⟨N, hN⟩ := additiveEulerChain_grid_uniform_tendsto g L hLip x B Y hB0 hY T hT hYe
    1 (by norm_num)
  refine ⟨max 0 C + 1, by positivity, N, fun n hn k hk ↦ ?_⟩
  let h := T / ((n + 1 : ℕ) : ℝ)
  have hh : 0 ≤ h := div_nonneg hT (by positivity)
  have hgrid : (k : ℝ) * h ∈ Icc 0 T := by
    refine ⟨by positivity, ?_⟩
    have hkn : (k : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.mpr hk
    have he : (((n + 1 : ℕ) : ℝ)) * h = T := by dsimp [h]; field_simp
    exact (mul_le_mul_of_nonneg_right hkn hh).trans_eq he
  have hbound := norm_le_norm_sub_add (ULA.additiveEulerChain g h x B k) (Y ((k : ℝ) * h))
  have he := hN n hn k hk
  have hy := hC ((k : ℝ) * h) hgrid
  have hCmax := le_max_right (0 : ℝ) C
  dsimp [h] at hbound
  linarith

/-- The drift at every sufficiently fine Euler grid point has one uniform
norm bound, derived from the actual continuous reference and Lipschitz field.
For the lifted gradient this is a uniform score second-moment bound. -/
theorem additiveEulerChain_drift_grid_eventually_bounded
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t) :
    ∃ R : ℝ, 0 ≤ R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k ≤ n + 1,
      ‖g (ULA.additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B k)‖ ≤ R := by
  obtain ⟨R, hR, N, hN⟩ := additiveEulerChain_grid_eventually_bounded
    g L hLip x B Y hB0 hY T hT hYe
  refine ⟨(L : ℝ) * R + ‖g 0‖, by positivity, N, fun n hn k hk ↦ ?_⟩
  let z := ULA.additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B k
  have hz : ‖z‖ ≤ R := hN n hn k hk
  have hg : ‖g z - g 0‖ ≤ (L : ℝ) * ‖z‖ := by
    simpa only [sub_zero] using hLip.norm_sub_le z 0
  have hn := norm_le_norm_sub_add (g z) (g 0)
  exact hn.trans (add_le_add (hg.trans (mul_le_mul_of_nonneg_left hz L.coe_nonneg)) le_rfl)

/-- The elementary left Riemann-sum estimate on a uniform partition. -/
theorem uniform_left_sum_error_le_of_modulus
    (f : ℝ → H) (hf : Continuous f) (T h ε : ℝ)
    (hh : 0 ≤ h) (hε : 0 ≤ ε) (n : ℕ) (hpartition : (n : ℝ) * h = T)
    (hmod : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t ≤ h → ‖f s - f t‖ ≤ ε) :
    ‖(∑ k ∈ Finset.range n, h • f ((k : ℝ) * h)) - ∫ t in 0..T, f t‖ ≤ T * ε := by
  have hcell (k : ℕ) (hk : k < n) :
      ‖h • f ((k : ℝ) * h) - ∫ t in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h, f t‖ ≤ h * ε := by
    let a := (k : ℝ) * h
    let b := ((k + 1 : ℕ) : ℝ) * h
    have hab : a ≤ b := by dsimp [a, b]; push_cast; nlinarith
    have hdiff : b - a = h := by dsimp [a, b]; push_cast; ring
    have ha : a ∈ Icc 0 T := by
      refine ⟨by dsimp [a]; positivity, ?_⟩
      rw [← hpartition]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk.le) hh
    have hb : b ≤ T := by
      rw [← hpartition]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.succ_le_of_lt hk)) hh
    have he : h • f a = ∫ t in a..b, f a := by rw [intervalIntegral.integral_const, hdiff]
    change ‖h • f a - ∫ t in a..b, f t‖ ≤ _
    rw [he, ← intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable a b)]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := ε) (f := fun t ↦ f a - f t) (fun t ht ↦ ?_)
    · simpa only [hdiff, abs_of_nonneg hh, mul_comm] using hbnd
    · rw [uIoc_of_le hab] at ht
      exact hmod a ha t ⟨ha.1.trans ht.1.le, ht.2.trans hb⟩ (by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.1.le)]
        linarith [ht.2])
  have hi := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ (k : ℝ) * h) (n := n) (f := f) (μ := volume)
    (fun k _ ↦ hf.intervalIntegrable _ _)
  simp only [Nat.cast_zero, zero_mul, hpartition] at hi
  rw [← hi, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        ‖h • f ((k : ℝ) * h) -
          ∫ t in (k : ℝ) * h..((k + 1 : ℕ) : ℝ) * h, f t‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, h * ε :=
      Finset.sum_le_sum (fun k hk ↦ hcell k (Finset.mem_range.mp hk))
    _ = T * ε := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; rw [← hpartition]; ring

/-- Uniform left Riemann sums converge in every Banach target. -/
theorem uniform_left_sum_tendsto
    (f : ℝ → H) (hf : Continuous f) (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1),
      (T / ((n + 1 : ℕ) : ℝ)) • f ((k : ℝ) * (T / ((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (∫ t in 0..T, f t)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (T + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hscale : η * (T + 1) = ε := div_mul_cancel₀ ε (by positivity)
  have hsmall : T * η < ε := by nlinarith
  have huc : UniformContinuousOn f (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff_le.mp huc η hη
  have hmesh : Tendsto (fun n : ℕ ↦ T / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat T)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hmesh.eventually (gt_mem_nhds hδ))
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  apply (uniform_left_sum_error_le_of_modulus f hf T
    (T / ((n + 1 : ℕ) : ℝ)) η (by positivity) hη.le (n + 1) (by field_simp) ?_).trans_lt hsmall
  intro s hs t ht hst
  simpa only [dist_eq_norm] using hosc s hs t ht (hst.trans (hN n hn).le)

/-- Uniformly continuous observations of all Euler mesh points have the
correct time-integral limit. No pathwise differentiability is required. -/
theorem additiveEulerChain_test_sum_tendsto
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (F : H → G) (hF : UniformContinuous F) :
    Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1),
      (T / ((n + 1 : ℕ) : ℝ)) •
        F (ULA.additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B k))
      atTop (𝓝 (∫ t in 0..T, F (Y t))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / (2 * (T + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hscale : η * (2 * (T + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hsmall : T * η < ε / 2 := by nlinarith
  obtain ⟨δ, hδ, hFδ⟩ := Metric.uniformContinuous_iff.mp hF η hη
  obtain ⟨N₀, hN₀⟩ := additiveEulerChain_grid_uniform_tendsto g L hLip x B Y hB0 hY T hT hYe
    δ hδ
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp
    (uniform_left_sum_tendsto (fun t ↦ F (Y t)) (hF.continuous.comp hY) T hT)
      (ε / 2) (by positivity)
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  let h := T / ((n + 1 : ℕ) : ℝ)
  let A : G := ∑ k ∈ Finset.range (n + 1), h • F (ULA.additiveEulerChain g h x B k)
  let C : G := ∑ k ∈ Finset.range (n + 1), h • F (Y ((k : ℝ) * h))
  have hh : 0 ≤ h := div_nonneg hT (by positivity)
  have hpartition : (((n + 1 : ℕ) : ℝ)) * h = T := by dsimp [h]; field_simp
  have hsum : ‖A - C‖ ≤ T * η := by
    dsimp [A, C]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ k ∈ Finset.range (n + 1),
          ‖h • F (ULA.additiveEulerChain g h x B k) - h • F (Y ((k : ℝ) * h))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range (n + 1), h * η := by
        apply Finset.sum_le_sum
        intro k hk
        have he := hN₀ n ((le_max_left _ _).trans hn) k (Finset.mem_range.mp hk).le
        have hf := hFδ (by simpa only [dist_eq_norm] using he)
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
        exact mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hf.le) hh
      _ = T * η := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← hpartition]
        ring
  have hriem : ‖C - ∫ t in 0..T, F (Y t)‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hN₁ n ((le_max_right _ _).trans hn)
  have htriangle : ‖A - ∫ t in 0..T, F (Y t)‖ ≤
      ‖A - C‖ + ‖C - ∫ t in 0..T, F (Y t)‖ := by
    have he : A - ∫ t in 0..T, F (Y t) = (A - C) + (C - ∫ t in 0..T, F (Y t)) := by abel
    rw [he]
    exact norm_add_le _ _
  rw [dist_eq_norm]
  change ‖A - ∫ t in 0..T, F (Y t)‖ < ε
  linarith

end AverageLMC
