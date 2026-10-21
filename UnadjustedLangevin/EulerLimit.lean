import UnadjustedLangevin.LangevinIntegral
import UnadjustedLangevin.Recurrence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.UniformSpace.HeineCantor

set_option linter.style.header false

/-! # Matching-noise Euler approximation of the constructed Langevin solution

This is a deterministic Banach-space result, so it applies directly to the
constructed `L²` solution. The Euler chain uses exact increments of the same
additive input. Uniform continuity of the actual drift path controls all local
defects, and an elementary discrete Grönwall estimate proves convergence.
No Itô formula, Fokker–Planck uniqueness, or stochastic adaptedness is assumed.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

namespace ULA

section Generic

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Explicit Euler with the exact increments of one fixed additive input. -/
def additiveEulerChain (g : H → H) (h : ℝ) (x : H) (B : ℝ → H) : ℕ → H
  | 0 => x
  | k + 1 => additiveEulerChain g h x B k - h • g (additiveEulerChain g h x B k) +
      (B (((k + 1 : ℕ) : ℝ) * h) - B ((k : ℝ) * h))

omit [CompleteSpace H] in
@[simp] theorem additiveEulerChain_zero (g : H → H) (h : ℝ) (x : H) (B : ℝ → H) :
    additiveEulerChain g h x B 0 = x := rfl

omit [CompleteSpace H] in
@[simp] theorem additiveEulerChain_succ (g : H → H) (h : ℝ) (x : H) (B : ℝ → H)
    (k : ℕ) : additiveEulerChain g h x B (k + 1) =
      additiveEulerChain g h x B k - h • g (additiveEulerChain g h x B k) +
        (B (((k + 1 : ℕ) : ℝ) * h) - B ((k : ℝ) * h)) := rfl

omit [CompleteSpace H] in
/-- The global integral equation implies the exact equation between any two
nonnegative times within the horizon. -/
theorem langevin_integral_increment
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hY : Continuous Y) (T : ℝ)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (a b : ℝ) (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) :
    Y b - Y a = -(∫ s in a..b, g (Y s)) + (B b - B a) := by
  have hc : Continuous (fun s ↦ g (Y s)) := hLip.continuous.comp hY
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  have hea := hYe a ha
  have heb := hYe b hb
  rw [← hi] at heb
  rw [sub_eq_iff_eq_add] at hea heb
  rw [hea, heb]
  module

omit [NormedSpace ℝ H] [CompleteSpace H] in
/-- A noncontractive finite recurrence, with an explicit horizon bound. -/
theorem finite_euler_recurrence_bound (e : ℕ → ℝ) (q b : ℝ)
    (hq : 1 ≤ q) (hb : 0 ≤ b) (he0 : e 0 = 0) (n : ℕ)
    (hstep : ∀ k < n, e (k + 1) ≤ q * e k + b) :
    e n ≤ (n : ℝ) * b * q ^ n := by
  induction n with
  | zero => simp [he0]
  | succ n ih =>
      have hn := ih (fun k hk ↦ hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      have hp : b ≤ b * q ^ (n + 1) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hq) hb
      calc
        e (n + 1) ≤ q * e n + b := hstep n (Nat.lt_succ_self n)
        _ ≤ q * ((n : ℝ) * b * q ^ n) + b :=
          add_le_add (mul_le_mul_of_nonneg_left hn (le_trans zero_le_one hq)) le_rfl
        _ = (n : ℝ) * b * q ^ (n + 1) + b := by rw [pow_succ]; ring
        _ ≤ (n : ℝ) * b * q ^ (n + 1) + b * q ^ (n + 1) := add_le_add le_rfl hp
        _ = ((n + 1 : ℕ) : ℝ) * b * q ^ (n + 1) := by push_cast; ring

omit [CompleteSpace H] in
/-- The Euler update for a Lipschitz drift is `(1 + Lh)`-Lipschitz. -/
theorem explicitEuler_norm_sub_le (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (h : ℝ) (hh : 0 ≤ h) (x y : H) :
    ‖(x - h • g x) - (y - h • g y)‖ ≤ (1 + (L : ℝ) * h) * ‖x - y‖ := by
  have hid : (x - h • g x) - (y - h • g y) = (x - y) - h • (g x - g y) := by module
  rw [hid]
  calc
    _ ≤ ‖x - y‖ + ‖h • (g x - g y)‖ := norm_sub_le _ _
    _ = ‖x - y‖ + h * ‖g x - g y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    _ ≤ ‖x - y‖ + h * ((L : ℝ) * ‖x - y‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (hLip.norm_sub_le x y) hh)
    _ = _ := by ring

/-- Endpoint error controlled by the actual drift's modulus of continuity.
The modulus premise is discharged by compact uniform continuity below. -/
theorem additiveEulerChain_error_le_of_drift_modulus
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T h ε : ℝ) (hT : 0 ≤ T) (hh : 0 ≤ h) (hε : 0 ≤ ε) (n : ℕ)
    (hpartition : (n : ℝ) * h = T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (hmod : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t ≤ h →
      ‖g (Y s) - g (Y t)‖ ≤ ε) :
    ‖additiveEulerChain g h x B n - Y T‖ ≤ T * ε * Real.exp ((L : ℝ) * T) := by
  let X := additiveEulerChain g h x B
  let e : ℕ → ℝ := fun k ↦ ‖X k - Y ((k : ℝ) * h)‖
  have hY0 : Y 0 = x := by
    have he := hYe 0 ⟨le_rfl, hT⟩
    simpa only [intervalIntegral.integral_same, neg_zero, hB0, add_zero, sub_eq_zero] using he
  have he0 : e 0 = 0 := by simp [e, X, hY0]
  have hgrid (k : ℕ) (hk : k ≤ n) : (k : ℝ) * h ∈ Icc 0 T := by
    refine ⟨by positivity, ?_⟩
    rw [← hpartition]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hh
  have hstep (k : ℕ) (hk : k < n) :
      e (k + 1) ≤ (1 + (L : ℝ) * h) * e k + h * ε := by
    let a : ℝ := (k : ℝ) * h
    have ha : a ∈ Icc 0 T := hgrid k hk.le
    have hb : a + h ∈ Icc 0 T := by
      convert hgrid (k + 1) (Nat.succ_le_of_lt hk) using 1
      dsimp [a]
      push_cast
      ring
    let R := localDefect g (fun s ↦ Y (a + s)) h
    have hR : ‖R‖ ≤ h * ε := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := h) (C := ε) (f := fun s ↦ g (Y (a + s)) - g (Y a))
        (fun s hs ↦ ?_)
      · simpa only [R, localDefect, add_zero, sub_zero, abs_of_nonneg hh, mul_comm] using hi
      · rw [uIoc_of_le hh] at hs
        exact hmod (a + s) ⟨by linarith [ha.1, hs.1], by linarith [hb.2, hs.2]⟩ a ha
          (by simpa only [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hs.1.le] using hs.2)
    have hinc := langevin_integral_increment g L hLip x B Y hY T hYe a (a + h) ha hb
    have hinc' : Y (a + h) - Y a =
        -(∫ s in 0..h, g (Y (a + s))) + (B (a + h) - B a) := by
      have hi : (∫ s in a..a + h, g (Y s)) = ∫ s in 0..h, g (Y (a + s)) := by
        simpa only [add_zero] using (intervalIntegral.integral_comp_add_left
          (f := fun s ↦ g (Y s)) (a := 0) (b := h) a).symm
      rw [hi] at hinc
      exact hinc
    have hid := localDefect_euler_identity g (fun s ↦ Y (a + s))
      (fun s ↦ B (a + s) - B a) h
      ((hLip.continuous.comp (hY.comp (continuous_const.add continuous_id))).intervalIntegrable 0 h)
      (by simpa only [add_zero] using hinc')
    have hnext : X (k + 1) - Y (a + h) =
        ((X k - h • g (X k)) - (Y a - h • g (Y a))) + R := by
      rw [hid]
      change additiveEulerChain g h x B (k + 1) - _ = _
      rw [additiveEulerChain_succ]
      have htime : (((k + 1 : ℕ) : ℝ) * h) = a + h := by dsimp [a]; push_cast; ring
      rw [htime]
      dsimp [R, a, X]
      simp only [add_zero]
      module
    change ‖X (k + 1) - Y (((k + 1 : ℕ) : ℝ) * h)‖ ≤ _
    rw [show (((k + 1 : ℕ) : ℝ) * h) = a + h by dsimp [a]; push_cast; ring, hnext]
    exact (norm_add_le _ _).trans
      (add_le_add (explicitEuler_norm_sub_le g L hLip h hh (X k) (Y a)) hR)
  have he := finite_euler_recurrence_bound e (1 + (L : ℝ) * h) (h * ε)
    (by linarith [mul_nonneg L.coe_nonneg hh]) (mul_nonneg hh hε) he0 n hstep
  have hpow : (1 + (L : ℝ) * h) ^ n ≤ Real.exp ((L : ℝ) * T) := by
    calc
      _ ≤ Real.exp ((L : ℝ) * h) ^ n :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ((L : ℝ) * h)]) n
      _ = Real.exp ((n : ℝ) * ((L : ℝ) * h)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp ((L : ℝ) * T) := by rw [← hpartition]; congr 1; ring
  calc
    _ = e n := by simp only [e, X, hpartition]
    _ ≤ (n : ℝ) * (h * ε) * (1 + (L : ℝ) * h) ^ n := he
    _ ≤ (n : ℝ) * (h * ε) * Real.exp ((L : ℝ) * T) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = T * ε * Real.exp ((L : ℝ) * T) := by rw [← hpartition]; ring

/-- Matching-noise explicit Euler converges to every continuous additive
integral solution, on the uniform mesh `T/(n+1)`, at its exact endpoint.
The only drift assumption is global Lipschitz continuity. -/
theorem additiveEulerChain_tendsto
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t) :
    Tendsto (fun n : ℕ ↦ additiveEulerChain g (T / ((n + 1 : ℕ) : ℝ)) x B (n + 1))
      atTop (𝓝 (Y T)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let C : ℝ := T * Real.exp ((L : ℝ) * T)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let η : ℝ := ε / (C + 1)
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
  refine ⟨N, fun n hn ↦ ?_⟩
  have hh : 0 ≤ T / ((n + 1 : ℕ) : ℝ) := div_nonneg hT (by positivity)
  have hpartition : (((n + 1 : ℕ) : ℝ)) * (T / ((n + 1 : ℕ) : ℝ)) = T := by
    field_simp
  have hbound := additiveEulerChain_error_le_of_drift_modulus g L hLip x B Y hB0 hY
    T (T / ((n + 1 : ℕ) : ℝ)) η hT hh hη.le (n + 1) hpartition hYe
    (fun s hs t ht hst ↦ by
      simpa only [dist_eq_norm] using hosc s hs t ht (hst.trans (hN n hn).le))
  rw [dist_eq_norm]
  exact lt_of_le_of_lt hbound hsmall

end Generic

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- In particular, the already constructed `L²` Langevin solution is the limit
of matching-noise Euler approximations. No stochastic-calculus premise occurs. -/
theorem lp_langevin_integral_euler_tendsto
    (U : H → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp H 2 P) (B Y : ℝ → Lp H 2 P)
    (hB0 : B 0 = 0) (hY : Continuous Y) (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) + B t) :
    Tendsto (fun n : ℕ ↦ additiveEulerChain (lpDrift P (gradient U) hLip)
      (T / ((n + 1 : ℕ) : ℝ)) initial B (n + 1)) atTop (𝓝 (Y T)) :=
  additiveEulerChain_tendsto (lpDrift P (gradient U) hLip) L
    (lpDrift_lipschitz P (gradient U) hLip) initial B Y hB0 hY T hT hYe

end ULA
