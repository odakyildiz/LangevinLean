import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option linter.style.header false

/-! # The paper's explicit scale-invariant iteration complexity

These are scalar implications of the paper's mixing estimate.  They do not
assert the existence of the invariant distribution or the mixing estimate.
-/

noncomputable section

namespace WassersteinMixing

/-- The step selected in Corollary 1.1. -/
def paperStep (β d ε : ℝ) : ℝ :=
  (1 / β) * min 1 (ε / (12 * Real.sqrt d))

/-- The prefactor multiplying the logarithm in the paper's iteration count. -/
def iterationPrefactor (α β d ε : ℝ) : ℝ :=
  (β / α) * max 1 (12 * Real.sqrt d / ε)

/-- Reciprocal form of the selected step. -/
theorem paperStep_eq_inv (β d ε : ℝ) (hβ : 0 < β) (hd : 0 < d) (hε : 0 < ε) :
    paperStep β d ε = 1 / (β * max 1 (12 * Real.sqrt d / ε)) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  by_cases hc : ε ≤ 12 * Real.sqrt d
  · have hmin : ε / (12 * Real.sqrt d) ≤ 1 :=
      (div_le_one (by positivity)).mpr hc
    have hmax : 1 ≤ 12 * Real.sqrt d / ε := (one_le_div hε).mpr hc
    rw [paperStep, min_eq_right hmin, max_eq_right hmax]
    field_simp
  · have hlarge : 12 * Real.sqrt d ≤ ε := le_of_lt (lt_of_not_ge hc)
    have hmin : 1 ≤ ε / (12 * Real.sqrt d) :=
      (one_le_div (by positivity)).mpr hlarge
    have hmax : 12 * Real.sqrt d / ε ≤ 1 := (div_le_one hε).mpr hlarge
    simp [paperStep, min_eq_left hmin, max_eq_left hmax]

/-- The selected step is positive. -/
theorem paperStep_pos (β d ε : ℝ) (hβ : 0 < β) (hd : 0 < d) (hε : 0 < ε) :
    0 < paperStep β d ε := by
  rw [paperStep_eq_inv β d ε hβ hd hε]
  positivity

/-- The selected step satisfies the paper's stability restriction. -/
theorem paperStep_le_inv_beta (β d ε : ℝ) (hβ : 0 < β) (_hd : 0 < d) (_hε : 0 < ε) :
    paperStep β d ε ≤ 1 / β := by
  unfold paperStep
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_eq (mul_one _)

/-- The iteration prefactor is the reciprocal of the dimensionless step. -/
theorem step_mul_iterationPrefactor (α β d ε : ℝ) (hα : 0 < α)
    (hβ : 0 < β) (hd : 0 < d) (hε : 0 < ε) :
    (α * paperStep β d ε) * iterationPrefactor α β d ε = 1 := by
  rw [paperStep_eq_inv β d ε hβ hd hε, iterationPrefactor]
  have hm : max 1 (12 * Real.sqrt d / ε) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  field_simp

/-- Curvature scaling cancels exactly in the scale-invariant bias. -/
theorem sqrt_curvature_scale (α β d : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) (hd : 0 ≤ d) :
    Real.sqrt α * Real.sqrt ((β / α) * β * d) = β * Real.sqrt d := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt hα.le, Real.sq_sqrt (by positivity), Real.sq_sqrt hd]
  field_simp

/-- Half of the requested accuracy is reserved for the stationary bias. -/
theorem paperStep_bias_le (α β d ε : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hd : 0 < d) (hε : 0 < ε) :
    Real.sqrt α * (6 * paperStep β d ε * Real.sqrt ((β / α) * β * d)) ≤ ε / 2 := by
  have hm : 0 < max 1 (12 * Real.sqrt d / ε) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbound : 12 * Real.sqrt d ≤ ε * max 1 (12 * Real.sqrt d / ε) := by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp
      (le_max_right (1 : ℝ) (12 * Real.sqrt d / ε))
  calc
    _ = 6 * paperStep β d ε * (β * Real.sqrt d) := by
      rw [← sqrt_curvature_scale α β d hα hβ.le hd.le]
      ring
    _ = 6 * Real.sqrt d / max 1 (12 * Real.sqrt d / ε) := by
      rw [paperStep_eq_inv β d ε hβ hd hε]
      field_simp
    _ ≤ ε / 2 := by
      apply (div_le_iff₀ hm).mpr
      nlinarith

/-- A logarithmic iteration count controls a geometric transient, including
zero initial error and the boundary contraction factor zero. -/
theorem geometric_transient_le (t A ε : ℝ) (_ht : 0 < t) (ht1 : t ≤ 1)
    (hA : 0 ≤ A) (hε : 0 < ε) (k : ℕ)
    (hk : Real.log (1 + 2 * A / ε) ≤ t * k) :
    (1 - t) ^ k * A ≤ ε / 2 := by
  have hq : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hpow : (1 - t) ^ k ≤ Real.exp (-t * k) := by
    have hbase : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
    have hp := pow_le_pow_left₀ hq hbase k
    rw [← Real.exp_nat_mul] at hp
    convert hp using 1
    congr 1
    ring
  have harg : 0 < 1 + 2 * A / ε := by positivity
  have hexp : Real.exp (-t * k) ≤ 1 / (1 + 2 * A / ε) := by
    rw [one_div, ← Real.exp_log harg, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hquot : (1 / (1 + 2 * A / ε)) * A ≤ ε / 2 := by
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ harg).mpr
    have hcancel : (2 * A / ε) * ε = 2 * A := div_mul_cancel₀ _ (ne_of_gt hε)
    nlinarith
  exact (mul_le_mul_of_nonneg_right (hpow.trans hexp) hA).trans hquot

/-- The exact scalar implication in Corollary 1.1: the stated step and
iteration count make the displayed scale-invariant mixing bound at most ε. -/
theorem paper_complexity_bound (α β d R ε : ℝ) (hα : 0 < α) (hαβ : α ≤ β)
    (hd : 0 < d) (hR : 0 ≤ R) (hε : 0 < ε) (k : ℕ)
    (hk : iterationPrefactor α β d ε *
      Real.log (1 + 2 * Real.sqrt α * R / ε) ≤ (k : ℝ)) :
    Real.sqrt α * ((1 - α * paperStep β d ε) ^ k * R +
      6 * paperStep β d ε * Real.sqrt ((β / α) * β * d)) ≤ ε := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hh := paperStep_pos β d ε hβ hd hε
  have ht : 0 < α * paperStep β d ε := mul_pos hα hh
  have ht1 : α * paperStep β d ε ≤ 1 := by
    have hb := paperStep_le_inv_beta β d ε hβ hd hε
    have hm := mul_le_mul_of_nonneg_right hαβ hh.le
    have hn := mul_le_mul_of_nonneg_left hb hβ.le
    have hid : β * (1 / β) = 1 := mul_one_div_cancel (ne_of_gt hβ)
    nlinarith
  have hi := step_mul_iterationPrefactor α β d ε hα hβ hd hε
  have hlog : Real.log (1 + 2 * (Real.sqrt α * R) / ε) ≤
      (α * paperStep β d ε) * k := by
    have hx := mul_le_mul_of_nonneg_left hk ht.le
    rw [← mul_assoc, hi, one_mul] at hx
    simpa only [mul_assoc] using hx
  have htrans := geometric_transient_le (α * paperStep β d ε) (Real.sqrt α * R)
    ε ht ht1 (by positivity) hε k hlog
  have hbias := paperStep_bias_le α β d ε hα hβ hd hε
  nlinarith

end WassersteinMixing
