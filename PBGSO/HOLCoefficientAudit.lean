import PBGSO.HigherOrderMethod
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A checked correction to the higher-order coefficient interpretation

The printed affine coefficients define a numerical method, but they are not
the exact matrix exponential of the force-free higher-order subsystem. For
alpha=gamma=1, a necessary fundamental-matrix identity would be
mu22'=mu32. At h=1 the two sides differ. This does not invalidate the
implementation or the proved numerical error budgets.
-/

noncomputable section
namespace PBGSO.Methods

/-- Exact derivative of the printed mu22 coefficient at unit parameters. -/
theorem hol_mu22_unit_hasDeriv (t : ℝ) :
    HasDerivAt (fun h : ℝ => (holCoefficients 1 1 h).μ22)
      (-1 + Real.exp (-t)) t := by
  have he : HasDerivAt (fun h : ℝ => Real.exp (-h)) (-Real.exp (-t)) t := by
    simpa only [Function.comp_def, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  convert (((hasDerivAt_const t (2 : ℝ)).sub (hasDerivAt_id t)).sub he) using 1
  · funext h
    simp [holCoefficients]
    ring
  · ring

/-- The derivative mismatch is an exact expression, not a numerical test. -/
theorem hol_linear_coefficient_defect :
    deriv (fun h : ℝ => (holCoefficients 1 1 h).μ22) 1 -
      (holCoefficients 1 1 1).μ32 = 1 - 3 * Real.exp (-1) := by
  rw [(hol_mu22_unit_hasDeriv 1).deriv]
  simp only [holCoefficients, one_pow, div_one, one_mul, mul_one]
  ring

/-- In particular the printed coefficient matrix cannot be the exact
fundamental solution of u'=v, v'=-u-v on every positive time interval. -/
theorem hol_linear_coefficient_not_exact :
    deriv (fun h : ℝ => (holCoefficients 1 1 h).μ22) 1 ≠
      (holCoefficients 1 1 1).μ32 := by
  have hp : 0 < Real.exp (-1) := Real.exp_pos _
  have he : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
  have hb := mul_lt_mul_of_pos_right Real.exp_one_lt_three hp
  have hd := hol_linear_coefficient_defect
  intro h
  rw [h, sub_self] at hd
  nlinarith

end PBGSO.Methods
