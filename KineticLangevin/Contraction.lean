import KineticLangevin.Geometry
import Mathlib.Analysis.ODE.Gronwall

/-! # The spectral cancellation behind kinetic Langevin contraction

The drift matrix itself is not symmetric.  In the transformed coordinates its
off-diagonal terms cancel in the quadratic form, because the Hessian is
self-adjoint.  This proves the dimension-independent rate used in Proposition
1 of Dalalyan--Riou-Durand.  The hypotheses below are ordinary differential
equations and Hessian bounds, rather than an assumed contraction estimate.
-/

noncomputable section
open scoped RealInnerProductSpace
open Set

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Derivative of transformed energy along the kinetic difference equation
`v' = -γv-Hx`, `x'=v`. -/
def energyDerivative (γ a : ℝ) (H : E →L[ℝ] E) (s : E × E) : ℝ :=
  2 * ⟪(transform γ a s).1, -a • s.1 - H s.2⟫ +
    2 * ⟪(transform γ a s).2, (γ - a) • s.1 + H s.2⟫

/-- The exact cancellation identity, with the denominator cleared. -/
theorem spectral_identity (γ a : ℝ) (H : E →L[ℝ] E)
    (hH : ∀ x y, ⟪x, H y⟫ = ⟪y, H x⟫) (s : E × E) :
    (γ - 2 * a) * energyDerivative γ a H s =
      2 * (a ^ 2 * ‖(transform γ a s).1‖ ^ 2 -
        ⟪(transform γ a s).1, H (transform γ a s).1⟫ +
        ⟪(transform γ a s).2, H (transform γ a s).2⟫ -
        (γ - a) ^ 2 * ‖(transform γ a s).2‖ ^ 2) := by
  simp only [energyDerivative, transform, ← real_inner_self_eq_norm_sq,
    map_add, map_sub, map_neg, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [hH s.1 s.2, real_inner_comm s.1 s.2]
  ring

/-- Spectral bounds for a symmetric Hessian imply the paper's differential
energy inequality, for every admissible change of coordinates. -/
theorem spectral_dissipativity (γ a m M : ℝ) (hd : 0 < γ - 2 * a)
    (H : E →L[ℝ] E) (hH : ∀ x y, ⟪x, H y⟫ = ⟪y, H x⟫)
    (hLower : ∀ x, m * ‖x‖ ^ 2 ≤ ⟪x, H x⟫)
    (hUpper : ∀ x, ⟪x, H x⟫ ≤ M * ‖x‖ ^ 2) (s : E × E) :
    energyDerivative γ a H s ≤
      (2 * max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)) *
        transformEnergy γ a s := by
  let k := max (a ^ 2 - m) (M - (γ - a) ^ 2)
  have hy := hLower (transform γ a s).1
  have hz := hUpper (transform γ a s).2
  have hky := mul_le_mul_of_nonneg_right (le_max_left (a ^ 2 - m)
    (M - (γ - a) ^ 2)) (sq_nonneg ‖(transform γ a s).1‖)
  have hkz := mul_le_mul_of_nonneg_right (le_max_right (a ^ 2 - m)
    (M - (γ - a) ^ 2)) (sq_nonneg ‖(transform γ a s).2‖)
  have he := spectral_identity γ a H hH s
  have hb : (γ - 2 * a) * energyDerivative γ a H s ≤
      2 * k * transformEnergy γ a s := by
    unfold transformEnergy
    dsimp [k]
    nlinarith
  have hdiv := (le_div_iff₀ hd).mpr (show energyDerivative γ a H s * (γ - 2 * a) ≤
    2 * k * transformEnergy γ a s by nlinarith [hb])
  convert hdiv using 1 <;> dsimp [k] <;> ring

/-- In the useful friction regime `γ²≥m+M`, the unshifted coordinates give
the simple decay exponent `m/γ`. -/
theorem spectral_dissipativity_zero (γ m M : ℝ) (hγ : 0 < γ)
    (hfriction : m + M ≤ γ ^ 2) (H : E →L[ℝ] E)
    (hH : ∀ x y, ⟪x, H y⟫ = ⟪y, H x⟫)
    (hLower : ∀ x, m * ‖x‖ ^ 2 ≤ ⟪x, H x⟫)
    (hUpper : ∀ x, ⟪x, H x⟫ ≤ M * ‖x‖ ^ 2) (s : E × E) :
    energyDerivative γ 0 H s ≤ (-2 * m / γ) * transformEnergy γ 0 s := by
  have he := spectral_dissipativity γ 0 m M (by simpa using hγ) H hH hLower hUpper s
  have hm : M - γ ^ 2 ≤ -m := by linarith
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_sub, sub_zero,
    max_eq_left hm, neg_mul, mul_neg, mul_zero] using he

/-- Differentiating the actual transformed energy of a kinetic difference
path produces the quadratic form just bounded. -/
theorem hasDerivAt_transformEnergy (γ a : ℝ) (H : E →L[ℝ] E)
    (v x : ℝ → E) (t : ℝ)
    (hv : HasDerivAt v (-γ • v t - H (x t)) t)
    (hx : HasDerivAt x (v t) t) :
    HasDerivAt (fun r ↦ transformEnergy γ a (v r, x r))
      (energyDerivative γ a H (v t, x t)) t := by
  have hy := hv.add (hx.const_smul (γ - a))
  have hz := hv.neg.sub (hx.const_smul a)
  have hyd : -γ • v t - H (x t) + (γ - a) • v t = -a • v t - H (x t) := by
    module
  have hzd : -(-γ • v t - H (x t)) - a • v t = (γ - a) • v t + H (x t) := by
    module
  rw [hyd] at hy
  rw [hzd] at hz
  exact hy.norm_sq.add hz.norm_sq

/-- Proposition 1's differential equation implies exponential decay of its
transformed energy.  The Hessian is allowed to vary with time. -/
theorem transformed_energy_decay (γ a m M T : ℝ) (hd : 0 < γ - 2 * a)
    (v x : ℝ → E) (H : ℝ → E →L[ℝ] E)
    (hvcont : ContinuousOn v (Icc 0 T)) (hxcont : ContinuousOn x (Icc 0 T))
    (hv : ∀ t ∈ Ico 0 T, HasDerivAt v (-γ • v t - H t (x t)) t)
    (hx : ∀ t ∈ Ico 0 T, HasDerivAt x (v t) t)
    (hH : ∀ t ∈ Ico 0 T, ∀ y z, ⟪y, H t z⟫ = ⟪z, H t y⟫)
    (hLower : ∀ t ∈ Ico 0 T, ∀ y, m * ‖y‖ ^ 2 ≤ ⟪y, H t y⟫)
    (hUpper : ∀ t ∈ Ico 0 T, ∀ y, ⟪y, H t y⟫ ≤ M * ‖y‖ ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformEnergy γ a (v t, x t) ≤ transformEnergy γ a (v 0, x 0) *
      Real.exp ((2 * max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)) * t) := by
  let F : ℝ → ℝ := fun t ↦ transformEnergy γ a (v t, x t)
  let F' : ℝ → ℝ := fun t ↦ energyDerivative γ a (H t) (v t, x t)
  let K := 2 * max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)
  have hcont : ContinuousOn F (Icc 0 T) := by
    exact (((hvcont.add (hxcont.const_smul (γ - a))).norm.pow 2).add
      (((hvcont.neg).sub (hxcont.const_smul a)).norm.pow 2))
  have hder : ∀ t ∈ Ico 0 T, HasDerivAt F (F' t) t := by
    intro t ht
    exact hasDerivAt_transformEnergy γ a (H t) v x t (hv t ht) (hx t ht)
  have hbound : ∀ t ∈ Ico 0 T, F' t ≤ K * F t + 0 := by
    intro t ht
    simpa using spectral_dissipativity γ a m M hd (H t) (hH t ht)
      (hLower t ht) (hUpper t ht) (v t, x t)
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun t ht r hr ↦ (hder t ht).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl (F 0)) hbound t ht
  simpa only [gronwallBound_ε0, sub_zero] using hgr

/-- The position estimate in Proposition 1, in squared form.  Taking square
roots gives precisely `√(2((γ-a)²+a²))/(γ-2a)` times the exponential factor. -/
theorem synchronous_position_sq_decay (γ a m M T : ℝ) (hd : 0 < γ - 2 * a)
    (v x : ℝ → E) (H : ℝ → E →L[ℝ] E) (hv0 : v 0 = 0)
    (hvcont : ContinuousOn v (Icc 0 T)) (hxcont : ContinuousOn x (Icc 0 T))
    (hv : ∀ t ∈ Ico 0 T, HasDerivAt v (-γ • v t - H t (x t)) t)
    (hx : ∀ t ∈ Ico 0 T, HasDerivAt x (v t) t)
    (hH : ∀ t ∈ Ico 0 T, ∀ y z, ⟪y, H t z⟫ = ⟪z, H t y⟫)
    (hLower : ∀ t ∈ Ico 0 T, ∀ y, m * ‖y‖ ^ 2 ≤ ⟪y, H t y⟫)
    (hUpper : ∀ t ∈ Ico 0 T, ∀ y, ⟪y, H t y⟫ ≤ M * ‖y‖ ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (γ - 2 * a) ^ 2 * ‖x t‖ ^ 2 ≤
      2 * ((γ - a) ^ 2 + a ^ 2) * Real.exp
        ((2 * max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)) * t) * ‖x 0‖ ^ 2 := by
  have hdec := transformed_energy_decay γ a m M T hd v x H hvcont hxcont hv hx
    hH hLower hUpper t ht
  rw [hv0, transformEnergy_zero_velocity] at hdec
  have hp := position_sq_le_energy γ a (v t, x t)
  nlinarith

/-- The same spectral energy derivative calculation for right derivatives. -/
theorem hasDerivWithinAt_transformEnergy (γ a : ℝ) (H : E →L[ℝ] E)
    (v x : ℝ → E) (t : ℝ)
    (hv : HasDerivWithinAt v (-γ • v t - H (x t)) (Ici t) t)
    (hx : HasDerivWithinAt x (v t) (Ici t) t) :
    HasDerivWithinAt (fun r ↦ transformEnergy γ a (v r, x r))
      (energyDerivative γ a H (v t, x t)) (Ici t) t := by
  have hy := hv.add (hx.const_smul (γ - a))
  have hz := hv.neg.sub (hx.const_smul a)
  have hyd : -γ • v t - H (x t) + (γ - a) • v t = -a • v t - H (x t) := by module
  have hzd : -(-γ • v t - H (x t)) - a • v t = (γ - a) • v t + H (x t) := by module
  rw [hyd] at hy
  rw [hzd] at hz
  exact hy.norm_sq.add hz.norm_sq

/-- Arbitrary-shift spectral contraction using only right derivatives,
including the endpoint regularity provided by actual integral equations. -/
theorem transformed_energy_decay_right (γ a m M T : ℝ) (hd : 0 < γ - 2 * a)
    (v x : ℝ → E) (H : ℝ → E →L[ℝ] E)
    (hvcont : ContinuousOn v (Icc 0 T)) (hxcont : ContinuousOn x (Icc 0 T))
    (hv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (-γ • v t - H t (x t)) (Ici t) t)
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (v t) (Ici t) t)
    (hH : ∀ t ∈ Ico 0 T, ∀ y z, ⟪y, H t z⟫ = ⟪z, H t y⟫)
    (hLower : ∀ t ∈ Ico 0 T, ∀ y, m * ‖y‖ ^ 2 ≤ ⟪y, H t y⟫)
    (hUpper : ∀ t ∈ Ico 0 T, ∀ y, ⟪y, H t y⟫ ≤ M * ‖y‖ ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformEnergy γ a (v t, x t) ≤ transformEnergy γ a (v 0, x 0) *
      Real.exp ((2 * max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)) * t) := by
  let F : ℝ → ℝ := fun t ↦ transformEnergy γ a (v t, x t)
  let F' : ℝ → ℝ := fun t ↦ energyDerivative γ a (H t) (v t, x t)
  let K := 2 * max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)
  have hcont : ContinuousOn F (Icc 0 T) := by
    exact (((hvcont.add (hxcont.const_smul (γ - a))).norm.pow 2).add
      (((hvcont.neg).sub (hxcont.const_smul a)).norm.pow 2))
  have hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt F (F' t) (Ici t) t := by
    intro t ht
    exact hasDerivWithinAt_transformEnergy γ a (H t) v x t (hv t ht) (hx t ht)
  have hbound : ∀ t ∈ Ico 0 T, F' t ≤ K * F t + 0 := by
    intro t ht
    simpa using spectral_dissipativity γ a m M hd (H t) (hH t ht)
      (hLower t ht) (hUpper t ht) (v t, x t)
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun t ht r hr ↦ (hder t ht).liminf_right_slope_le hr)
    (le_refl (F 0)) hbound t ht
  simpa only [gronwallBound_ε0, sub_zero] using hgr

/-- The complete prefactor and exponent of Proposition 1 from the
right-differentiable synchronous ODE, valid for every `a<γ/2`. -/
theorem synchronous_position_decay_right (γ a m M T : ℝ) (hd : 0 < γ - 2 * a)
    (v x : ℝ → E) (H : ℝ → E →L[ℝ] E) (hv0 : v 0 = 0)
    (hvcont : ContinuousOn v (Icc 0 T)) (hxcont : ContinuousOn x (Icc 0 T))
    (hv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v (-γ • v t - H t (x t)) (Ici t) t)
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (v t) (Ici t) t)
    (hH : ∀ t ∈ Ico 0 T, ∀ y z, ⟪y, H t z⟫ = ⟪z, H t y⟫)
    (hLower : ∀ t ∈ Ico 0 T, ∀ y, m * ‖y‖ ^ 2 ≤ ⟪y, H t y⟫)
    (hUpper : ∀ t ∈ Ico 0 T, ∀ y, ⟪y, H t y⟫ ≤ M * ‖y‖ ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖x t‖ ≤ Real.sqrt (2 * ((γ - a) ^ 2 + a ^ 2)) / (γ - 2 * a) *
      Real.exp ((max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)) * t) * ‖x 0‖ := by
  let k := max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)
  have he := transformed_energy_decay_right γ a m M T hd v x H hvcont hxcont hv hx
    hH hLower hUpper t ht
  rw [hv0, transformEnergy_zero_velocity] at he
  have hp := position_sq_le_energy γ a (v t, x t)
  have hexp : Real.exp (k * t) ^ 2 =
      Real.exp ((2 * max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)) * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [k]
    ring
  have hmain : (γ - 2 * a) * ‖x t‖ ≤
      Real.sqrt (2 * ((γ - a) ^ 2 + a ^ 2)) * Real.exp (k * t) * ‖x 0‖ := by
    apply (sq_le_sq₀ (mul_nonneg hd.le (norm_nonneg _)) (by positivity)).mp
    rw [mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 2 * ((γ - a) ^ 2 + a ^ 2)), hexp]
    nlinarith
  have hdiv : ‖x t‖ ≤ (Real.sqrt (2 * ((γ - a) ^ 2 + a ^ 2)) *
      Real.exp (k * t) * ‖x 0‖) / (γ - 2 * a) :=
    (le_div_iff₀ hd).mpr (by nlinarith)
  convert hdiv using 1 <;> dsimp [k] <;> ring

end KineticLangevin
