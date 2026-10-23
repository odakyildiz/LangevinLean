import KineticLangevin.PotentialContraction

/-! # Arbitrary-parameter contraction from first-order potential assumptions

Centered phase coordinates convert the sector inequality of a strongly
convex smooth gradient directly into the spectral estimate of the paper.
No continuous Hessian, mean-Hessian choice, or contraction hypothesis is
needed.  The exponent is exactly the maximum of the two curvature endpoints.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace NNReal

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The energy derivative for a concrete force difference, with arbitrary
shift parameter `a`. -/
def generalForceEnergyDerivative (γ a : ℝ) (v x force : E) : ℝ :=
  2 * ⟪v + (γ - a) • x, -a • v - force⟫ +
    2 * ⟪-v - a • x, (γ - a) • v + force⟫

/-- The transformed energy in the centered coordinates `v+(γ/2)x`. -/
theorem transformEnergy_centered (γ a : ℝ) (v x : E) :
    transformEnergy γ a (v, x) =
      2 * ‖v + (γ / 2) • x‖ ^ 2 + ((γ - 2 * a) ^ 2 / 2) * ‖x‖ ^ 2 := by
  simp only [transformEnergy, transform, ← real_inner_self_eq_norm_sq,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_neg_left, inner_neg_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm v x]
  ring

/-- The exact centered energy derivative identity. -/
theorem generalForceEnergyDerivative_centered (γ a : ℝ) (v x force : E) :
    generalForceEnergyDerivative γ a v x force =
      -γ * transformEnergy γ a (v, x) +
        4 * ⟪v + (γ / 2) • x, (((γ - a) ^ 2 + a ^ 2) / 2) • x - force⟫ := by
  simp only [generalForceEnergyDerivative, transformEnergy, transform,
    ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm v x]
  ring

/-- The centered sector bound controls the force residual around any scalar
curvature `c`; its constant is the larger distance to `m` and `M`. -/
theorem centered_force_residual (m M c : ℝ) (hmM : m ≤ M) (x force : E)
    (hcenter : ‖force - ((m + M) / 2) • x‖ ≤ ((M - m) / 2) * ‖x‖) :
    ‖c • x - force‖ ≤ max (c - m) (M - c) * ‖x‖ := by
  have he : c • x - force = (c - (m + M) / 2) • x -
      (force - ((m + M) / 2) • x) := by module
  have ht := norm_sub_le ((c - (m + M) / 2) • x)
    (force - ((m + M) / 2) • x)
  rw [he]
  rw [norm_smul, Real.norm_eq_abs] at ht
  have hcoeff : |c - (m + M) / 2| + (M - m) / 2 = max (c - m) (M - c) := by
    by_cases hc : (m + M) / 2 ≤ c
    · rw [abs_of_nonneg (by linarith : 0 ≤ c - (m + M) / 2), max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonpos (by linarith : c - (m + M) / 2 ≤ 0), max_eq_right (by linarith)]
      ring
  rw [← hcoeff]
  nlinarith

/-- The full arbitrary-parameter dissipativity estimate follows from the
gradient sector inequality, including friction regimes where the exponent
is positive. It is the precise quadratic-form estimate of Proposition 1. -/
theorem general_force_dissipativity (γ a m M : ℝ) (hd : 0 < γ - 2 * a)
    (hmM : m ≤ M) (v x force : E)
    (hcenter : ‖force - ((m + M) / 2) • x‖ ≤ ((M - m) / 2) * ‖x‖) :
    generalForceEnergyDerivative γ a v x force ≤
      (2 * max (a ^ 2 - m) (M - (γ - a) ^ 2) / (γ - 2 * a)) *
        transformEnergy γ a (v, x) := by
  let c := ((γ - a) ^ 2 + a ^ 2) / 2
  let k := max (c - m) (M - c)
  let y := v + (γ / 2) • x
  have hk : 0 ≤ k := by
    have h1 := le_max_left (c - m) (M - c)
    have h2 := le_max_right (c - m) (M - c)
    dsimp [k]
    linarith
  have hres := centered_force_residual m M c hmM x force hcenter
  have hip := real_inner_le_norm y (c • x - force)
  have hscaled := mul_le_mul_of_nonneg_left hres (norm_nonneg y)
  have hinner : ⟪y, c • x - force⟫ ≤ k * ‖y‖ * ‖x‖ := by
    dsimp [k]
    nlinarith
  have henergy := transformEnergy_centered γ a v x
  have hyoung : 4 * (γ - 2 * a) * ‖y‖ * ‖x‖ ≤
      2 * transformEnergy γ a (v, x) := by
    have hs := sq_nonneg (2 * ‖y‖ - (γ - 2 * a) * ‖x‖)
    change transformEnergy γ a (v, x) = 2 * ‖y‖ ^ 2 +
      ((γ - 2 * a) ^ 2 / 2) * ‖x‖ ^ 2 at henergy
    nlinarith
  have hmapped := mul_le_mul_of_nonneg_left hyoung hk
  have hinnerd := mul_le_mul_of_nonneg_left hinner hd.le
  have hderiv := generalForceEnergyDerivative_centered γ a v x force
  change generalForceEnergyDerivative γ a v x force =
    -γ * transformEnergy γ a (v, x) + 4 * ⟪y, c • x - force⟫ at hderiv
  have hmax : k = max (a ^ 2 - m) (M - (γ - a) ^ 2) + γ * (γ - 2 * a) / 2 := by
    have h1 : c - m = (a ^ 2 - m) + γ * (γ - 2 * a) / 2 := by dsimp [c]; ring
    have h2 : M - c = (M - (γ - a) ^ 2) + γ * (γ - 2 * a) / 2 := by dsimp [c]; ring
    dsimp [k]
    rw [h1, h2, max_add_add_right]
  have hbound : generalForceEnergyDerivative γ a v x force * (γ - 2 * a) ≤
      2 * max (a ^ 2 - m) (M - (γ - a) ^ 2) * transformEnergy γ a (v, x) := by
    have hdEq := congrArg (fun r : ℝ ↦ r * (γ - 2 * a)) hderiv
    have hmEq := congrArg (fun r : ℝ ↦ 2 * r * transformEnergy γ a (v, x)) hmax
    nlinarith
  have hdiv := (le_div_iff₀ hd).mpr hbound
  convert hdiv using 1 <;> ring

/-- The paper's potential assumptions provide the centered sector input,
without a continuous-Hessian hypothesis. -/
theorem potential_general_force_dissipativity [CompleteSpace E]
    (f : E → ℝ) (m γ a : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hd : 0 < γ - 2 * a) (v x y : E) :
    generalForceEnergyDerivative γ a v (x - y) (gradient f x - gradient f y) ≤
      (2 * max (a ^ 2 - m) ((M : ℝ) - (γ - a) ^ 2) / (γ - 2 * a)) *
        transformEnergy γ a (v, x - y) := by
  apply general_force_dissipativity γ a m M hd hmM
  exact ULA.gradient_difference_centered_bound x y (gradient f x) (gradient f y) m M hmM
    (ULA.strong_smooth_gradient_interpolation f m M hdiff hsc hLip hmM x y)

/-- Differentiating the arbitrary-shift energy along a concrete force
difference is valid in the right-derivative sense at the initial time. -/
theorem hasDerivWithinAt_generalForceEnergy (γ a : ℝ) (v x force : ℝ → E) (t : ℝ)
    (hv : HasDerivWithinAt v (-γ • v t - force t) (Ici t) t)
    (hx : HasDerivWithinAt x (v t) (Ici t) t) :
    HasDerivWithinAt (fun r ↦ transformEnergy γ a (v r, x r))
      (generalForceEnergyDerivative γ a (v t) (x t) (force t)) (Ici t) t := by
  have hy := hv.add (hx.const_smul (γ - a))
  have hz := hv.neg.sub (hx.const_smul a)
  have hyd : -γ • v t - force t + (γ - a) • v t = -a • v t - force t := by module
  have hzd : -(-γ • v t - force t) - a • v t = (γ - a) • v t + force t := by module
  rw [hyd] at hy
  rw [hzd] at hz
  exact hy.norm_sq.add hz.norm_sq

/-- The full shifted exponential-energy estimate from the original
first-order potential assumptions and the actual right difference ODE. -/
theorem potential_general_energy_decay_right [CompleteSpace E]
    (f : E → ℝ) (m γ a : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hd : 0 < γ - 2 * a)
    (T : ℝ) (v x y : ℝ → E)
    (hvcont : ContinuousOn v (Icc 0 T))
    (hxcont : ContinuousOn x (Icc 0 T)) (hycont : ContinuousOn y (Icc 0 T))
    (hv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v
      (-γ • v t - (gradient f (x t) - gradient f (y t))) (Ici t) t)
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun r ↦ x r - y r) (v t) (Ici t) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformEnergy γ a (v t, x t - y t) ≤ transformEnergy γ a (v 0, x 0 - y 0) *
      Real.exp ((2 * max (a ^ 2 - m) ((M : ℝ) - (γ - a) ^ 2) / (γ - 2 * a)) * t) := by
  let F := fun t ↦ transformEnergy γ a (v t, x t - y t)
  let F' := fun t ↦ generalForceEnergyDerivative γ a (v t) (x t - y t)
    (gradient f (x t) - gradient f (y t))
  have hcont : ContinuousOn F (Icc 0 T) := by
    exact (((hvcont.add ((hxcont.sub hycont).const_smul (γ - a))).norm.pow 2).add
      (((hvcont.neg).sub ((hxcont.sub hycont).const_smul a)).norm.pow 2))
  have hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt F (F' t) (Ici t) t := by
    intro t ht
    exact hasDerivWithinAt_generalForceEnergy γ a v (fun r ↦ x r - y r)
      (fun r ↦ gradient f (x r) - gradient f (y r)) t (hv t ht) (hx t ht)
  have hbound : ∀ t ∈ Ico 0 T, F' t ≤
      (2 * max (a ^ 2 - m) ((M : ℝ) - (γ - a) ^ 2) / (γ - 2 * a)) * F t + 0 := by
    intro t ht
    simpa using potential_general_force_dissipativity f m γ a M hdiff hsc hLip hmM
      hd (v t) (x t) (y t)
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun t ht r hr ↦ (hder t ht).liminf_right_slope_le hr)
    (le_refl (F 0)) hbound t ht
  simpa only [gronwallBound_ε0, sub_zero] using hgr

end KineticLangevin
