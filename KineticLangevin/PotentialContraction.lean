import KineticLangevin.Contraction
import UnadjustedLangevin.SharpContraction

/-! # Kinetic contraction directly from the potential

The spectral argument can also be proved without selecting a mean Hessian.
Strong convexity and a Lipschitz gradient imply a sector inequality for
`gradient f x - gradient f y - m • (x-y)`.  Completing a square proves the
same `m/γ` contraction whenever `γ² ≥ m+M`.  This formulation needs only a
differentiable potential, rather than a separately continuous Hessian.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open Set

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual derivative along a synchronous kinetic difference with force
equal to a difference of gradients. -/
def forceEnergyDerivative (γ : ℝ) (v x force : E) : ℝ :=
  2 * ⟪v + γ • x, -force⟫ + 2 * ⟪-v, γ • v + force⟫

/-- Strong-smooth interpolation rewritten as cocoercivity after subtracting
the strongly monotone part. -/
theorem interpolation_sector (m M : ℝ) (x force : E)
    (hi : m * M * ‖x‖ ^ 2 + ‖force‖ ^ 2 ≤ (m + M) * ⟪force, x⟫) :
    ‖force - m • x‖ ^ 2 ≤ (M - m) * ⟪x, force - m • x⟫ := by
  simp only [norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_comm force x]
  nlinarith

/-- Completing one square converts the sector inequality into dissipativity
of the concrete nonlinear kinetic drift. -/
theorem force_dissipativity (γ m M : ℝ) (hγ : 0 < γ) (hmM : m ≤ M)
    (hfriction : m + M ≤ γ ^ 2) (v x force : E)
    (hsector : ‖force - m • x‖ ^ 2 ≤ (M - m) * ⟪x, force - m • x⟫) :
    forceEnergyDerivative γ v x force ≤
      (-2 * m / γ) * transformEnergy γ 0 (v, x) := by
  let k := force - m • x
  have hk : force = k + m • x := by dsimp [k]; module
  have hid : γ * forceEnergyDerivative γ v x force +
      2 * m * transformEnergy γ 0 (v, x) =
      2 * (-(γ ^ 2 - 2 * m) * ‖v‖ ^ 2 - 2 * γ * ⟪v, k⟫ - γ ^ 2 * ⟪x, k⟫) := by
    rw [hk]
    simp only [forceEnergyDerivative, transformEnergy, transform, sub_zero,
      zero_smul, norm_neg, norm_add_sq_real, inner_add_left, inner_add_right,
      inner_neg_right, inner_neg_left, real_inner_smul_left, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_self_eq_norm_sq,
      real_inner_comm x v]
    ring
  have hb : γ * forceEnergyDerivative γ v x force +
      2 * m * transformEnergy γ 0 (v, x) ≤ 0 := by
    rcases hmM.eq_or_lt with heq | hlt
    · have hk0 : k = 0 := by
        apply norm_eq_zero.mp
        have hz : ‖k‖ ^ 2 ≤ 0 := by simpa [k, heq] using hsector
        nlinarith [norm_nonneg k]
      rw [hid, hk0]
      simp only [inner_zero_right, mul_zero, sub_zero]
      have hf : 0 ≤ γ ^ 2 - 2 * m := by linarith
      nlinarith [mul_nonneg hf (sq_nonneg ‖v‖)]
    · have hsq := sq_nonneg ‖γ • k + (M - m) • v‖
      simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        real_inner_smul_left, real_inner_smul_right] at hsq
      rw [real_inner_comm v k] at hsq
      have hs := mul_le_mul_of_nonneg_left hsector (sq_nonneg γ)
      change γ ^ 2 * ‖k‖ ^ 2 ≤ γ ^ 2 * ((M - m) * ⟪x, k⟫) at hs
      have hr : 0 ≤ (M - m) * (γ ^ 2 - m - M) * ‖v‖ ^ 2 := by
        exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hmM) (by linarith)) (sq_nonneg _)
      have hprod : (M - m) * (γ * forceEnergyDerivative γ v x force +
          2 * m * transformEnergy γ 0 (v, x)) ≤ 0 := by
        rw [hid]
        nlinarith
      nlinarith
  have hdiv : forceEnergyDerivative γ v x force ≤
      (-2 * m * transformEnergy γ 0 (v, x)) / γ := by
    apply (le_div_iff₀ hγ).mpr
    nlinarith
  convert hdiv using 1 <;> ring

/-- The potential assumptions of the paper establish nonlinear kinetic
dissipativity. No Hessian or contraction conclusion is assumed. -/
theorem potential_force_dissipativity [CompleteSpace E]
    (f : E → ℝ) (m γ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hfriction : m + (M : ℝ) ≤ γ ^ 2) (v x y : E) :
    forceEnergyDerivative γ v (x - y) (gradient f x - gradient f y) ≤
      (-2 * m / γ) * transformEnergy γ 0 (v, x - y) := by
  apply force_dissipativity γ m M hγ hmM hfriction
  exact interpolation_sector m M (x - y) (gradient f x - gradient f y)
    (ULA.strong_smooth_gradient_interpolation f m M hdiff hsc hLip hmM x y)

/-- The difference of two synchronously driven kinetic diffusions is
differentiable even though each velocity path contains Brownian noise. -/
theorem hasDerivAt_forceEnergy (γ : ℝ) (v x force : ℝ → E) (t : ℝ)
    (hv : HasDerivAt v (-γ • v t - force t) t)
    (hx : HasDerivAt x (v t) t) :
    HasDerivAt (fun r ↦ transformEnergy γ 0 (v r, x r))
      (forceEnergyDerivative γ (v t) (x t) (force t)) t := by
  have hy := hv.add (hx.const_smul γ)
  have hz := hv.neg
  have hyd : -γ • v t - force t + γ • v t = -force t := by module
  have hzd : -(-γ • v t - force t) = γ • v t + force t := by module
  rw [hyd] at hy
  rw [hzd] at hz
  convert hy.norm_sq.add hz.norm_sq using 1 <;>
    simp [transformEnergy, transform, forceEnergyDerivative]
  funext r
  rfl

/-- Exponential transformed-energy contraction of the actual nonlinear
kinetic difference equation, derived directly from the potential assumptions.
The paths `x,y` are the two positions and `v` is the velocity difference. -/
theorem potential_synchronous_energy_decay [CompleteSpace E]
    (f : E → ℝ) (m γ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hfriction : m + (M : ℝ) ≤ γ ^ 2)
    (T : ℝ) (v x y : ℝ → E)
    (hvcont : ContinuousOn v (Icc 0 T))
    (hxcont : ContinuousOn x (Icc 0 T)) (hycont : ContinuousOn y (Icc 0 T))
    (hv : ∀ t ∈ Ico 0 T, HasDerivAt v
      (-γ • v t - (gradient f (x t) - gradient f (y t))) t)
    (hx : ∀ t ∈ Ico 0 T, HasDerivAt (fun r ↦ x r - y r) (v t) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformEnergy γ 0 (v t, x t - y t) ≤
      transformEnergy γ 0 (v 0, x 0 - y 0) * Real.exp ((-2 * m / γ) * t) := by
  let F := fun t ↦ transformEnergy γ 0 (v t, x t - y t)
  let F' := fun t ↦ forceEnergyDerivative γ (v t) (x t - y t)
    (gradient f (x t) - gradient f (y t))
  have hcont : ContinuousOn F (Icc 0 T) := by
    convert
      ((hvcont.add ((hxcont.sub hycont).const_smul γ)).norm.pow 2).add
        (hvcont.neg.norm.pow 2) using 1
    ext t
    simp [F, transformEnergy, transform]
  have hder : ∀ t ∈ Ico 0 T, HasDerivAt F (F' t) t := by
    intro t ht
    exact hasDerivAt_forceEnergy γ v (fun r ↦ x r - y r)
      (fun r ↦ gradient f (x r) - gradient f (y r)) t (hv t ht) (hx t ht)
  have hbound : ∀ t ∈ Ico 0 T, F' t ≤ (-2 * m / γ) * F t + 0 := by
    intro t ht
    simpa using potential_force_dissipativity f m γ M hdiff hsc hLip hmM
      hγ hfriction (v t) (x t) (y t)
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun t ht r hr ↦ (hder t ht).hasDerivWithinAt.liminf_right_slope_le hr)
    (le_refl (F 0)) hbound t ht
  simpa only [gronwallBound_ε0, sub_zero] using hgr

/-- The simple `√2 exp(-mt/γ)` position contraction of the paper, proved
for nonlinear strongly convex, smooth potentials and equal initial velocities.
Only the noise-cancelled differential equations are required of the paths. -/
theorem potential_synchronous_position_decay [CompleteSpace E]
    (f : E → ℝ) (m γ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hfriction : m + (M : ℝ) ≤ γ ^ 2)
    (T : ℝ) (v x y : ℝ → E) (hv0 : v 0 = 0)
    (hvcont : ContinuousOn v (Icc 0 T))
    (hxcont : ContinuousOn x (Icc 0 T)) (hycont : ContinuousOn y (Icc 0 T))
    (hv : ∀ t ∈ Ico 0 T, HasDerivAt v
      (-γ • v t - (gradient f (x t) - gradient f (y t))) t)
    (hx : ∀ t ∈ Ico 0 T, HasDerivAt (fun r ↦ x r - y r) (v t) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖x t - y t‖ ≤ Real.sqrt 2 * Real.exp ((-m / γ) * t) * ‖x 0 - y 0‖ := by
  have he := potential_synchronous_energy_decay f m γ M hdiff hsc hLip hmM
    hγ hfriction T v x y hvcont hxcont hycont hv hx t ht
  rw [hv0, transformEnergy_zero_velocity] at he
  simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at he
  have hp := position_sq_le_energy γ 0 (v t, x t - y t)
  simp only [mul_zero, sub_zero] at hp
  have hs : ‖x t - y t‖ ^ 2 ≤
      2 * Real.exp ((-2 * m / γ) * t) * ‖x 0 - y 0‖ ^ 2 := by
    nlinarith [sq_pos_of_pos hγ]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤
    Real.sqrt 2 * Real.exp ((-m / γ) * t) * ‖x 0 - y 0‖)).mp
  have hexp : Real.exp ((-m / γ) * t) ^ 2 = Real.exp ((-2 * m / γ) * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hexp] using hs

/-- The energy derivative computation also holds for right derivatives,
which is the natural endpoint statement for finite-horizon integral paths. -/
theorem hasDerivWithinAt_forceEnergy (γ : ℝ) (v x force : ℝ → E) (t : ℝ)
    (hv : HasDerivWithinAt v (-γ • v t - force t) (Ici t) t)
    (hx : HasDerivWithinAt x (v t) (Ici t) t) :
    HasDerivWithinAt (fun r ↦ transformEnergy γ 0 (v r, x r))
      (forceEnergyDerivative γ (v t) (x t) (force t)) (Ici t) t := by
  have hy := hv.add (hx.const_smul γ)
  have hz := hv.neg
  have hyd : -γ • v t - force t + γ • v t = -force t := by module
  have hzd : -(-γ • v t - force t) = γ • v t + force t := by module
  rw [hyd] at hy
  rw [hzd] at hz
  convert hy.norm_sq.add hz.norm_sq using 1 <;>
    simp [transformEnergy, transform, forceEnergyDerivative]
  funext r
  rfl

/-- The pathwise nonlinear energy contraction with right derivatives,
including at the initial endpoint. This version applies directly to the
shared-noise derivative proved from the actual integral equations. -/
theorem potential_synchronous_energy_decay_right [CompleteSpace E]
    (f : E → ℝ) (m γ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hfriction : m + (M : ℝ) ≤ γ ^ 2)
    (T : ℝ) (v x y : ℝ → E)
    (hvcont : ContinuousOn v (Icc 0 T))
    (hxcont : ContinuousOn x (Icc 0 T)) (hycont : ContinuousOn y (Icc 0 T))
    (hv : ∀ t ∈ Ico 0 T, HasDerivWithinAt v
      (-γ • v t - (gradient f (x t) - gradient f (y t))) (Ici t) t)
    (hx : ∀ t ∈ Ico 0 T, HasDerivWithinAt (fun r ↦ x r - y r) (v t) (Ici t) t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformEnergy γ 0 (v t, x t - y t) ≤
      transformEnergy γ 0 (v 0, x 0 - y 0) * Real.exp ((-2 * m / γ) * t) := by
  let F := fun t ↦ transformEnergy γ 0 (v t, x t - y t)
  let F' := fun t ↦ forceEnergyDerivative γ (v t) (x t - y t)
    (gradient f (x t) - gradient f (y t))
  have hcont : ContinuousOn F (Icc 0 T) := by
    convert
      ((hvcont.add ((hxcont.sub hycont).const_smul γ)).norm.pow 2).add
        (hvcont.neg.norm.pow 2) using 1
    ext t
    simp [F, transformEnergy, transform]
  have hder : ∀ t ∈ Ico 0 T, HasDerivWithinAt F (F' t) (Ici t) t := by
    intro t ht
    exact hasDerivWithinAt_forceEnergy γ v (fun r ↦ x r - y r)
      (fun r ↦ gradient f (x r) - gradient f (y r)) t (hv t ht) (hx t ht)
  have hbound : ∀ t ∈ Ico 0 T, F' t ≤ (-2 * m / γ) * F t + 0 := by
    intro t ht
    simpa using potential_force_dissipativity f m γ M hdiff hsc hLip hmM
      hγ hfriction (v t) (x t) (y t)
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun t ht r hr ↦ (hder t ht).liminf_right_slope_le hr)
    (le_refl (F 0)) hbound t ht
  simpa only [gronwallBound_ε0, sub_zero] using hgr

end KineticLangevin
