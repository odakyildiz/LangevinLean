import KineticLangevin.SynchronousFlow
import UnadjustedLangevin.LpDrift

/-! # Actual kinetic coupling in the Hilbert space of random vectors

The nonlinear gradient is lifted pointwise using the project's proved
`lpDrift` construction. Its centered sector bound passes to L² by the
pointwise norm inequality. Consequently the kinetic transformed contraction
holds for actual L² integral solutions without defining a fictitious
potential on the space of random variables.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace

namespace KineticLangevin

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (P : Measure Ω) [IsFiniteMeasure P]

/-- Strong-smooth centered gradient control passes to the actual pointwise
lift on square-integrable random variables. -/
theorem lpDrift_centered_bound
    (f : H → ℝ) (m : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (X Y : Lp H 2 P) :
    ‖(ULA.lpDrift P (gradient f) hLip X - ULA.lpDrift P (gradient f) hLip Y) -
      ((m + (M : ℝ)) / 2) • (X - Y)‖ ≤ ((M : ℝ) - m) / 2 * ‖X - Y‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub
      (ULA.lpDrift P (gradient f) hLip X - ULA.lpDrift P (gradient f) hLip Y)
      (((m + (M : ℝ)) / 2) • (X - Y)),
    Lp.coeFn_sub (ULA.lpDrift P (gradient f) hLip X) (ULA.lpDrift P (gradient f) hLip Y),
    Lp.coeFn_smul ((m + (M : ℝ)) / 2) (X - Y), Lp.coeFn_sub X Y,
    ULA.lpDrift_coe P (gradient f) hLip X, ULA.lpDrift_coe P (gradient f) hLip Y]
      with ω hs hforce hsm hxy hgx hgy
  simp only [hs, hforce, hsm, hxy, hgx, hgy, Pi.sub_apply, Pi.smul_apply]
  exact ULA.gradient_difference_centered_bound (X ω) (Y ω)
    (gradient f (X ω)) (gradient f (Y ω)) m M hmM
    (ULA.strong_smooth_gradient_interpolation f m M hdiff hsc hLip hmM (X ω) (Y ω))

/-- The actual L² kinetic integral solutions satisfy the transformed energy
bound, with the actual lifted nonlinear gradient. -/
theorem lp_kinetic_integral_energy_decay
    (f : H → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (Y Z B : ℝ → Lp H 2 P × Lp H 2 P) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformEnergy γ 0 (Y t - Z t) ≤
      transformEnergy γ 0 (Y 0 - Z 0) * Real.exp ((-2 * m / γ) * t) := by
  let G := ULA.lpDrift P (gradient f) hLip
  have hG : LipschitzWith M G := ULA.lpDrift_lipschitz P (gradient f) hLip
  have hd := integral_difference_hasDerivWithinAt (kineticNegativeDrift G γ 1)
    (γ + 1 * M + 1) (kineticNegativeDrift_lipschitz G M γ 1 hG)
    Y Z B hY hZ T heY heZ
  let F := fun r ↦ transformEnergy γ 0 (Y r - Z r)
  let F' := fun r ↦ generalForceEnergyDerivative γ 0 ((Y r).1 - (Z r).1)
    ((Y r).2 - (Z r).2) (G (Y r).2 - G (Z r).2)
  have hcont : ContinuousOn F (Icc 0 T) := by
    unfold F transformEnergy transform
    simp only [sub_zero, zero_smul, sub_zero]
    exact (((hY.fst.sub hZ.fst).add ((hY.snd.sub hZ.snd).const_smul γ)).norm.pow 2).add
      ((hY.fst.sub hZ.fst).neg.norm.pow 2) |>.continuousOn
  have hder : ∀ r ∈ Ico 0 T, HasDerivWithinAt F (F' r) (Ici r) r := by
    intro r hr
    have hv := (ContinuousLinearMap.fst ℝ (Lp H 2 P) (Lp H 2 P)).hasFDerivAt.comp_hasDerivWithinAt r (hd r hr)
    have hx := (ContinuousLinearMap.snd ℝ (Lp H 2 P) (Lp H 2 P)).hasFDerivAt.comp_hasDerivWithinAt r (hd r hr)
    change HasDerivWithinAt (fun s ↦ (Y s).1 - (Z s).1)
      (-((γ : ℝ) • (Y r).1 + 1 • G (Y r).2 -
        ((γ : ℝ) • (Z r).1 + 1 • G (Z r).2))) (Ici r) r at hv
    change HasDerivWithinAt (fun s ↦ (Y s).2 - (Z s).2)
      (-(-(Y r).1 - -(Z r).1)) (Ici r) r at hx
    have hv' : HasDerivWithinAt (fun s ↦ (Y s).1 - (Z s).1)
        (-(γ : ℝ) • ((Y r).1 - (Z r).1) - (G (Y r).2 - G (Z r).2)) (Ici r) r := by
      convert hv using 1 <;> module
    have hx' : HasDerivWithinAt (fun s ↦ (Y s).2 - (Z s).2)
        ((Y r).1 - (Z r).1) (Ici r) r := by convert hx using 1 <;> module
    exact hasDerivWithinAt_generalForceEnergy (γ : ℝ) 0
      (fun s ↦ (Y s).1 - (Z s).1) (fun s ↦ (Y s).2 - (Z s).2)
      (fun s ↦ G (Y s).2 - G (Z s).2) r hv' hx'
  have hbound : ∀ r ∈ Ico 0 T, F' r ≤ (-2 * m / γ) * F r + 0 := by
    intro r hr
    have he := general_force_dissipativity γ 0 m M (by simpa using hγ) hmM
      ((Y r).1 - (Z r).1) ((Y r).2 - (Z r).2) (G (Y r).2 - G (Z r).2)
      (lpDrift_centered_bound P f m M hdiff hsc hLip hmM (Y r).2 (Z r).2)
    have hmax : (M : ℝ) - (γ : ℝ) ^ 2 ≤ -m := by linarith
    have hpair : ((Y r).1 - (Z r).1, (Y r).2 - (Z r).2) = Y r - Z r := rfl
    rw [hpair] at he
    simpa [F, F', max_eq_left hmax] using he
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun r hr c hc ↦ (hder r hr).liminf_right_slope_le hc)
    (le_refl (F 0)) hbound t ht
  simpa only [gronwallBound_ε0, sub_zero] using hgr

/-- The full L² transformed norm contracts by `exp(-mt/γ)`. -/
theorem lp_kinetic_integral_transformNorm_decay
    (f : H → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (Y Z B : ℝ → Lp H 2 P × Lp H 2 P) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformNorm γ 0 (Y t - Z t) ≤
      Real.exp ((-m / γ) * t) * transformNorm γ 0 (Y 0 - Z 0) := by
  have he := lp_kinetic_integral_energy_decay P f m M γ hdiff hsc hLip hmM
    hγ hfriction Y Z B hY hZ T heY heZ t ht
  have hexp : Real.exp ((-m / γ) * t) ^ 2 = Real.exp ((-2 * m / γ) * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply transformNorm_le_of_energy_le γ 0 _ _ (by
    exact mul_nonneg (Real.exp_pos _).le (transformNorm_nonneg _ _ _))
  rw [mul_pow, hexp, transformNorm_sq]
  nlinarith

end KineticLangevin
