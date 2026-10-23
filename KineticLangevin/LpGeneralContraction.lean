import KineticLangevin.LpContraction

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal RealInnerProductSpace
namespace KineticLangevin
variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (P : Measure Ω) [IsFiniteMeasure P]

/-- The actual L² kinetic integral solutions satisfy the transformed energy
bound, with the actual lifted nonlinear gradient. -/
theorem lp_kinetic_integral_energy_decay_general
    (f : H → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hd : 0 < (γ : ℝ)-2*a)
    (Y Z B : ℝ → Lp H 2 P × Lp H 2 P) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformEnergy γ a (Y t - Z t) ≤
      transformEnergy γ a (Y 0 - Z 0) * Real.exp ((2 * max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2) / ((γ : ℝ)-2*a))*t) := by
  let G := ULA.lpDrift P (gradient f) hLip
  have hG : LipschitzWith M G := ULA.lpDrift_lipschitz P (gradient f) hLip
  have hdiffEq := integral_difference_hasDerivWithinAt (kineticNegativeDrift G γ 1)
    (γ + 1 * M + 1) (kineticNegativeDrift_lipschitz G M γ 1 hG)
    Y Z B hY hZ T heY heZ
  let F := fun r ↦ transformEnergy γ a (Y r - Z r)
  let F' := fun r ↦ generalForceEnergyDerivative γ a ((Y r).1 - (Z r).1)
    ((Y r).2 - (Z r).2) (G (Y r).2 - G (Z r).2)
  have hcont : ContinuousOn F (Icc 0 T) := by
    unfold F transformEnergy transform
    exact ((((hY.fst.sub hZ.fst).add ((hY.snd.sub hZ.snd).const_smul ((γ : ℝ)-a))).norm.pow 2).add
      (((hY.fst.sub hZ.fst).neg.sub ((hY.snd.sub hZ.snd).const_smul a)).norm.pow 2)).continuousOn
  have hder : ∀ r ∈ Ico 0 T, HasDerivWithinAt F (F' r) (Ici r) r := by
    intro r hr
    have hv := (ContinuousLinearMap.fst ℝ (Lp H 2 P) (Lp H 2 P)).hasFDerivAt.comp_hasDerivWithinAt r (hdiffEq r hr)
    have hx := (ContinuousLinearMap.snd ℝ (Lp H 2 P) (Lp H 2 P)).hasFDerivAt.comp_hasDerivWithinAt r (hdiffEq r hr)
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
    exact hasDerivWithinAt_generalForceEnergy (γ : ℝ) a
      (fun s ↦ (Y s).1 - (Z s).1) (fun s ↦ (Y s).2 - (Z s).2)
      (fun s ↦ G (Y s).2 - G (Z s).2) r hv' hx'
  have hbound : ∀ r ∈ Ico 0 T, F' r ≤
      (2 * max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2) / ((γ : ℝ)-2*a)) * F r + 0 := by
    intro r hr
    have he := general_force_dissipativity γ a m M hd hmM
      ((Y r).1-(Z r).1) ((Y r).2-(Z r).2) (G (Y r).2-G (Z r).2)
      (lpDrift_centered_bound P f m M hdiff hsc hLip hmM (Y r).2 (Z r).2)
    have hpair : ((Y r).1-(Z r).1,(Y r).2-(Z r).2) = Y r-Z r := rfl
    rw [hpair] at he
    simpa only [F,F',add_zero] using he
  have hgr := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun r hr c hc ↦ (hder r hr).liminf_right_slope_le hc)
    (le_refl (F 0)) hbound t ht
  simpa only [gronwallBound_ε0, sub_zero] using hgr

/-- The complete arbitrary-shift position bound of Theorem 1 for actual
synchronous kinetic integral flows, without a continuous-Hessian assumption.
The only strict parameter restriction is the invertibility `γ-2a>0`. -/
theorem lp_kinetic_integral_position_decay_general
    (f : H → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hd : 0 < (γ : ℝ) - 2 * a)
    (Y Z B : ℝ → Lp H 2 P × Lp H 2 P) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 =
      -(∫ s in 0..t, kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Z s)) + B t)
    (hvelocity : (Y 0).1 = (Z 0).1) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖(Y t).2 - (Z t).2‖ ≤
      Real.sqrt (2 * (((γ : ℝ) - a) ^ 2 + a ^ 2)) / ((γ : ℝ) - 2 * a) *
        Real.exp ((max (a ^ 2 - m) ((M : ℝ) - ((γ : ℝ) - a) ^ 2) /
          ((γ : ℝ) - 2 * a)) * t) * ‖(Y 0).2 - (Z 0).2‖ := by
  have he := lp_kinetic_integral_energy_decay_general P f m a M γ hdiff hsc hLip hmM hd
    Y Z B hY hZ T heY heZ t ht
  have hinit : Y 0-Z 0 = (0,(Y 0).2-(Z 0).2) := by ext <;> simp [hvelocity]
  rw [hinit,transformEnergy_zero_velocity] at he
  have hp := position_sq_le_energy γ a (Y t - Z t)
  let k := max (a ^ 2 - m) ((M : ℝ) - ((γ : ℝ) - a) ^ 2) / ((γ : ℝ) - 2 * a)
  have hexp : Real.exp (k * t) ^ 2 = Real.exp
      ((2 * max (a ^ 2 - m) ((M : ℝ) - ((γ : ℝ) - a) ^ 2) / ((γ : ℝ) - 2 * a)) * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    dsimp [k]
    ring
  have hmain : ((γ : ℝ) - 2 * a) * ‖(Y t).2 - (Z t).2‖ ≤
      Real.sqrt (2 * (((γ : ℝ) - a) ^ 2 + a ^ 2)) * Real.exp (k * t) *
        ‖(Y 0).2 - (Z 0).2‖ := by
    apply (sq_le_sq₀ (mul_nonneg hd.le (norm_nonneg _)) (by positivity)).mp
    rw [mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 2 * (((γ : ℝ) - a) ^ 2 + a ^ 2)), hexp]
    change ((γ : ℝ) - 2 * a) ^ 2 * ‖(Y t).2 - (Z t).2‖ ^ 2 ≤
      2 * (((γ : ℝ) - a) ^ 2 + a ^ 2) * _ * ‖(Y 0).2 - (Z 0).2‖ ^ 2
    change ((γ : ℝ) - 2 * a) ^ 2 * ‖(Y t).2 - (Z t).2‖ ^ 2 ≤
      2 * transformEnergy γ a (Y t - Z t) at hp
    change transformEnergy γ a (Y t - Z t) ≤ _ at he
    nlinarith
  have hdiv : ‖(Y t).2 - (Z t).2‖ ≤
      (Real.sqrt (2 * (((γ : ℝ) - a) ^ 2 + a ^ 2)) * Real.exp (k * t) *
        ‖(Y 0).2 - (Z 0).2‖) / ((γ : ℝ) - 2 * a) :=
    (le_div_iff₀ hd).mpr (by nlinarith)
  convert hdiv using 1 <;> dsimp [k] <;> ring

end KineticLangevin
