import KineticLangevin.IntegralCoupling
import KineticLangevin.PotentialContraction
import KineticLangevin.GeneralContraction

/-! # Contraction of the constructed synchronous kinetic integral flows

The hypotheses here are the concrete integral equations provided by Picard
existence. Noise cancellation, the right differential equations, and energy
decay are consequences. This closes the deterministic existence-to-coupling
bridge without an assumed reference contraction estimate or stationarity.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Actual kinetic integral solutions driven by a common additive input
contract in the transformed energy. The noise path itself is unrestricted. -/
theorem kinetic_integral_energy_decay
    (f : E → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (Y Z B : ℝ → E × E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformEnergy γ 0 (Y t - Z t) ≤
      transformEnergy γ 0 (Y 0 - Z 0) * Real.exp ((-2 * m / γ) * t) := by
  have hd := integral_difference_hasDerivWithinAt
    (kineticNegativeDrift (gradient f) γ 1) (γ + 1 * M + 1)
    (kineticNegativeDrift_lipschitz (gradient f) M γ 1 hLip)
    Y Z B hY hZ T heY heZ
  have hv : ∀ r ∈ Ico 0 T, HasDerivWithinAt (fun s ↦ (Y s).1 - (Z s).1)
      (-(γ : ℝ) • ((Y r).1 - (Z r).1) -
        (gradient f (Y r).2 - gradient f (Z r).2)) (Ici r) r := by
    intro r hr
    have hp := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivWithinAt r (hd r hr)
    change HasDerivWithinAt (fun s ↦ (Y s).1 - (Z s).1)
      (-((γ : ℝ) • (Y r).1 + 1 • gradient f (Y r).2 -
        ((γ : ℝ) • (Z r).1 + 1 • gradient f (Z r).2))) (Ici r) r at hp
    convert hp using 1 <;> module
  have hx : ∀ r ∈ Ico 0 T, HasDerivWithinAt (fun s ↦ (Y s).2 - (Z s).2)
      ((Y r).1 - (Z r).1) (Ici r) r := by
    intro r hr
    have hp := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivWithinAt r (hd r hr)
    change HasDerivWithinAt (fun s ↦ (Y s).2 - (Z s).2)
      (-(-(Y r).1 - -(Z r).1)) (Ici r) r at hp
    convert hp using 1 <;> module
  have he := potential_synchronous_energy_decay_right f m γ M hdiff hsc hLip hmM
    hγ hfriction T (fun r ↦ (Y r).1 - (Z r).1) (fun r ↦ (Y r).2) (fun r ↦ (Z r).2)
    ((hY.fst.sub hZ.fst).continuousOn) hY.snd.continuousOn hZ.snd.continuousOn
    hv hx t ht
  exact he

/-- The position projection of the actual synchronous integral flows has
the paper's `√2 exp(-mt/γ)` bound when their initial velocities agree. -/
theorem kinetic_integral_position_decay
    (f : E → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (Y Z B : ℝ → E × E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (Z s)) + B t)
    (hvelocity : (Y 0).1 = (Z 0).1) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖(Y t).2 - (Z t).2‖ ≤ Real.sqrt 2 * Real.exp ((-m / γ) * t) *
      ‖(Y 0).2 - (Z 0).2‖ := by
  have he := kinetic_integral_energy_decay f m M γ hdiff hsc hLip hmM
    hγ hfriction Y Z B hY hZ T heY heZ t ht
  have hinitial : Y 0 - Z 0 = (0, (Y 0).2 - (Z 0).2) := by
    ext <;> simp [hvelocity]
  rw [hinitial, transformEnergy_zero_velocity] at he
  simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at he
  have hp := position_sq_le_energy γ 0 (Y t - Z t)
  simp only [mul_zero, sub_zero, Prod.snd_sub] at hp
  have hs : ‖(Y t).2 - (Z t).2‖ ^ 2 ≤
      2 * Real.exp ((-2 * m / γ) * t) * ‖(Y 0).2 - (Z 0).2‖ ^ 2 := by
    nlinarith [sq_pos_of_pos hγ]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤
    Real.sqrt 2 * Real.exp ((-m / γ) * t) * ‖(Y 0).2 - (Z 0).2‖)).mp
  have hexp : Real.exp ((-m / γ) * t) ^ 2 = Real.exp ((-2 * m / γ) * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hexp] using hs

/-- The full transformed Euclidean norm contracts, rather than only the
position projection. This is the norm used to accumulate discretization error. -/
theorem kinetic_integral_transformNorm_decay
    (f : E → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (Y Z B : ℝ → E × E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (Z s)) + B t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    transformNorm γ 0 (Y t - Z t) ≤ Real.exp ((-m / γ) * t) * transformNorm γ 0 (Y 0 - Z 0) := by
  have he := kinetic_integral_energy_decay f m M γ hdiff hsc hLip hmM
    hγ hfriction Y Z B hY hZ T heY heZ t ht
  have hexp : Real.exp ((-m / γ) * t) ^ 2 = Real.exp ((-2 * m / γ) * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply transformNorm_le_of_energy_le γ 0
    (Real.exp ((-m / γ) * t) * transformNorm γ 0 (Y 0 - Z 0)) _ (by
      exact mul_nonneg (Real.exp_pos _).le (transformNorm_nonneg _ _ _))
  rw [mul_pow, hexp, transformNorm_sq]
  nlinarith

/-- The complete arbitrary-shift position bound of Theorem 1 for actual
synchronous kinetic integral flows, without a continuous-Hessian assumption.
The only strict parameter restriction is the invertibility `γ-2a>0`. -/
theorem kinetic_integral_position_decay_general
    (f : E → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hd : 0 < (γ : ℝ) - 2 * a)
    (Y Z B : ℝ → E × E) (hY : Continuous Y) (hZ : Continuous Z) (T : ℝ)
    (heY : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (Y s)) + B t)
    (heZ : ∀ t ∈ Icc 0 T, Z t - Z 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (Z s)) + B t)
    (hvelocity : (Y 0).1 = (Z 0).1) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖(Y t).2 - (Z t).2‖ ≤
      Real.sqrt (2 * (((γ : ℝ) - a) ^ 2 + a ^ 2)) / ((γ : ℝ) - 2 * a) *
        Real.exp ((max (a ^ 2 - m) ((M : ℝ) - ((γ : ℝ) - a) ^ 2) /
          ((γ : ℝ) - 2 * a)) * t) * ‖(Y 0).2 - (Z 0).2‖ := by
  have hdiffPath := integral_difference_hasDerivWithinAt
    (kineticNegativeDrift (gradient f) γ 1) (γ + 1 * M + 1)
    (kineticNegativeDrift_lipschitz (gradient f) M γ 1 hLip)
    Y Z B hY hZ T heY heZ
  have hv : ∀ r ∈ Ico 0 T, HasDerivWithinAt (fun s ↦ (Y s).1 - (Z s).1)
      (-(γ : ℝ) • ((Y r).1 - (Z r).1) -
        (gradient f (Y r).2 - gradient f (Z r).2)) (Ici r) r := by
    intro r hr
    have hp := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivWithinAt r (hdiffPath r hr)
    change HasDerivWithinAt (fun s ↦ (Y s).1 - (Z s).1)
      (-((γ : ℝ) • (Y r).1 + 1 • gradient f (Y r).2 -
        ((γ : ℝ) • (Z r).1 + 1 • gradient f (Z r).2))) (Ici r) r at hp
    convert hp using 1 <;> module
  have hx : ∀ r ∈ Ico 0 T, HasDerivWithinAt (fun s ↦ (Y s).2 - (Z s).2)
      ((Y r).1 - (Z r).1) (Ici r) r := by
    intro r hr
    have hp := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivWithinAt r (hdiffPath r hr)
    change HasDerivWithinAt (fun s ↦ (Y s).2 - (Z s).2)
      (-(-(Y r).1 - -(Z r).1)) (Ici r) r at hp
    convert hp using 1 <;> module
  have he := potential_general_energy_decay_right f m γ a M hdiff hsc hLip hmM hd T
    (fun r ↦ (Y r).1 - (Z r).1) (fun r ↦ (Y r).2) (fun r ↦ (Z r).2)
    ((hY.fst.sub hZ.fst).continuousOn) hY.snd.continuousOn hZ.snd.continuousOn
    hv hx t ht
  rw [sub_eq_zero.mpr hvelocity, transformEnergy_zero_velocity] at he
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
