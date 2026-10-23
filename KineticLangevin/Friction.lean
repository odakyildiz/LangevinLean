import KineticLangevin.GeneralContraction

/-! # Optimizing the contraction exponent

These are the scalar optimization arguments behind Table 1. The admissible
shift interval is `0 ≤ a < γ/2`. The critical equal-curvature boundary with a
zero denominator is excluded explicitly, rather than evaluating a singular
prefactor.
-/

noncomputable section
namespace KineticLangevin

/-- The norm exponent in the general synchronous contraction theorem. -/
def contractionExponent (γ a m M : ℝ) : ℝ :=
  max (a^2-m) (M-(γ-a)^2) / (γ-2*a)

/-- With `d=γ-2a`, the two curvature branches have a common denominator. -/
theorem contractionExponent_centered (γ a m M : ℝ) (hd : 0 < γ-2*a) :
    contractionExponent γ a m M = -γ/2 +
      max (((γ-2*a)^2+γ^2-4*m)/(4*(γ-2*a)))
        ((4*M-γ^2-(γ-2*a)^2)/(4*(γ-2*a))) := by
  have h1 : (a^2-m)/(γ-2*a) = -γ/2 +
      ((γ-2*a)^2+γ^2-4*m)/(4*(γ-2*a)) := by
    calc
      _ = ((-γ/2)*(γ-2*a)+((γ-2*a)^2+γ^2-4*m)/4)/(γ-2*a) := by congr 1; ring
      _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hd.ne', div_div]
  have h2 : (M-(γ-a)^2)/(γ-2*a) = -γ/2 +
      (4*M-γ^2-(γ-2*a)^2)/(4*(γ-2*a)) := by
    calc
      _ = ((-γ/2)*(γ-2*a)+(4*M-γ^2-(γ-2*a)^2)/4)/(γ-2*a) := by congr 1; ring
      _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hd.ne', div_div]
  unfold contractionExponent
  rw [← max_div_div_right hd.le, h1, h2, ← max_add_add_left]

/-- Below `γ²=m+M`, no nonnegative shift improves the exponent at `a=0`. -/
theorem contractionExponent_low_optimal (γ m M a : ℝ) (hγ : 0 < γ)
    (hmM : m ≤ M) (hregime : γ^2 ≤ m+M) (ha : 0 ≤ a) (hd : 0 < γ-2*a) :
    (M-γ^2)/γ ≤ contractionExponent γ a m M := by
  have hcurv : γ*a ≤ 2*M := by nlinarith
  have hfrac : (M-γ^2)/γ ≤ (M-(γ-a)^2)/(γ-2*a) := by
    apply (div_le_div_iff₀ hγ hd).mpr
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hcurv)]
  exact hfrac.trans ((div_le_div_iff_of_pos_right hd).mpr (le_max_right _ _))

/-- The low-friction optimum is attained by the unshifted coordinates. -/
theorem contractionExponent_low_zero (γ m M : ℝ) (hregime : γ^2 ≤ m+M) :
    contractionExponent γ 0 m M = (M-γ^2)/γ := by
  simp only [contractionExponent, zero_pow (by decide : 2 ≠ 0), zero_sub, sub_zero,
    mul_zero]
  rw [max_eq_right (by linarith)]

/-- The two curvature endpoints balance at the middle-regime shift. -/
theorem contractionExponent_middle_value (γ m M : ℝ) (hγ : 0 < γ)
    (hleft : m+M ≤ γ^2) (hradicand : 0 < 2*(m+M)-γ^2) :
    let d := Real.sqrt (2*(m+M)-γ^2)
    let a := (γ-d)/2
    0 ≤ a ∧ 0 < γ-2*a ∧
      contractionExponent γ a m M = -γ/2 + (M-m)/(2*d) := by
  dsimp only
  let d := Real.sqrt (2*(m+M)-γ^2)
  have hd : 0 < d := Real.sqrt_pos.mpr hradicand
  have hdsq : d^2 = 2*(m+M)-γ^2 := Real.sq_sqrt hradicand.le
  have hdγ : d ≤ γ := by nlinarith
  have hden : γ-2*((γ-d)/2) = d := by ring
  refine ⟨by dsimp [d] at hdγ ⊢; linarith, by rw [hden]; exact hd, ?_⟩
  unfold contractionExponent
  have heq : ((γ-d)/2)^2-m = M-(γ-(γ-d)/2)^2 := by nlinarith
  rw [heq, max_self, hden]
  change (M-(γ-(γ-d)/2)^2)/d = -γ/2+(M-m)/(2*d)
  field_simp [hd.ne']
  nlinarith

/-- At middle friction, the balanced shift minimizes the exponent globally
on the full admissible shift interval. The proof factors both branch errors
instead of differentiating the maximum at its corner. -/
theorem contractionExponent_middle_optimal (γ m M a : ℝ) (hγ : 0 < γ)
    (hmM : m ≤ M) (hleft : m+M ≤ γ^2) (hright : γ^2 ≤ 3*m+M)
    (hradicand : 0 < 2*(m+M)-γ^2) (ha : 0 ≤ a) (hd : 0 < γ-2*a) :
    -γ/2 + (M-m)/(2*Real.sqrt (2*(m+M)-γ^2)) ≤ contractionExponent γ a m M := by
  let D := Real.sqrt (2*(m+M)-γ^2)
  let d := γ-2*a
  have hD : 0 < D := Real.sqrt_pos.mpr hradicand
  have hDsq : D^2 = 2*(m+M)-γ^2 := Real.sq_sqrt hradicand.le
  have hds : 0 < d := hd
  have hcenter := contractionExponent_centered γ a m M hd
  change contractionExponent γ a m M = -γ/2 +
    max ((d^2+γ^2-4*m)/(4*d)) ((4*M-γ^2-d^2)/(4*d)) at hcenter
  rw [hcenter]
  suffices (M-m)/(2*D) ≤
      max ((d^2+γ^2-4*m)/(4*d)) ((4*M-γ^2-d^2)/(4*d)) by
    dsimp [D] at this; linarith
  have hM : 0 ≤ M-m := sub_nonneg.mpr hmM
  have hDcube := congrArg (fun r : ℝ ↦ D*r) hDsq
  by_cases horder : d ≤ D
  · apply le_trans _ (le_max_right _ _)
    apply (div_le_div_iff₀ (by positivity : 0 < 2*D) (by positivity : 0 < 4*d)).mpr
    have hfactor : 0 ≤ (D-d)*(D^2+D*d+2*(M-m)) :=
      mul_nonneg (sub_nonneg.mpr horder) (by positivity)
    nlinarith [hDcube]
  · have horder : D ≤ d := le_of_not_ge horder
    apply le_trans _ (le_max_left _ _)
    apply (div_le_div_iff₀ (by positivity : 0 < 2*D) (by positivity : 0 < 4*d)).mpr
    have hcoef : 0 ≤ 2*D^2-2*(M-m) := by nlinarith
    have hfactor : 0 ≤ (d-D)*(D*(d-D)+(2*D^2-2*(M-m))) :=
      mul_nonneg (sub_nonneg.mpr horder) (by positivity)
    nlinarith [hDcube]

/-- The overdamped optimal shift solves `a*(γ-a)=m`; the larger root is
not admissible. The strict radicand is the nonsingular endpoint condition. -/
theorem contractionExponent_high_value (γ m M : ℝ) (hm : 0 ≤ m)
    (hγ : 0 < γ) (hregime : 3*m+M ≤ γ^2) (hdisc : 0 < γ^2-4*m) :
    let D := Real.sqrt (γ^2-4*m)
    let a := (γ-D)/2
    0 ≤ a ∧ 0 < γ-2*a ∧ contractionExponent γ a m M = -a := by
  dsimp only
  let D := Real.sqrt (γ^2-4*m)
  have hD : 0 < D := Real.sqrt_pos.mpr hdisc
  have hDsq : D^2 = γ^2-4*m := Real.sq_sqrt hdisc.le
  have hDγ : D ≤ γ := by nlinarith
  have hden : γ-2*((γ-D)/2) = D := by ring
  refine ⟨by linarith, by rw [hden]; exact hD, ?_⟩
  unfold contractionExponent
  have hmax : M-(γ-(γ-D)/2)^2 ≤ ((γ-D)/2)^2-m := by nlinarith
  rw [max_eq_left hmax, hden]
  apply (div_eq_iff hD.ne').mpr
  nlinarith

/-- The high-friction value is the global optimum, by the nonnegative
square `(γ-2a-sqrt(γ²-4m))²`. -/
theorem contractionExponent_high_optimal (γ m M a : ℝ) (hdisc : 0 < γ^2-4*m)
    (hd : 0 < γ-2*a) :
    -(γ-Real.sqrt (γ^2-4*m))/2 ≤ contractionExponent γ a m M := by
  let D := Real.sqrt (γ^2-4*m)
  have hDsq : D^2 = γ^2-4*m := Real.sq_sqrt hdisc.le
  have hbranch : -(γ-D)/2 ≤ (a^2-m)/(γ-2*a) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (γ-2*a-D)]
  exact hbranch.trans ((div_le_div_iff_of_pos_right hd).mpr (le_max_left _ _))

end KineticLangevin
