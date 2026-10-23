import KineticLangevin.HamiltonianMetropolis
import UnadjustedLangevin.Analysis.Smooth

/-! # Quantitative energy error for the actual Verlet map

These estimates use a globally Lipschitz gradient. They bound the explicit
Hamiltonian defect, hence the actual rejection probability of the invariant
Metropolis approximation; no stationarity or numerical error is postulated.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The two-sided first-order Taylor estimate follows by applying the smooth
upper bound to the potential and its negative. -/
theorem smooth_taylor_abs (f : E → ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f)) (x y : E) :
    |f y - f x - ⟪gradient f x,y-x⟫| ≤ (M : ℝ)/2 * ‖y-x‖^2 := by
  have hneg : gradient (fun z ↦ -f z) = fun z ↦ -gradient f z := by
    funext z
    change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (-f) z) =
      -(InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)
    rw [fderiv_neg,map_neg]
  have hu := ULA.Analysis.smooth_upper_bound f M hf hLip x y
  have hn := ULA.Analysis.smooth_upper_bound (fun z ↦ -f z) M hf.neg
    (by rw [hneg]; exact hLip.neg) x y
  simp only [hneg, inner_neg_left] at hn
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- Averaging the Taylor remainders from the two endpoints bounds the
trapezoidal force-work error with no Hessian regularity assumption. -/
theorem smooth_trapezoid_abs (f : E → ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f)) (x y : E) :
    |f y-f x - (1/2:ℝ)*⟪gradient f x+gradient f y,y-x⟫| ≤
      (M : ℝ)/2 * ‖y-x‖^2 := by
  have hx := smooth_taylor_abs f M hf hLip x y
  have hy := smooth_taylor_abs f M hf hLip y x
  have hsub : x-y = -(y-x) := by module
  rw [hsub,norm_neg,inner_neg_right] at hy
  have htri := abs_add_le (f y-f x-⟪gradient f x,y-x⟫)
    (-(f x-f y+⟪gradient f y,y-x⟫))
  simp only [abs_neg,← sub_eq_add_neg] at htri
  simp only [sub_neg_eq_add] at hy
  have he : f y-f x-(1/2:ℝ)*⟪gradient f x+gradient f y,y-x⟫ =
      ((f y-f x-⟪gradient f x,y-x⟫) -
        (f x-f y+⟪gradient f y,y-x⟫))/2 := by
    rw [inner_add_left]
    ring
  rw [he,abs_div]
  norm_num only [show |(2:ℝ)|=2 by norm_num]
  have hh := htri.trans (add_le_add hx hy)
  linarith

/-- A Lipschitz force bounds the exact difference of squared force norms. -/
theorem force_norm_sq_sub_abs (g : E → E) (M : ℝ≥0)
    (hLip : LipschitzWith M g) (x y : E) :
    |‖g y‖^2-‖g x‖^2| ≤
      (M : ℝ)*‖y-x‖*(2*‖g x‖+(M : ℝ)*‖y-x‖) := by
  have hd := hLip.norm_sub_le y x
  have hr := abs_norm_sub_norm_le (g y) (g x)
  have hy : ‖g y‖ ≤ ‖g x‖+(M : ℝ)*‖y-x‖ := by
    have ht := norm_sub_le (g y-g x) (-g x)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at ht
    linarith
  have hid : ‖g y‖^2-‖g x‖^2 = (‖g y‖-‖g x‖)*(‖g y‖+‖g x‖) := by ring
  rw [hid,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul (hr.trans hd) (by linarith) (by positivity) (by positivity)

/-- The Verlet energy defect is explicitly quadratic in the step, with a
higher-order force correction retained. -/
theorem verlet_energy_defect_abs (f : E → ℝ) (M : ℝ≥0)
    (hf : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f)) (h : ℝ) (z : E×E) :
    let w := z.1-(h/2) • gradient f z.2
    |hamiltonianEnergy f (verletStep (gradient f) h z)-hamiltonianEnergy f z| ≤
      (M : ℝ)/2*h^2*‖w‖^2 + h^2/8*((M : ℝ)* (|h| * ‖w‖)*
        (2*‖gradient f z.2‖+(M : ℝ)*(|h| * ‖w‖))) := by
  let w := z.1-(h/2) • gradient f z.2
  let y := z.2+h • w
  have hwork := smooth_trapezoid_abs f M hf hLip z.2 y
  have hforce := force_norm_sq_sub_abs (gradient f) M hLip z.2 y
  have hy : y-z.2 = h • w := by dsimp [y]; module
  rw [hy,norm_smul,Real.norm_eq_abs] at hwork hforce
  have hid := verlet_energy_defect_identity f (gradient f) h z
  change _ = f y-f z.2-(h/2)*⟪w,gradient f z.2+gradient f y⟫+
    h^2/8*(‖gradient f y‖^2-‖gradient f z.2‖^2) at hid
  have hw : (1/2:ℝ)*⟪gradient f z.2+gradient f y,h • w⟫ =
      (h/2)*⟪w,gradient f z.2+gradient f y⟫ := by
    rw [real_inner_smul_right,real_inner_comm]
    ring
  rw [hw] at hwork
  rw [hid]
  calc
    _ ≤ |f y-f z.2-(h/2)*⟪w,gradient f z.2+gradient f y⟫| +
        |h^2/8*(‖gradient f y‖^2-‖gradient f z.2‖^2)| := abs_add_le _ _
    _ ≤ (M : ℝ)/2*(|h| * ‖w‖)^2 + (h^2/8)*
        ((M : ℝ)*(|h| * ‖w‖)*(2*‖gradient f z.2‖+(M : ℝ)*(|h| * ‖w‖))) := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ h^2/8)]
      exact add_le_add hwork (mul_le_mul_of_nonneg_left hforce (by positivity))
    _ = _ := by dsimp [w]; rw [mul_pow,sq_abs]; ring

end KineticLangevin
