import KineticLangevin.MildError
import KineticLangevin.SynchronousFlow

/-! # The first-order coupling inequality for the implemented step

This is the concrete bridge from continuous-time contraction and weighted
local error to the scalar recurrence. An exact auxiliary kinetic path starts
at the numerical point and is coupled to a reference integral path.  Its
mild equation identifies the exponential update's actual error.  The
reference velocity bound remains an explicit assumption; Gibbs stationarity
or the corresponding Gaussian moment is not assumed through a hidden field.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual exponential step satisfies the one-step inequality used in
the first-order proof. Every path and both forms of the shared noise are
explicit: `W` is the additive input, and `B` its velocity convolution. -/
theorem exponentialStep_coupling_bound
    (f : E → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 ≤ m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (A R W : ℝ → E × E) (B : ℝ → E)
    (hA : Continuous A) (hR : Continuous R) (hB : Continuous B)
    (h C : ℝ) (hh : 0 ≤ h) (hC : 0 ≤ C) (hsmall : (γ : ℝ) * h ≤ 1 / 4)
    (heA : ∀ t ∈ Icc 0 h, A t - A 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (A s)) + W t)
    (heR : ∀ t ∈ Icc 0 h, R t - R 0 =
      -(∫ s in 0..t, kineticNegativeDrift (gradient f) γ 1 (R s)) + W t)
    (hmild : ∀ t ∈ Icc 0 h, (A t).1 = psi γ 0 t • (A 0).1 -
      (∫ s in 0..t, Real.exp (-(γ : ℝ) * (t - s)) • gradient f (A s).2) + B t)
    (hkin : ∀ t ∈ Icc 0 h, (A t).2 - (A 0).2 = ∫ s in 0..t, (A s).1)
    (hreference : ∀ t ∈ Icc 0 h, ‖(R t).1‖ ≤ C) :
    transformNorm γ 0
      (exponentialStep (gradient f) γ h (A 0) (B h, ∫ s in 0..h, B s) - R h) ≤
      Real.exp ((-m / γ) * h) * transformNorm γ 0 (A 0 - R 0) +
        (3 / 4 : ℝ) * (M : ℝ) * h ^ 2 * (C + transformNorm γ 0 (A 0 - R 0)) := by
  let e := transformNorm γ 0 (A 0 - R 0)
  have he : 0 ≤ e := transformNorm_nonneg _ _ _
  have hdec := kinetic_integral_transformNorm_decay f m M γ hdiff hsc hLip hmM
    hγ hfriction A R W hA hR h heA heR
  have hvelocity (t : ℝ) (ht : t ∈ Icc 0 h) : ‖(A t).1‖ ≤ C + e := by
    have hd := hdec t ht
    have hfactor : Real.exp ((-m / γ) * t) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      rw [neg_div, neg_mul]
      exact neg_nonpos.mpr (mul_nonneg (div_nonneg hm hγ.le) ht.1)
    have hproj := velocity_le_transformNorm γ (A t - R t)
    have hscaled := mul_le_mul_of_nonneg_right hfactor he
    have htriangle := norm_add_le ((A t).1 - (R t).1) (R t).1
    have hid : (A t).1 - (R t).1 + (R t).1 = (A t).1 := by abel
    rw [hid] at htriangle
    have href := hreference t ht
    change ‖(A t).1 - (R t).1‖ ≤ transformNorm γ 0 (A t - R t) at hproj
    nlinarith
  have hlocal := exponentialStep_localNorm_bound (gradient f) M hLip
    (fun t ↦ (A t).2) (fun t ↦ (A t).1) B hA.snd hA.fst hB γ h (C + e)
    hγ.le hh (add_nonneg hC he) hsmall hmild hkin hvelocity
  have htriangle := transformNorm_sub_triangle γ 0
    (exponentialStep (gradient f) γ h (A 0) (B h, ∫ s in 0..h, B s)) (A h) (R h)
  have hend := hdec h ⟨hh, le_rfl⟩
  dsimp [e] at hlocal
  nlinarith

end KineticLangevin
