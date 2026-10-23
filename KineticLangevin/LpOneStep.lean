import KineticLangevin.LpContraction
import KineticLangevin.MildError
import UnadjustedLangevin.GaussianCoordinates
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # The stochastic L² one-step inequality with a Gaussian reference

The reference velocity norm is proved from its actual standard Gaussian
marginal. The nonlinear kinetic coupling is carried out in L², where the
Bochner-integral local-error estimates and transformed triangle inequality
are precisely Minkowski's inequality for the random vectors. Stationarity
providing the Gaussian reference marginal remains explicit.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace KineticLangevin

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Every coordinate of the actual standard Gaussian vector is `N(0,1)`. -/
theorem standardGaussian_coordinate_law (i : ι) :
    HasLaw (fun x : EuclideanSpace ℝ ι ↦ x i) (gaussianReal 0 1)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  classical
  constructor
  · exact (by fun_prop : Measurable (fun x : EuclideanSpace ℝ ι ↦ x i)).aemeasurable
  · rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
    change (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)).map (Function.eval i) = gaussianReal 0 1
    rw [Measure.pi_map_eval]
    simp

/-- A standard Gaussian velocity marginal supplies the exact stationary
L² velocity moment `√p`; no moment inequality is assumed. -/
theorem gaussian_velocity_Lp_norm (P : Measure Ω)
    (V : Lp (EuclideanSpace ℝ ι) 2 P)
    (hlaw : HasLaw V (stdGaussian (EuclideanSpace ℝ ι)) P) :
    ‖V‖ = Real.sqrt (Fintype.card ι : ℝ) := by
  have hcoord (i : ι) : HasLaw (fun ω ↦ V ω i) (gaussianReal 0 1) P := by
    convert (standardGaussian_coordinate_law i).comp hlaw using 1
    funext ω
    rfl
  simpa using ULA.gaussian_coordinates_Lp_norm P V 1 hcoord

variable (P : Measure Ω) [IsFiniteMeasure P]

/-- The actual L² exponential update has the paper's stochastic one-step
bound, with an explicit upper bound on the reference velocity norm.
Its local error and contraction premises are derived from concrete integral
paths and the mild representation, rather than assumed as a recurrence. -/
theorem lp_exponentialStep_coupling_bound_of_velocity_norm
    (f : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 ≤ m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (A R W : ℝ → Lp (EuclideanSpace ℝ ι) 2 P × Lp (EuclideanSpace ℝ ι) 2 P)
    (B : ℝ → Lp (EuclideanSpace ℝ ι) 2 P)
    (hA : Continuous A) (hR : Continuous R) (hB : Continuous B)
    (h : ℝ) (hh : 0 ≤ h) (hsmall : (γ : ℝ) * h ≤ 1 / 4)
    (heA : ∀ t ∈ Icc 0 h, A t - A 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (A s)) + W t)
    (heR : ∀ t ∈ Icc 0 h, R t - R 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (R s)) + W t)
    (hmild : ∀ t ∈ Icc 0 h, (A t).1 = psi γ 0 t • (A 0).1 -
      (∫ s in 0..t, Real.exp (-(γ : ℝ) * (t - s)) •
        ULA.lpDrift P (gradient f) hLip (A s).2) + B t)
    (hkin : ∀ t ∈ Icc 0 h, (A t).2 - (A 0).2 = ∫ s in 0..t, (A s).1)
    (C : ℝ) (hC : 0 ≤ C) (hreference : ∀ t ∈ Icc 0 h, ‖(R t).1‖ ≤ C) :
    transformNorm γ 0 (exponentialStep (ULA.lpDrift P (gradient f) hLip) γ h
      (A 0) (B h, ∫ s in 0..h, B s) - R h) ≤
      Real.exp ((-m / γ) * h) * transformNorm γ 0 (A 0 - R 0) +
        (3 / 4 : ℝ) * (M : ℝ) * h ^ 2 *
          (C + transformNorm γ 0 (A 0 - R 0)) := by
  let e := transformNorm γ 0 (A 0 - R 0)
  have he : 0 ≤ e := transformNorm_nonneg _ _ _
  have hdec := lp_kinetic_integral_transformNorm_decay P f m M γ hdiff hsc hLip hmM
    hγ hfriction A R W hA hR h heA heR
  have hvelocity (t : ℝ) (ht : t ∈ Icc 0 h) :
      ‖(A t).1‖ ≤ C + e := by
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
  have hlocal := exponentialStep_localNorm_bound (ULA.lpDrift P (gradient f) hLip) M
    (ULA.lpDrift_lipschitz P (gradient f) hLip)
    (fun t ↦ (A t).2) (fun t ↦ (A t).1) B hA.snd hA.fst hB γ h
    (C + e) hγ.le hh (by positivity)
    hsmall hmild hkin hvelocity
  have htriangle := transformNorm_sub_triangle γ 0
    (exponentialStep (ULA.lpDrift P (gradient f) hLip) γ h (A 0)
      (B h, ∫ s in 0..h, B s)) (A h) (R h)
  have hend := hdec h ⟨hh, le_rfl⟩
  dsimp [e] at hlocal
  nlinarith

/-- The actual L² exponential update has the paper's stochastic one-step
bound, once the exact reference velocity marginal is standard Gaussian.
Its local error and contraction premises are derived from concrete integral
paths and the mild representation, rather than assumed as a recurrence. -/
theorem lp_exponentialStep_coupling_bound
    (f : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 ≤ m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ) ^ 2)
    (A R W : ℝ → Lp (EuclideanSpace ℝ ι) 2 P × Lp (EuclideanSpace ℝ ι) 2 P)
    (B : ℝ → Lp (EuclideanSpace ℝ ι) 2 P)
    (hA : Continuous A) (hR : Continuous R) (hB : Continuous B)
    (h : ℝ) (hh : 0 ≤ h) (hsmall : (γ : ℝ) * h ≤ 1 / 4)
    (heA : ∀ t ∈ Icc 0 h, A t - A 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (A s)) + W t)
    (heR : ∀ t ∈ Icc 0 h, R t - R 0 = -(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (R s)) + W t)
    (hmild : ∀ t ∈ Icc 0 h, (A t).1 = psi γ 0 t • (A 0).1 -
      (∫ s in 0..t, Real.exp (-(γ : ℝ) * (t - s)) •
        ULA.lpDrift P (gradient f) hLip (A s).2) + B t)
    (hkin : ∀ t ∈ Icc 0 h, (A t).2 - (A 0).2 = ∫ s in 0..t, (A s).1)
    (hreference : ∀ t ∈ Icc 0 h, HasLaw ((R t).1) (stdGaussian (EuclideanSpace ℝ ι)) P) :
    transformNorm γ 0 (exponentialStep (ULA.lpDrift P (gradient f) hLip) γ h
      (A 0) (B h, ∫ s in 0..h, B s) - R h) ≤
      Real.exp ((-m / γ) * h) * transformNorm γ 0 (A 0 - R 0) +
        (3 / 4 : ℝ) * (M : ℝ) * h ^ 2 *
          (Real.sqrt (Fintype.card ι : ℝ) + transformNorm γ 0 (A 0 - R 0)) := by
  apply lp_exponentialStep_coupling_bound_of_velocity_norm P f m M γ hdiff hsc hLip hmM
    hm hγ hfriction A R W B hA hR hB h hh hsmall heA heR hmild hkin
    (Real.sqrt (Fintype.card ι : ℝ)) (Real.sqrt_nonneg _)
  intro t ht
  exact (gaussian_velocity_Lp_norm P (R t).1 (hreference t ht)).le

end KineticLangevin
