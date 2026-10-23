import KineticLangevin.LpOneStep

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace KineticLangevin
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsFiniteMeasure P]

/-- The source auxiliary-velocity lemma follows from true synchronous contraction and the actual Gaussian reference marginal. -/
theorem lp_auxiliary_velocity_bound
    (f : EuclideanSpace ℝ ι→ℝ) (m : ℝ) (M γ : ℝ≥0) (hm : 0≤m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m≤(M : ℝ))
    (hγ : 0<(γ : ℝ)) (hfriction : m+(M : ℝ)≤(γ : ℝ)^2)
    (A R W : ℝ→Lp (EuclideanSpace ℝ ι) 2 P×Lp (EuclideanSpace ℝ ι) 2 P)
    (hA : Continuous A) (hR : Continuous R) (T : ℝ)
    (heA : ∀ t∈Icc 0 T,A t-A 0=-(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (A s))+W t)
    (heR : ∀ t∈Icc 0 T,R t-R 0=-(∫ s in 0..t,
      kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (R s))+W t)
    (t : ℝ) (ht : t∈Icc 0 T)
    (hGaussian : HasLaw (R t).1 (stdGaussian (EuclideanSpace ℝ ι)) P) :
    ‖(A t).1‖≤Real.sqrt (Fintype.card ι : ℝ)+transformNorm γ 0 (A 0-R 0) := by
  have hd := lp_kinetic_integral_transformNorm_decay P f m M γ hf hsc hLip hmM
    hγ hfriction A R W hA hR T heA heR t ht
  have he : Real.exp ((-m/γ)*t)≤1 := by
    apply Real.exp_le_one_iff.mpr
    rw [neg_div,neg_mul]
    exact neg_nonpos.mpr (mul_nonneg (div_nonneg hm hγ.le) ht.1)
  have hscale := mul_le_mul_of_nonneg_right he (transformNorm_nonneg γ 0 (A 0-R 0))
  have hp := velocity_le_transformNorm γ (A t-R t)
  have htri := norm_sub_le (A t).1 (R t).1
  have hv := norm_add_le ((A t).1-(R t).1) (R t).1
  rw [sub_add_cancel] at hv
  rw [gaussian_velocity_Lp_norm P (R t).1 hGaussian] at hv
  change ‖(A t).1-(R t).1‖≤transformNorm γ 0 (A t-R t) at hp
  nlinarith
end KineticLangevin
