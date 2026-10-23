import KineticLangevin.FreeOUCorrection
import KineticLangevin.Geometry
import KineticLangevin.GaussianTruncation
import KineticLangevin.RandomOperatorLp

/-! # A sharp transformed bound for the complete random Hessian correction -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace KineticLangevin

section Integrals
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniformly bounded actual velocity has a linearly bounded primitive. -/
theorem norm_primitive_le_linear (U : ℝ→E) (C t : ℝ) (ht : 0≤t)
    (hbound : ∀ r∈Icc 0 t,‖U r‖≤C) : ‖∫ r in 0..t,U r‖≤C*t := by
  have hp : ∀ r∈uIoc 0 t,‖U r‖≤C := by
    intro r hr
    rw [uIoc_of_le ht] at hr
    exact hbound r ⟨hr.1.le,hr.2⟩
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=t) (C:=C) (f:=U) hp
  simpa only [sub_zero,abs_of_nonneg ht] using hb

/-- The exact second primitive of a bounded velocity has the sharp quadratic coefficient. -/
theorem norm_double_primitive_le_quadratic (U : ℝ→E) (C t : ℝ) (ht : 0≤t)
    (hbound : ∀ r∈Icc 0 t,‖U r‖≤C) :
    ‖∫ s in 0..t,∫ r in 0..s,U r‖≤C*t^2/2 := by
  calc
    _ ≤ ∫ s in 0..t,C*s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht
      · exact Filter.Eventually.of_forall (fun s hs ↦
          norm_primitive_le_linear U C s hs.1.le (fun r hr ↦ hbound r ⟨hr.1,hr.2.trans hs.2⟩))
      · exact (by fun_prop : Continuous (fun s : ℝ ↦ C*s)).intervalIntegrable 0 t
    _ = _ := by rw [intervalIntegral.integral_const_mul,integral_id];ring

/-- Damping cannot enlarge the same exact quadratic primitive bound. -/
theorem norm_damped_primitive_le_quadratic (U : ℝ→E) (γ C t : ℝ)
    (hγ : 0≤γ) (hC : 0≤C) (ht : 0≤t) (hbound : ∀ r∈Icc 0 t,‖U r‖≤C) :
    ‖∫ s in 0..t,Real.exp (-γ*(t-s)) • ∫ r in 0..s,U r‖≤C*t^2/2 := by
  calc
    _ ≤ ∫ s in 0..t,C*s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht
      · apply Filter.Eventually.of_forall
        intro s hs
        have hi := norm_primitive_le_linear U C s hs.1.le
          (fun r hr ↦ hbound r ⟨hr.1,hr.2.trans hs.2⟩)
        have he : Real.exp (-γ*(t-s))≤1 := by
          rw [Real.exp_le_one_iff]
          exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) (sub_nonneg.mpr hs.2)
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        calc
          _ ≤ Real.exp (-γ*(t-s))*(C*s) := mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le
          _ ≤ C*s := by nlinarith [mul_nonneg (sub_nonneg.mpr he) (mul_nonneg hC hs.1.le)]
      · exact (by fun_prop : Continuous (fun s : ℝ ↦ C*s)).intervalIntegrable 0 t
    _ = _ := by rw [intervalIntegral.integral_const_mul,integral_id];ring
end Integrals

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] (P : Measure Ω)

/-- The full transformed Hessian-difference correction has the sharp quadratic time coefficient. -/
theorem freeOUCorrection_transformNorm_bound
    (A : Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V : Lp (EuclideanSpace ℝ ι) 2 P) (γ C : ℝ) (a : ℝ≥0)
    (hγ : 0≤γ) (hC : 0≤C) (t : ℝ) (ht : 0≤t)
    (hbound : ∀ r∈Icc 0 t,‖A (freeOUResponse P L V γ a 0 r)‖≤C) :
    transformNorm γ 0 (A (freeOUCorrection P L V γ a 1 t),A (freeOUCorrection P L V γ a 2 t))≤
      Real.sqrt 2*t^2*C/2 := by
  let U := fun r ↦ A (freeOUResponse P L V γ a 0 r)
  have hdouble : A (freeOUResponse P L V γ a 2 t)=∫ s in 0..t,∫ r in 0..s,U r := by
    rw [apply_freeOUResponse_primitive P A L V γ a 1 t ht]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [uIcc_of_le ht] at hs
    exact apply_freeOUResponse_primitive P A L V γ a 0 s hs.1
  have hfirst : ‖A (freeOUResponse P L V γ a 2 t)‖≤C*t^2/2 := by
    rw [hdouble]
    exact norm_double_primitive_le_quadratic U C t ht hbound
  have hsecond : ‖A (freeOUCorrection P L V γ a 1 t)‖≤C*t^2/2 := by
    rw [apply_freeOUCorrection_phi_two P A L V γ a hγ t ht]
    exact norm_damped_primitive_le_quadratic U γ C t hγ hC ht hbound
  have hbalance : A (freeOUCorrection P L V γ a 1 t)+γ • A (freeOUCorrection P L V γ a 2 t)=
      A (freeOUResponse P L V γ a 2 t) := by
    rw [← map_smul,← map_add,freeOUCorrection_balance P L V γ a t]
  apply transformNorm_le_of_energy_le _ _ _ _ (by positivity)
  simp only [transformEnergy,transform,sub_zero,zero_smul,norm_neg,hbalance]
  have hs1 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤C*t^2/2)).2 hfirst
  have hs2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤C*t^2/2)).2 hsecond
  calc
    _ ≤ 2*(C*t^2/2)^2 := by nlinarith only [hs1,hs2]
    _ = _ := by simp only [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)];ring

/-- The repaired random Hessian correction obeys the Gaussian cutoff bound using only free-OU marginals. -/
theorem freeOUCorrection_gaussian_transformNorm_bound [IsProbabilityMeasure P]
    (A : Lp (EuclideanSpace ℝ ι) 2 P →L[ℝ] Lp (EuclideanSpace ℝ ι) 2 P)
    (L : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P)
    (V X : Lp (EuclideanSpace ℝ ι) 2 P) (γ B M₂ α : ℝ) (a : ℝ≥0)
    (hγ : 0≤γ) (hB : 0≤B) (hM₂ : 0≤M₂) (hα : 5*(Fintype.card ι : ℝ)≤α)
    (t : ℝ) (ht : 0≤t)
    (hGaussian : ∀ r∈Icc 0 t,HasLaw (freeOUResponse P L V γ a 0 r) (stdGaussian (EuclideanSpace ℝ ι)) P)
    (hpoint : ∀ r∈Icc 0 t,∀ᵐ ω ∂P,‖(A (freeOUResponse P L V γ a 0 r)) ω‖≤
      min B (M₂*‖X ω‖)*‖freeOUResponse P L V γ a 0 r ω‖) :
    transformNorm γ 0 (A (freeOUCorrection P L V γ a 1 t),A (freeOUCorrection P L V γ a 2 t))≤
      Real.sqrt 2*t^2*(M₂*Real.sqrt α*‖X‖+2*B*Real.exp (-(α-(Fintype.card ι : ℝ))/8))/2 := by
  apply freeOUCorrection_transformNorm_bound P A L V γ _ a hγ (by positivity) t ht
  intro r hr
  exact gaussian_truncation_Lp P (A (freeOUResponse P L V γ a 0 r)) X (freeOUResponse P L V γ a 0 r)
    (hGaussian r hr) B M₂ α hB hM₂ hα (hpoint r hr)

/-- Actual bounded random Hessian multiplication satisfies the cutoff hypothesis from its two genuine operator bounds. -/
theorem randomOperatorLp_gaussian_truncation [IsProbabilityMeasure P]
    (H : Ω→EuclideanSpace ℝ ι→L[ℝ] EuclideanSpace ℝ ι)
    (hH : AEStronglyMeasurable H P) (B M₂ α : ℝ) (hB : 0≤B) (hM₂ : 0≤M₂)
    (hbound : ∀ᵐ ω ∂P,‖H ω‖≤B)
    (X V : Lp (EuclideanSpace ℝ ι) 2 P)
    (hLip : ∀ᵐ ω ∂P,‖H ω‖≤M₂*‖X ω‖)
    (hV : HasLaw V (stdGaussian (EuclideanSpace ℝ ι)) P) (hα : 5*(Fintype.card ι : ℝ)≤α) :
    ‖randomOperatorLp P H hH B hbound V‖≤
      M₂*Real.sqrt α*‖X‖+2*B*Real.exp (-(α-(Fintype.card ι : ℝ))/8) := by
  apply gaussian_truncation_Lp P (randomOperatorLp P H hH B hbound V) X V hV B M₂ α hB hM₂ hα
  filter_upwards [randomOperatorLp_coe P H hH B hbound V,hbound,hLip] with ω hω hBω hLipω
  rw [hω]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (le_min hBω hLipω) (norm_nonneg _))

end KineticLangevin
