import KineticLangevin.GaussianFourth
import Mathlib.MeasureTheory.Integral.Pi

/-! # A proved chi-square positive-part tail bound -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace KineticLangevin

/-- The Gaussian exponential square moment at one third is finite and
exactly sqrt three, derived from the real Gaussian density. -/
theorem scalarGaussian_exp_square_third :
    Integrable (fun x : ℝ ↦ Real.exp (x^2/3)) (gaussianReal 0 1) ∧
      (∫ x : ℝ,Real.exp (x^2/3) ∂gaussianReal 0 1)=Real.sqrt 3 := by
  have hmul (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (x^2/3) =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/6 : ℝ)*x^2) := by
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hi : Integrable (fun x : ℝ ↦ gaussianPDFReal 0 1 x * Real.exp (x^2/3)) volume := by
    simp_rw [hmul]
    exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ)<1/6)).const_mul _
  refine ⟨?_,?_⟩
  · rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
    apply (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all volume (fun _ ↦ gaussianPDF_lt_top))).mpr
    simpa only [gaussianPDF,ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _),smul_eq_mul] using hi
  · rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
    simp_rw [smul_eq_mul,hmul]
    rw [integral_const_mul,integral_gaussian]
    have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
    have hA : Real.sqrt (2*Real.pi)^2=2*Real.pi := Real.sq_sqrt (by positivity)
    have hB : Real.sqrt (Real.pi/(1/6 : ℝ))^2=Real.pi/(1/6 : ℝ) := Real.sq_sqrt (by positivity)
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg 3)).mp
    rw [mul_pow,inv_pow,hA,hB,Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)]
    field_simp
    <;> ring

/-- The actual Euclidean standard Gaussian exponential square moment is the
product of its scalar moments, so it is finite in every finite dimension. -/
theorem stdGaussian_exp_norm_square_third (ι : Type*) [Fintype ι] :
    Integrable (fun z : EuclideanSpace ℝ ι ↦ Real.exp (‖z‖^2/3)) (stdGaussian (EuclideanSpace ℝ ι)) ∧
      (∫ z : EuclideanSpace ℝ ι,Real.exp (‖z‖^2/3) ∂stdGaussian (EuclideanSpace ℝ ι))=
        (Real.sqrt 3)^(Fintype.card ι) := by
  classical
  let μ := Measure.pi (fun _ : ι ↦ gaussianReal 0 1)
  have he (w : ι → ℝ) : Real.exp (‖WithLp.toLp 2 w‖^2/3)=∏ i : ι,Real.exp ((w i)^2/3) := by
    rw [EuclideanSpace.real_norm_sq_eq,Finset.sum_div,Real.exp_sum]
  have hi : Integrable (fun w : ι → ℝ ↦ Real.exp (‖WithLp.toLp 2 w‖^2/3)) μ := by
    simp_rw [he]
    exact Integrable.fintype_prod (fun _ ↦ scalarGaussian_exp_square_third.1)
  rw [← map_pi_eq_stdGaussian]
  refine ⟨?_,?_⟩
  · exact (integrable_map_measure (by fun_prop) (by fun_prop)).mpr hi
  · rw [integral_map (by fun_prop) (by fun_prop)]
    simp_rw [he]
    rw [integral_fintype_prod_eq_prod (fun (_ : ι) (x : ℝ) ↦ Real.exp (x^2/3))]
    simp only [scalarGaussian_exp_square_third.2,Finset.prod_const,Finset.card_univ]

/-- A rational exponential lower bound controls the scalar square moment
without invoking an unproved chi-square concentration theorem. -/
theorem sqrt_three_le_exp_two_thirds : Real.sqrt 3 ≤ Real.exp (2/3 : ℝ) := by
  have he : (4/3 : ℝ)≤Real.exp (1/3 : ℝ) := by linarith [Real.add_one_le_exp (1/3 : ℝ)]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤4/3) he 4
  have hid : Real.exp (2/3 : ℝ)^2=Real.exp (1/3 : ℝ)^4 := by
    rw [pow_two,← Real.exp_add]
    have hr : (2/3 : ℝ)+2/3=1/3+1/3+1/3+1/3 := by norm_num
    rw [hr]
    simp only [Real.exp_add]
    ring
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  rw [← hid] at hp
  norm_num at hp
  nlinarith [Real.sqrt_nonneg 3,Real.exp_pos (2/3 : ℝ)]

/-- The positive part is controlled by an exponential at the chosen tilt. -/
theorem positivePart_le_exp_third (y a : ℝ) :
    max (y-a) 0 ≤ 3*Real.exp ((y-a)/3) := by
  apply max_le
  · linarith [Real.add_one_le_exp ((y-a)/3)]
  · positivity

/-- The source-paper chi-square positive-part bound for the actual standard
Gaussian vector. It includes every finite dimension, with explicit threshold. -/
theorem stdGaussian_norm_square_positivePart_le (ι : Type*) [Fintype ι]
    (a : ℝ) (ha : 5*(Fintype.card ι : ℝ)≤a) :
    (∫ z : EuclideanSpace ℝ ι,max (‖z‖^2-a) 0 ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
      4*Real.exp (-(a-(Fintype.card ι : ℝ))/4) := by
  let μ := stdGaussian (EuclideanSpace ℝ ι)
  have hm := stdGaussian_exp_norm_square_third ι
  have hpoint (z : EuclideanSpace ℝ ι) :
      max (‖z‖^2-a) 0 ≤ (3*Real.exp (-a/3))*Real.exp (‖z‖^2/3) := by
    have h := positivePart_le_exp_third (‖z‖^2) a
    have he : (‖z‖^2-a)/3=-a/3+‖z‖^2/3 := by ring
    rw [he,Real.exp_add] at h
    nlinarith only [h]
  have hi : Integrable (fun z : EuclideanSpace ℝ ι ↦ (3*Real.exp (-a/3))*Real.exp (‖z‖^2/3)) μ :=
    hm.1.const_mul _
  have htail : Integrable (fun z : EuclideanSpace ℝ ι ↦ max (‖z‖^2-a) 0) μ := by
    apply hi.mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
    exact hpoint z
  have hb := integral_mono htail hi hpoint
  rw [integral_const_mul,hm.2] at hb
  have hp : Real.sqrt 3^(Fintype.card ι)≤Real.exp ((2/3 : ℝ)*(Fintype.card ι : ℝ)) := by
    calc
      _ ≤ Real.exp (2/3 : ℝ)^(Fintype.card ι) :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) sqrt_three_le_exp_two_thirds _
      _ = _ := by rw [← Real.exp_nat_mul];congr 1;ring
  calc
    _ ≤ (3*Real.exp (-a/3))*Real.sqrt 3^(Fintype.card ι) := hb
    _ ≤ (3*Real.exp (-a/3))*Real.exp ((2/3 : ℝ)*(Fintype.card ι : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 3*Real.exp (-a/3+(2/3 : ℝ)*(Fintype.card ι : ℝ)) := by rw [Real.exp_add];ring
    _ ≤ 3*Real.exp (-(a-(Fintype.card ι : ℝ))/4) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num : (0 : ℝ)≤3)
      linarith
    _ ≤ _ := by nlinarith [Real.exp_pos (-(a-(Fintype.card ι : ℝ))/4)]

/-- The actual chi-square tail estimate transfers to a stationary Gaussian
velocity on any source; no independence from other coupled variables is used. -/
theorem gaussian_norm_square_positivePart_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (V : Ω → EuclideanSpace ℝ ι)
    (hV : HasLaw V (stdGaussian (EuclideanSpace ℝ ι)) P)
    (a : ℝ) (ha : 5*(Fintype.card ι : ℝ)≤a) :
    (∫ ω,max (‖V ω‖^2-a) 0 ∂P)≤4*Real.exp (-(a-(Fintype.card ι : ℝ))/4) := by
  have he := hV.integral_comp (f := fun x : EuclideanSpace ℝ ι ↦ max (‖x‖^2-a) 0) (by fun_prop)
  change (∫ ω,max (‖V ω‖^2-a) 0 ∂P)=∫ x : EuclideanSpace ℝ ι,max (‖x‖^2-a) 0 ∂stdGaussian _ at he
  exact he.trans_le (stdGaussian_norm_square_positivePart_le ι a ha)

end KineticLangevin
