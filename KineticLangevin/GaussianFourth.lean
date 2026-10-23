import UnadjustedLangevin.GaussianMoments
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.Integration

/-! # Exact fourth moments used by the Hessian-corrected kinetic scheme -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace KineticLangevin

/-- The fourth moment of a centered scalar Gaussian is three times its
variance squared, derived from its actual moment-generating function. -/
theorem centeredGaussian_fourth_moment (v : ℝ≥0) :
    (∫ x : ℝ, x^4 ∂gaussianReal 0 v) = 3*(v : ℝ)^2 := by
  have d0 (t : ℝ) : HasDerivAt (fun y : ℝ ↦ Real.exp ((v : ℝ)*y^2/2))
      ((v : ℝ)*t*Real.exp ((v : ℝ)*t^2/2)) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (v : ℝ) |>.div_const 2).exp using 1 <;>
      (try funext y) <;> simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,id_eq] <;> ring
  have d1 (t : ℝ) : HasDerivAt (fun y : ℝ ↦ ((v : ℝ)*y)*Real.exp ((v : ℝ)*y^2/2))
      (((v : ℝ)+(v : ℝ)^2*t^2)*Real.exp ((v : ℝ)*t^2/2)) t := by
    convert (((hasDerivAt_id t).const_mul (v : ℝ)).mul (d0 t)) using 1 <;>
      (try funext y) <;> simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,id_eq] <;> ring
  have d2 (t : ℝ) : HasDerivAt
      (fun y : ℝ ↦ ((v : ℝ)+(v : ℝ)^2*y^2)*Real.exp ((v : ℝ)*y^2/2))
      ((3*(v : ℝ)^2*t+(v : ℝ)^3*t^3)*Real.exp ((v : ℝ)*t^2/2)) t := by
    have hp := (hasDerivAt_const t (v : ℝ)).add (((hasDerivAt_id t).pow 2).const_mul ((v : ℝ)^2))
    convert (hp.mul (d0 t)) using 1 <;>
      (try funext y) <;> simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,id_eq] <;> ring
  have d3 : HasDerivAt
      (fun y : ℝ ↦ (3*(v : ℝ)^2*y+(v : ℝ)^3*y^3)*Real.exp ((v : ℝ)*y^2/2))
      (3*(v : ℝ)^2) 0 := by
    have hp := ((hasDerivAt_id (0 : ℝ)).const_mul (3*(v : ℝ)^2)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul ((v : ℝ)^3))
    convert (hp.mul (d0 0)) using 1 <;>
      (try funext y) <;> simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,id_eq] <;> norm_num
  have h1 := funext (fun t ↦ (d0 t).deriv)
  have h2 := funext (fun t ↦ (d1 t).deriv)
  have h3 := funext (fun t ↦ (d2 t).deriv)
  calc
    _ = iteratedDeriv 4 (mgf (fun x : ℝ ↦ x) (gaussianReal 0 v)) 0 := by
      simpa only [Pi.pow_apply] using (iteratedDeriv_mgf_zero (X := fun x : ℝ ↦ x)
        (μ := gaussianReal 0 v) (by simp) 4).symm
    _ = 3*(v : ℝ)^2 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul,zero_add]
      rw [iteratedDeriv_succ',h1,iteratedDeriv_succ',h2,iteratedDeriv_succ',h3,iteratedDeriv_one]
      exact d3.deriv

/-- The exact Gaussian norm fourth moment retains the `2p` term, including
one-dimensional targets where replacing it by `p²` would be invalid. -/
theorem stdGaussian_norm_fourth_moment (ι : Type*) [Fintype ι] :
    (∫ z : EuclideanSpace ℝ ι, ‖z‖^4 ∂stdGaussian (EuclideanSpace ℝ ι)) =
      (Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ) := by
  classical
  let μ : Measure (ι → ℝ) := Measure.pi (fun _ : ι ↦ gaussianReal 0 1)
  have hlaw (i : ι) : HasLaw (fun w : ι → ℝ ↦ w i) (gaussianReal 0 1) μ :=
    (measurePreserving_eval (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw
  have hmem4 (i : ι) : MemLp (fun w : ι → ℝ ↦ w i) 4 μ :=
    (hlaw i).memLp (memLp_id_gaussianReal (4 : ℝ≥0))
  have hi4 (i : ι) : Integrable (fun w : ι → ℝ ↦ (w i)^4) μ := by
    convert (hmem4 i).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0) using 1
    funext w
    simp only [Real.norm_eq_abs,show (4 : ℕ)=2*2 by rfl,pow_mul,sq_abs]
  have hi (i j : ι) : Integrable (fun w : ι → ℝ ↦ (w i)^2*(w j)^2) μ := by
    apply ((hi4 i).add (hi4 j)).mono' (by fun_prop)
    filter_upwards [] with w
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    change (w i)^2*(w j)^2 ≤ (w i)^4+(w j)^4
    nlinarith [sq_nonneg ((w i)^2-(w j)^2)]
  have hsecond (i : ι) : (∫ w : ι → ℝ, (w i)^2 ∂μ)=1 := by
    have he := (hlaw i).integral_comp (f := fun x : ℝ ↦ x^2) (by fun_prop)
    change (∫ w : ι → ℝ, (w i)^2 ∂μ) = ∫ x : ℝ,x^2 ∂gaussianReal 0 1 at he
    exact he.trans (ULA.centered_gaussian_second_moment 1)
  have hfourth (i : ι) : (∫ w : ι → ℝ, (w i)^4 ∂μ)=3 := by
    have he := (hlaw i).integral_comp (f := fun x : ℝ ↦ x^4) (by fun_prop)
    change (∫ w : ι → ℝ, (w i)^4 ∂μ) = ∫ x : ℝ,x^4 ∂gaussianReal 0 1 at he
    exact he.trans (by simpa using centeredGaussian_fourth_moment 1)
  have hind : iIndepFun (fun i (w : ι → ℝ) ↦ w i) μ :=
    iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)
  have hcross (i j : ι) : (∫ w : ι → ℝ, (w i)^2*(w j)^2 ∂μ) = if i=j then 3 else 1 := by
    by_cases hij : i=j
    · subst j
      simpa [← pow_add] using hfourth i
    · rw [if_neg hij]
      have hsq := (hind.indepFun hij).comp (φ := fun x : ℝ ↦ x^2) (ψ := fun x : ℝ ↦ x^2)
        (by fun_prop) (by fun_prop)
      change IndepFun (fun w : ι → ℝ ↦ (w i)^2) (fun w : ι → ℝ ↦ (w j)^2) μ at hsq
      rw [hsq.integral_fun_mul_eq_mul_integral
        (by exact (show Measurable (fun w : ι → ℝ ↦ (w i)^2) by fun_prop).aestronglyMeasurable)
        (by exact (show Measurable (fun w : ι → ℝ ↦ (w j)^2) by fun_prop).aestronglyMeasurable),hsecond i,hsecond j,one_mul]
  rw [← map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  change (∫ w : ι → ℝ, ‖WithLp.toLp 2 w‖^4 ∂μ) = _
  have hexpand (w : ι → ℝ) : ‖WithLp.toLp 2 w‖^4 =
      ∑ i : ι, ∑ j : ι, (w i)^2*(w j)^2 := by
    rw [show ‖WithLp.toLp 2 w‖^4=(‖WithLp.toLp 2 w‖^2)^2 by ring,
      EuclideanSpace.real_norm_sq_eq,pow_two,Finset.sum_mul_sum]
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ ↦ hi _ j),hcross]
  have he (i j : ι) : (if i=j then (3 : ℝ) else 1)=1+(if i=j then 2 else 0) := by
    split_ifs <;> norm_num
  simp_rw [he,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  ring

/-- The exact fourth moment transfers to any actual random vector with the
standard Gaussian law, independently of its probability-space realization. -/
theorem gaussian_vector_fourth_moment {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : Ω → EuclideanSpace ℝ ι)
    (hX : HasLaw X (stdGaussian (EuclideanSpace ℝ ι)) P) :
    (∫ ω, ‖X ω‖^4 ∂P)=(Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ) := by
  have he := hX.integral_comp (f := fun x : EuclideanSpace ℝ ι ↦ ‖x‖^4) (by fun_prop)
  change (∫ ω, ‖X ω‖^4 ∂P)=∫ x : EuclideanSpace ℝ ι, ‖x‖^4 ∂stdGaussian _ at he
  exact he.trans (stdGaussian_norm_fourth_moment ι)

end KineticLangevin
