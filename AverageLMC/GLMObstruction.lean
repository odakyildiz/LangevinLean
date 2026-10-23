import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option linter.style.header false

/-!
# A deterministic obstruction to the isotropic GLM Hessian estimate

The GLM proposition in `papers/Average_LMC/Arxiv_version_May_26.tex` asserts
`M₂ ≤ C n` when `p ≤ n` and the covariance is the identity.  Consider instead
`g₁(t) = t² - sin t` and `gᵢ(t) = t²` for the other components.  All component
second derivatives are at least one and their second plus third derivative
absolute values are at most four.

The full potential's Hessian has the form
`Q + sin ⟪a, x⟫ • rankOne a a`, where `Q` is the constant quadratic Hessian
and `a` is the first design row.  This file proves that every operator-norm
Lipschitz bound for this explicit Hessian is at least `‖a‖³`.

This is a counterexample ingredient, not a formalization of the paper's
convergence theorems.  The Gaussian probability argument is separate.
-/

noncomputable section

open scoped InnerProductSpace

namespace AverageLMC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The component with nonzero third derivative. -/
def oscillatingComponent (t : ℝ) : ℝ := t ^ 2 - Real.sin t

/-- Its first derivative. -/
def oscillatingComponentGradient (t : ℝ) : ℝ := 2 * t - Real.cos t

/-- Its second derivative. -/
def oscillatingComponentHessian (t : ℝ) : ℝ := 2 + Real.sin t

lemma hasDerivAt_oscillatingComponent (t : ℝ) :
    HasDerivAt oscillatingComponent (oscillatingComponentGradient t) t := by
  change HasDerivAt (fun u : ℝ => u ^ 2 - Real.sin u) (2 * t - Real.cos t) t
  convert ((hasDerivAt_id t).pow 2).sub (Real.hasDerivAt_sin t) using 1 <;> first | rfl | norm_num

lemma hasDerivAt_oscillatingComponentGradient (t : ℝ) :
    HasDerivAt oscillatingComponentGradient (oscillatingComponentHessian t) t := by
  change HasDerivAt (fun u : ℝ => 2 * u - Real.cos u) (2 + Real.sin t) t
  convert ((hasDerivAt_id t).const_mul 2).sub (Real.hasDerivAt_cos t) using 1 <;>
    first | rfl | norm_num

lemma hasDerivAt_oscillatingComponentHessian (t : ℝ) :
    HasDerivAt oscillatingComponentHessian (Real.cos t) t := by
  change HasDerivAt (fun u : ℝ => 2 + Real.sin u) (Real.cos t) t
  exact (Real.hasDerivAt_sin t).const_add 2

lemma oscillatingComponentHessian_lower (t : ℝ) :
    1 ≤ oscillatingComponentHessian t := by
  dsimp [oscillatingComponentHessian]
  linarith [Real.neg_one_le_sin t]

lemma oscillatingComponent_derivative_bound (t : ℝ) :
    |oscillatingComponentHessian t| + |Real.cos t| ≤ 4 := by
  rw [abs_of_nonneg (by linarith [oscillatingComponentHessian_lower t])]
  dsimp [oscillatingComponentHessian]
  linarith [Real.sin_le_one t, abs_le.mpr ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩]

lemma oscillatingComponent_contDiff : ContDiff ℝ ⊤ oscillatingComponent := by
  unfold oscillatingComponent
  fun_prop

lemma oscillatingComponent_convex : ConvexOn ℝ Set.univ oscillatingComponent := by
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    oscillatingComponent_contDiff.continuous.continuousOn
    (fun x _ => (hasDerivAt_oscillatingComponent x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_oscillatingComponentGradient x).hasDerivWithinAt)
  intro x _
  linarith [oscillatingComponentHessian_lower x]

/-- A fixed component family satisfying the paper's component hypotheses with
`C_g = 4`, independently of the dimension and sample size. -/
def counterexampleComponent {ι : Type*} [DecidableEq ι] (i₀ i : ι) (t : ℝ) : ℝ :=
  if i = i₀ then oscillatingComponent t else t ^ 2

lemma counterexampleComponent_contDiff {ι : Type*} [DecidableEq ι] (i₀ i : ι) :
    ContDiff ℝ ⊤ (counterexampleComponent i₀ i) := by
  by_cases hi : i = i₀
  · have heq : counterexampleComponent i₀ i = oscillatingComponent := by
      funext t
      simp [counterexampleComponent, hi]
    rw [heq]
    exact oscillatingComponent_contDiff
  · have heq : counterexampleComponent i₀ i = fun t : ℝ => t ^ 2 := by
      funext t
      simp [counterexampleComponent, hi]
    rw [heq]
    fun_prop

lemma counterexampleComponent_convex {ι : Type*} [DecidableEq ι] (i₀ i : ι) :
    ConvexOn ℝ Set.univ (counterexampleComponent i₀ i) := by
  by_cases hi : i = i₀
  · have heq : counterexampleComponent i₀ i = oscillatingComponent := by
      funext t
      simp [counterexampleComponent, hi]
    rw [heq]
    exact oscillatingComponent_convex
  · have heq : counterexampleComponent i₀ i = fun t : ℝ => t ^ 2 := by
      funext t
      simp [counterexampleComponent, hi]
    rw [heq]
    exact even_two.convexOn_pow

/-- The uniform bound is on actual second and third derivatives, not on
separately supplied candidate derivative functions. -/
lemma counterexampleComponent_derivative_bound {ι : Type*} [DecidableEq ι]
    (i₀ i : ι) (t : ℝ) :
    |deriv (deriv (counterexampleComponent i₀ i)) t| +
      |deriv (deriv (deriv (counterexampleComponent i₀ i))) t| ≤ 4 := by
  have hg₁ : deriv oscillatingComponent = oscillatingComponentGradient :=
    funext fun x => (hasDerivAt_oscillatingComponent x).deriv
  have hg₂ : deriv oscillatingComponentGradient = oscillatingComponentHessian :=
    funext fun x => (hasDerivAt_oscillatingComponentGradient x).deriv
  have hg₃ : deriv oscillatingComponentHessian = Real.cos :=
    funext fun x => (hasDerivAt_oscillatingComponentHessian x).deriv
  by_cases hi : i = i₀
  · have heq : counterexampleComponent i₀ i = oscillatingComponent := by
      funext u
      simp [counterexampleComponent, hi]
    rw [heq, hg₁, hg₂, hg₃]
    exact oscillatingComponent_derivative_bound t
  · have hq : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
      funext x
      simp
    have heq : counterexampleComponent i₀ i = fun t : ℝ => t ^ 2 := by
      funext u
      simp [counterexampleComponent, hi]
    rw [heq, hq, deriv_const_mul_id']
    norm_num

/-- The explicit Hessian in the GLM counterexample, with arbitrary constant
quadratic part `Q` and first design vector `a`. -/
def glmHessian (Q : E →L[ℝ] E) (a x : E) : E →L[ℝ] E :=
  Q + Real.sin (inner ℝ a x) • InnerProductSpace.rankOne ℝ a a

/-- The actual gradient whose derivative is the displayed Hessian. -/
def glmGradient (Q : E →L[ℝ] E) (a x : E) : E :=
  Q x - Real.cos (inner ℝ a x) • a

lemma hasFDerivAt_glmGradient (Q : E →L[ℝ] E) (a x : E) :
    HasFDerivAt (glmGradient Q a) (glmHessian Q a x) x := by
  convert Q.hasFDerivAt.sub (((innerSL ℝ a).hasFDerivAt.cos).smul_const a) using 1
  · rfl
  · ext v
    simp [glmHessian, InnerProductSpace.rankOne_apply, smul_smul]

/-- A finite-sum GLM potential, with one oscillating component and quadratic
components at every other index. -/
def counterexamplePotential {ι : Type*} [Fintype ι] (X : ι → E) (i₀ : ι) (x : E) : ℝ :=
  (∑ i, (inner ℝ (X i) x) ^ 2) - Real.sin (inner ℝ (X i₀) x)

/-- The actual potential is exactly a finite-sum GLM with the certified
component family. -/
lemma counterexamplePotential_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → E) (i₀ : ι) (x : E) :
    counterexamplePotential X i₀ x =
      ∑ i, counterexampleComponent i₀ i (inner ℝ (X i) x) := by
  have ht (i : ι) : counterexampleComponent i₀ i (inner ℝ (X i) x) =
      (inner ℝ (X i) x) ^ 2 - if i = i₀ then Real.sin (inner ℝ (X i) x) else 0 := by
    by_cases hi : i = i₀ <;> simp [counterexampleComponent, oscillatingComponent, hi]
  simp_rw [ht]
  simp [counterexamplePotential, Finset.sum_sub_distrib]

lemma counterexamplePotential_contDiff {ι : Type*} [Fintype ι]
    (X : ι → E) (i₀ : ι) : ContDiff ℝ ⊤ (counterexamplePotential X i₀) := by
  have hi (i : ι) : ContDiff ℝ ⊤ (fun x : E => inner ℝ (X i) x) :=
    (innerSL ℝ (X i)).contDiff
  have hsum := ContDiff.sum (s := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => (hi i).pow 2)
  exact hsum.sub (hi i₀).sin

/-- The constant part of its Hessian. -/
def quadraticHessian {ι : Type*} [Fintype ι] (X : ι → E) : E →L[ℝ] E :=
  ∑ i, (2 : ℝ) • InnerProductSpace.rankOne ℝ (X i) (X i)

/-- Identification of the derivative of the actual finite-sum potential with
the score used above. -/
lemma hasFDerivAt_counterexamplePotential {ι : Type*} [Fintype ι]
    (X : ι → E) (i₀ : ι) (x : E) :
    HasFDerivAt (counterexamplePotential X i₀)
      (innerSL ℝ (glmGradient (quadraticHessian X) (X i₀) x)) x := by
  have hsum := HasFDerivAt.sum (u := Finset.univ)
    (fun i (_ : i ∈ Finset.univ) => ((innerSL ℝ (X i)).hasFDerivAt (x := x)).pow 2)
  convert hsum.sub ((innerSL ℝ (X i₀)).hasFDerivAt.sin) using 1
  · funext y
    simp [counterexamplePotential]
  · ext v
    simp [glmGradient, quadraticHessian, InnerProductSpace.rankOne_apply, mul_assoc]

/-- The vector field is the actual mathematical gradient of the finite-sum
potential, not a separately assumed score. -/
lemma gradient_counterexamplePotential [CompleteSpace E] {ι : Type*} [Fintype ι]
    (X : ι → E) (i₀ : ι) :
    gradient (counterexamplePotential X i₀) = glmGradient (quadraticHessian X) (X i₀) := by
  apply gradient_eq
  intro x
  exact hasFDerivAt_counterexamplePotential X i₀ x

/-- The displayed operator is the actual derivative of the actual gradient. -/
lemma fderiv_gradient_counterexamplePotential [CompleteSpace E] {ι : Type*} [Fintype ι]
    (X : ι → E) (i₀ : ι) (x : E) :
    fderiv ℝ (gradient (counterexamplePotential X i₀)) x =
      glmHessian (quadraticHessian X) (X i₀) x := by
  rw [gradient_counterexamplePotential]
  exact (hasFDerivAt_glmGradient (quadraticHessian X) (X i₀) x).fderiv

/-- Along the design vector, the Hessian derivative at zero has norm `‖a‖⁴`.
The path itself has speed `‖a‖`, giving the cubic Lipschitz lower bound. -/
lemma hasDerivAt_glmHessian_line (Q : E →L[ℝ] E) (a : E) :
    HasDerivAt (fun t : ℝ => glmHessian Q a (t • a))
      ((‖a‖ ^ 2) • InnerProductSpace.rankOne ℝ a a) 0 := by
  have hs : HasDerivAt (fun t : ℝ => Real.sin (t * ‖a‖ ^ 2)) (‖a‖ ^ 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (‖a‖ ^ 2)).sin
  simpa [glmHessian, inner_smul_right, real_inner_self_eq_norm_sq] using
    (hs.smul_const (InnerProductSpace.rankOne ℝ a a)).const_add Q

/-- Every operator-norm Lipschitz constant for the actual explicit GLM Hessian
must be at least the cube of the first design vector's norm. -/
theorem glmHessian_lipschitz_lower (Q : E →L[ℝ] E) (a : E) {M : ℝ}
    (hM : 0 ≤ M)
    (hlip : ∀ x y : E, ‖glmHessian Q a x - glmHessian Q a y‖ ≤ M * ‖x - y‖) :
    ‖a‖ ^ 3 ≤ M := by
  have hb : ‖deriv (fun t : ℝ => glmHessian Q a (t • a)) 0‖ ≤ M * ‖a‖ := by
    apply norm_deriv_le_of_lip' (mul_nonneg hM (norm_nonneg a))
    filter_upwards [] with t
    simp only [zero_smul]
    calc
      _ ≤ M * ‖t • a - (0 : E)‖ := hlip (t • a) (0 : E)
      _ = (M * ‖a‖) * ‖t - (0 : ℝ)‖ := by
        simp only [sub_zero, norm_smul, Real.norm_eq_abs]
        ring
  rw [(hasDerivAt_glmHessian_line Q a).deriv, norm_smul,
    InnerProductSpace.norm_rankOne, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖a‖)] at hb
  by_cases ha : a = 0
  · simpa [ha] using hM
  · have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    nlinarith

/-- A cubic lower bound stated directly using the Hessian of the actual
finite-sum GLM potential. -/
theorem counterexamplePotential_hessian_lipschitz_lower [CompleteSpace E]
    {ι : Type*} [Fintype ι] (X : ι → E) (i₀ : ι) {M : ℝ} (hM : 0 ≤ M)
    (hlip : ∀ x y : E,
      ‖fderiv ℝ (gradient (counterexamplePotential X i₀)) x -
        fderiv ℝ (gradient (counterexamplePotential X i₀)) y‖ ≤ M * ‖x - y‖) :
    ‖X i₀‖ ^ 3 ≤ M := by
  apply glmHessian_lipschitz_lower (quadraticHessian X) (X i₀) hM
  simpa only [fderiv_gradient_counterexamplePotential] using hlip

end AverageLMC
