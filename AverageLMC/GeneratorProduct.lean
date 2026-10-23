import AverageLMC.LaplacianGenerator
import UnadjustedLangevin.Generator

set_option linter.style.header false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace AverageLMC

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem directionalDerivative_mul (χ ψ : E → ℝ) (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (v x : E) :
    directionalDerivative (fun y ↦ χ y * ψ y) v x =
      χ x * directionalDerivative ψ v x + ψ x * directionalDerivative χ v x := by
  unfold directionalDerivative
  rw [fderiv_fun_mul (hχ x) (hψ x)]
  simp [mul_comm]

theorem directionalDerivative_add (χ ψ : E → ℝ) (hχ : Differentiable ℝ χ)
    (hψ : Differentiable ℝ ψ) (v x : E) :
    directionalDerivative (fun y ↦ χ y + ψ y) v x =
      directionalDerivative χ v x + directionalDerivative ψ v x := by
  unfold directionalDerivative
  rw [fderiv_fun_add (hχ x) (hψ x)]
  rfl

/-- The exact second directional derivative product rule for C² factors. -/
theorem directionalDerivative_two_mul (χ ψ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hψ : ContDiff ℝ 2 ψ) (v x : E) :
    directionalDerivative (directionalDerivative (fun y ↦ χ y * ψ y) v) v x =
      χ x * directionalDerivative (directionalDerivative ψ v) v x +
      ψ x * directionalDerivative (directionalDerivative χ v) v x +
      2 * directionalDerivative χ v x * directionalDerivative ψ v x := by
  have hχd := hχ.differentiable (by norm_num)
  have hψd := hψ.differentiable (by norm_num)
  have hDχ := (contDiff_directionalDerivative χ hχ v).differentiable (by norm_num)
  have hDψ := (contDiff_directionalDerivative ψ hψ v).differentiable (by norm_num)
  have heq : directionalDerivative (fun y ↦ χ y * ψ y) v = fun y ↦
      χ y * directionalDerivative ψ v y + ψ y * directionalDerivative χ v y :=
    funext (directionalDerivative_mul χ ψ hχd hψd v)
  rw [heq, directionalDerivative_add (fun y ↦ χ y * directionalDerivative ψ v y)
    (fun y ↦ ψ y * directionalDerivative χ v y) (hχd.mul hDψ) (hψd.mul hDχ),
    directionalDerivative_mul χ _ hχd hDψ, directionalDerivative_mul ψ _ hψd hDχ]
  ring


/-- The exact directional generator product rule. -/
theorem directionalGenerator_mul (f χ ψ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hψ : ContDiff ℝ 2 ψ) (v x : E) :
    ULA.directionalGenerator f (fun y ↦ χ y * ψ y) v x =
      χ x * ULA.directionalGenerator f ψ v x +
      ψ x * ULA.directionalGenerator f χ v x +
      2 * directionalDerivative χ v x * directionalDerivative ψ v x := by
  change directionalDerivative (directionalDerivative (fun y ↦ χ y * ψ y) v) v x -
    inner ℝ (gradient f x) v * directionalDerivative (fun y ↦ χ y * ψ y) v x = _
  rw [directionalDerivative_two_mul χ ψ hχ hψ,
    directionalDerivative_mul χ ψ (hχ.differentiable (by norm_num))
      (hψ.differentiable (by norm_num))]
  change χ x * (fderiv ℝ (fun z ↦ fderiv ℝ ψ z v) x v) +
      ψ x * (fderiv ℝ (fun z ↦ fderiv ℝ χ z v) x v) +
      2 * fderiv ℝ χ x v * fderiv ℝ ψ x v -
      inner ℝ (gradient f x) v * (χ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ χ x v) =
    χ x * (fderiv ℝ (fun z ↦ fderiv ℝ ψ z v) x v -
      inner ℝ (gradient f x) v * fderiv ℝ ψ x v) +
    ψ x * (fderiv ℝ (fun z ↦ fderiv ℝ χ z v) x v -
      inner ℝ (gradient f x) v * fderiv ℝ χ x v) +
    2 * fderiv ℝ χ x v * fderiv ℝ ψ x v
  ring

/-- The generator product rule, including its exact gradient cross term. -/
theorem langevinGenerator_mul (f χ ψ : E → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hψ : ContDiff ℝ 2 ψ) (x : E) :
    ULA.langevinGenerator f (fun y ↦ χ y * ψ y) x =
      χ x * ULA.langevinGenerator f ψ x + ψ x * ULA.langevinGenerator f χ x +
      2 * inner ℝ (gradient χ x) (gradient ψ x) := by
  simp only [ULA.langevinGenerator, directionalGenerator_mul f χ ψ hχ hψ,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp only [directionalDerivative, ← inner_gradient_left]
  simpa only [real_inner_comm (gradient ψ x)] using
    (stdOrthonormalBasis ℝ E).sum_inner_mul_inner (gradient χ x) (gradient ψ x)

/-- A coordinate score has exactly the corresponding coordinate of the actual
gradient generator. -/
theorem langevinGenerator_coordinate_gradient {p : ℕ}
    (f : State p → ℝ) (hf : ContDiff ℝ 3 f) (j : Fin p) (x : State p) :
    ULA.langevinGenerator f (fun y ↦ (gradient f y) j) x = (gradientGenerator f x) j := by
  have hg := contDiff_gradient_of_three f hf
  have hψ : ContDiff ℝ 2 (fun y ↦ (gradient f y) j) := by
    change ContDiff ℝ 2 ((EuclideanSpace.proj j) ∘ gradient f)
    exact (EuclideanSpace.proj j).contDiff.comp hg
  have hLap := (hg.contDiffAt (x := x)).laplacian_CLM_comp_left (l := EuclideanSpace.proj j)
  change Laplacian.laplacian (fun y ↦ (gradient f y) j) x =
    (Laplacian.laplacian (gradient f) x) j at hLap
  have hd : fderiv ℝ (fun y ↦ (gradient f y) j) x =
      (EuclideanSpace.proj j).comp (fderiv ℝ (gradient f) x) := by
    exact ((EuclideanSpace.proj j).hasFDerivAt.comp x
      (hg.differentiable (by norm_num) x).hasFDerivAt).fderiv
  rw [ULA.langevinGenerator_eq_laplacian_sub_inner f _ hψ x, hLap,
    laplacian_gradient_eq_gradient_laplacian f hf,
    show inner ℝ (gradient f x) (gradient (fun y ↦ (gradient f y) j) x) =
      inner ℝ (gradient (fun y ↦ (gradient f y) j) x) (gradient f x) from real_inner_comm _ _,
    inner_gradient_left, hd]
  simp [gradientGenerator]

end AverageLMC
