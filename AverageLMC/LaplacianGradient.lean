import AverageLMC.ScoreMoment
import AverageLMC.PathwiseEnergy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option linter.style.header false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace AverageLMC

/-- A fixed directional derivative, using the actual Fréchet derivative. -/
def directionalDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (v : E) : E → ℝ := fun x ↦ fderiv ℝ f x v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiff_directionalDerivative {n : ℕ} (f : E → ℝ)
    (hf : ContDiff ℝ (n + 1) f) (v : E) :
    ContDiff ℝ n (directionalDerivative f v) :=
  (hf.fderiv_right (m := n) (by norm_cast)).clm_apply contDiff_const

theorem directionalDerivative_two (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (u v x : E) :
    directionalDerivative (directionalDerivative f v) u x =
      fderiv ℝ (fderiv ℝ f) x u v := by
  unfold directionalDerivative
  rw [fderiv_clm_apply
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
    (differentiableAt_const _)]
  simp

/-- Schwarz symmetry for two actual directional derivatives. -/
theorem directionalDerivative_commute (f : E → ℝ) (hf : ContDiff ℝ 2 f) (u v : E) :
    directionalDerivative (directionalDerivative f v) u =
      directionalDerivative (directionalDerivative f u) v := by
  funext x
  rw [directionalDerivative_two f hf, directionalDerivative_two f hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by norm_num)) u v

/-- Three derivatives commute under C³ regularity; analyticity is not used. -/
theorem directionalDerivative_three (f : E → ℝ) (hf : ContDiff ℝ 3 f)
    (u v : E) :
    directionalDerivative (directionalDerivative (directionalDerivative f v) u) u =
      directionalDerivative (directionalDerivative (directionalDerivative f u) u) v := by
  rw [directionalDerivative_commute f (hf.of_le (by norm_num)) u v]
  exact directionalDerivative_commute (directionalDerivative f u)
    (contDiff_directionalDerivative f hf u) u v

/-- The Laplacian is the sum of second directional derivatives in the
canonical Euclidean basis. -/
theorem laplacian_eq_directionalDerivative {p : ℕ} (f : State p → ℝ)
    (hf : ContDiff ℝ 2 f) :
    laplacian f = fun x ↦ ∑ i : Fin p,
      directionalDerivative (directionalDerivative f (coordinateVector i)) (coordinateVector i) x := by
  funext x
  rw [laplacian, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin p) ℝ)]
  apply Finset.sum_congr rfl
  intro i _
  rw [directionalDerivative_two f hf]
  simp [iteratedFDeriv_two_apply, coordinateVector, EuclideanSpace.basisFun_apply]

/-- The coordinate of the actual gradient is its directional derivative. -/
theorem gradient_coordinate_directionalDerivative {p : ℕ} (f : State p → ℝ) (j : Fin p) :
    (fun x ↦ (gradient f x) j) = directionalDerivative f (coordinateVector j) := by
  funext x
  simp only [directionalDerivative, ← inner_gradient_left, inner_coordinateVector]

/-- Differentiating a finite sum of differentiable scalar observables commutes
with the finite sum. -/
theorem directionalDerivative_sum {ι : Type*} [Fintype ι]
    (g : ι → E → ℝ) (hg : ∀ i, Differentiable ℝ (g i)) (v x : E) :
    directionalDerivative (fun y ↦ ∑ i, g i y) v x =
      ∑ i, directionalDerivative (g i) v x := by
  unfold directionalDerivative
  rw [fderiv_fun_sum (fun i _ ↦ hg i x)]
  simp

/-- The actual gradient is C² whenever the potential is C³. -/
theorem contDiff_gradient_of_three {p : ℕ} (f : State p → ℝ) (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 2 (gradient f) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (State p)).symm.contDiff.comp
    (hf.fderiv_right (m := 2) (by norm_num))

/-- The true vector Laplacian commutes with the actual gradient under exactly
C³ regularity. -/
theorem laplacian_gradient_eq_gradient_laplacian {p : ℕ}
    (f : State p → ℝ) (hf : ContDiff ℝ 3 f) (x : State p) :
    Laplacian.laplacian (gradient f) x = gradient (laplacian f) x := by
  have hgrad := contDiff_gradient_of_three f hf
  ext j
  have hp := (hgrad.contDiffAt (x := x)).laplacian_CLM_comp_left (l := EuclideanSpace.proj j)
  change Laplacian.laplacian (fun x ↦ (gradient f x) j) x =
    (Laplacian.laplacian (gradient f) x) j at hp
  rw [← hp]
  rw [gradient_coordinate_directionalDerivative f j]
  rw [show (gradient (laplacian f) x) j = directionalDerivative (laplacian f)
    (coordinateVector j) x from congrFun (gradient_coordinate_directionalDerivative (laplacian f) j) x]
  change laplacian (directionalDerivative f (coordinateVector j)) x =
    directionalDerivative (laplacian f) (coordinateVector j) x
  rw [laplacian_eq_directionalDerivative _ (contDiff_directionalDerivative f hf _),
    laplacian_eq_directionalDerivative f (hf.of_le (by norm_num))]
  rw [directionalDerivative_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact congrFun (directionalDerivative_three f hf (coordinateVector i) (coordinateVector j)) x
  · intro i
    exact (contDiff_directionalDerivative _
      (contDiff_directionalDerivative f hf (coordinateVector i)) (coordinateVector i)).differentiable
      (by norm_num)

end AverageLMC
