import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Automatic skew correction in the general frozen sampler

The manuscript's double-divergence identity for `Q exp(-H)` is proved here
from skew symmetry and C² regularity. This establishes the local differential
cancellation. Normalisation, integration by parts, nonexplosion and the
identification of stationary Fokker--Planck solutions with invariant process
laws remain separate analytic requirements.
-/

noncomputable section
open scoped BigOperators
namespace PBGSO

variable {I E : Type*} [Fintype I]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite double sum of a skew-symmetric real array is zero. -/
theorem sum_skew_eq_zero (A : I → I → ℝ) (hA : ∀ i j, A i j = -A j i) :
    ∑ i, ∑ j, A i j = 0 := by
  have h : (∑ i, ∑ j, A i j) = -(∑ i, ∑ j, A i j) := by
    calc
      (∑ i, ∑ j, A i j) = ∑ j, ∑ i, A i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -A j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact hA i j
      _ = -(∑ i, ∑ j, A i j) := by simp
  linarith

/-- The second Fréchet derivative respects negation, including at points
where derivatives use Mathlib's totalised convention. -/
theorem second_fderiv_neg (f : E → ℝ) (z u v : E) :
    fderiv ℝ (fderiv ℝ (-f)) z u v =
      -(fderiv ℝ (fderiv ℝ f) z u v) := by
  have h : fderiv ℝ (-f) = -(fderiv ℝ f) :=
    funext fun x => fderiv_neg
  rw [h, fderiv_neg]
  rfl

/-- Mixed derivatives commute for each C² component. Their finite
contraction against a skew-symmetric field therefore vanishes. -/
theorem skew_second_divergence_zero (A : I → I → E → ℝ) (v : I → E)
    (hA : ∀ i j, ContDiff ℝ 2 (A i j))
    (hskew : ∀ i j z, A i j z = -A j i z) (z : E) :
    ∑ i, ∑ j, fderiv ℝ (fderiv ℝ (A i j)) z (v i) (v j) = 0 := by
  apply sum_skew_eq_zero
  intro i j
  have hfun : A i j = -(A j i) := funext fun x => hskew i j x
  rw [hfun, second_fderiv_neg]
  congr 1
  exact ((hA j i).contDiffAt.isSymmSndFDerivAt (by norm_num)).eq (v i) (v j)

/-- The exact skew double-divergence cancellation in the manuscript's
generalised Langevin construction. Taking `v` to be coordinate basis
vectors gives the stated sum of mixed partial derivatives. -/
theorem skew_gibbs_second_divergence_zero
    (Q : I → I → E → ℝ) (H : E → ℝ) (v : I → E)
    (hQ : ∀ i j, ContDiff ℝ 2 (Q i j)) (hH : ContDiff ℝ 2 H)
    (hskew : ∀ i j z, Q i j z = -Q j i z) (z : E) :
    ∑ i, ∑ j,
      fderiv ℝ (fderiv ℝ (fun x => Q i j x * Real.exp (-H x))) z
        (v i) (v j) = 0 := by
  apply skew_second_divergence_zero
  · intro i j
    exact (hQ i j).mul hH.neg.exp
  · intro i j x
    rw [hskew i j x]
    ring

end PBGSO
