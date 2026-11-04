import WassersteinMixing.SemigroupComposition
import WassersteinMixing.ActualMarkov
import WassersteinMixing.SemigroupScalar
import WassersteinMixing.SemigroupReversible
import WassersteinMixing.SemigroupPoisson

/-! # The constructed reversible Gibbs Langevin semigroup

All semigroup fields are proved for the actual canonical Brownian solution.
Markov composition comes from independent future noise and Euler limits;
self-adjointness comes from the reversible actual MALA approximation.
No spectral basis, semigroup, reversibility, or Markov hypothesis is input.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set

namespace WassersteinMixing.CanonicalSemigroup

section Real
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The actual real Langevin transitions compose at all nonnegative times. -/
theorem op_add_real (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    op (𝕜 := ℝ) (F := F) P V hV (s + t) = op P V hV s ∘L op P V hV t := by
  apply op_add_of_markov P V hV s t
  intro f
  exact actualEvaluation_markov_pastAt P V hV ⟨s, hs⟩ t ht f

end Real

section Complex
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
local instance instSemigroupInstanceReal : InnerProductSpace ℝ F :=
  InnerProductSpace.rclikeToReal ℂ F

/-- The actual complex Langevin transitions compose, by the proved real
conditional Markov identity and exact scalar restriction of adjunction. -/
theorem op_add (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    op (𝕜 := ℂ) (F := F) P V hV (s + t) = op P V hV s * op P V hV t := by
  have he := op_add_real (F := F) P V hV s t hs ht
  rw [← op_restrictScalars P V hV (s + t), ← op_restrictScalars P V hV s,
    ← op_restrictScalars P V hV t] at he
  apply ContinuousLinearMap.ext
  intro f
  exact congrArg (fun A : Lp F 2 (ULA.gibbsMeasure V) →L[ℝ]
    Lp F 2 (ULA.gibbsMeasure V) ↦ A f) he

/-- The genuine reversible strongly continuous semigroup on complex Gibbs
observables, constructed entirely from the source potential assumptions. -/
def semigroup (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V) :
    ReversibleSemigroup (Lp F 2 (ULA.gibbsMeasure V)) where
  op := op P V hV
  zero := op_zero P V hV
  add := fun {s t} hs ht ↦ op_add P V hV s t hs ht
  selfAdjoint := fun {t} ht ↦ op_isSelfAdjoint P V hV t ht
  norm_le := fun {t} _ f ↦ op_norm_le P V hV t f
  continuous := fun f ↦ continuousOn_op P V hV f

@[simp] theorem semigroup_op (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) :
    (semigroup (F := F) P V hV).op t = op (𝕜 := ℂ) P V hV t := rfl

end Complex
end WassersteinMixing.CanonicalSemigroup
