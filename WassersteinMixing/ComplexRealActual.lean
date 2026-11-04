import WassersteinMixing.ComplexRealTransition
import WassersteinMixing.SemigroupGlobal

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual Langevin transition preserves real coordinate observables

The canonical Brownian evaluations are genuine measure-preserving maps.
Their proved pointwise naturality and adjoint identities identify the complex
transition on real observables with the actual real transition, at every time.
-/

noncomputable section
open MeasureTheory

namespace WassersteinMixing.CanonicalSemigroup

variable {R H : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- The complex canonical transition of an embedded real observable is exactly
the embedding of its actual real canonical transition. -/
theorem op_mapLp (i : R →ₗᵢ[ℝ] H) (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) (f : Lp R 2 (ULA.gibbsMeasure V)) :
    op (𝕜 := ℂ) P V hV t (RealComplexEmbedding.mapLp i (ULA.gibbsMeasure V) f) =
      RealComplexEmbedding.mapLp i (ULA.gibbsMeasure V)
        (op (𝕜 := ℝ) P V hV t f) :=
  RealComplexEmbedding.compression_mapLp i (ULA.gibbsMeasure V) (actualProbability P V)
    (state P V hV 0) (state P V hV t)
    ⟨(Lp.stronglyMeasurable _).measurable, state_law P V hV 0⟩
    ⟨(Lp.stronglyMeasurable _).measurable, state_law P V hV t⟩ f

/-- Real-range preservation is a conclusion about the actual diffusion operator. -/
theorem op_mem_real_range (i : R →ₗᵢ[ℝ] H) (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) (f : Lp R 2 (ULA.gibbsMeasure V)) :
    op (𝕜 := ℂ) P V hV t (RealComplexEmbedding.mapLp i (ULA.gibbsMeasure V) f) ∈
      Set.range (RealComplexEmbedding.mapLp i (ULA.gibbsMeasure V)) :=
  ⟨_, (op_mapLp i P V hV t f).symm⟩

/-- The actual coordinatewise complex embedding intertwines the real and complex
Langevin operators without changing the dimension or norm. -/
theorem op_coordinateLp (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ)
    (f : Lp (E P.dimension) 2 (ULA.gibbsMeasure V)) :
    op (𝕜 := ℂ) P V hV t
        (RealComplexEmbedding.coordinateLp (E P.dimension) (ULA.gibbsMeasure V) f) =
      RealComplexEmbedding.coordinateLp (E P.dimension) (ULA.gibbsMeasure V)
        (op (𝕜 := ℝ) P V hV t f) :=
  op_mapLp (RealComplexEmbedding.coordinate (E P.dimension)) P V hV t f

/-- Any semigroup assembled from the actual canonical operator automatically
preserves embedded real observables. No preservation premise is introduced. -/
theorem preservesReal_of_op_eq (i : R →ₗᵢ[ℝ] H)
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (S : ReversibleSemigroup (Lp H 2 (ULA.gibbsMeasure V)))
    (hS : ∀ t, 0 ≤ t → S.op t = op (𝕜 := ℂ) P V hV t) :
    ComplexRealCorrector.PreservesReal S
      (RealComplexEmbedding.mapLp i (ULA.gibbsMeasure V)) := by
  intro t ht f
  rw [hS t ht]
  apply (ComplexRealCorrector.projection_fixed_iff _ _).mpr
  exact op_mem_real_range i P V hV t f

/-- Adjoint extraction of the constructed complex semigroup recovers the
actual real Langevin transition itself. -/
theorem realOp_eq_op (i : R →ₗᵢ[ℝ] H)
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V)
    (S : ReversibleSemigroup (Lp H 2 (ULA.gibbsMeasure V)))
    (t : ℝ) (hS : S.op t = op (𝕜 := ℂ) P V hV t) :
    ComplexRealCorrector.realOp S (RealComplexEmbedding.mapLp i (ULA.gibbsMeasure V)) t =
      op (𝕜 := ℝ) P V hV t := by
  ext f : 1
  change (RealComplexEmbedding.mapLp i (ULA.gibbsMeasure V)).toContinuousLinearMap.adjoint
    (S.op t (RealComplexEmbedding.mapLp i (ULA.gibbsMeasure V) f)) = _
  rw [hS, op_mapLp]
  exact ComplexRealCorrector.adjoint_embed _ _

end WassersteinMixing.CanonicalSemigroup
