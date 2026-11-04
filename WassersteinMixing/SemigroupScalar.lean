import WassersteinMixing.ComplexRealTransition
import WassersteinMixing.SemigroupGlobal

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Scalar restriction of the actual Langevin transition

The complex and real compressions of the same actual observation maps agree
as real operators. This transfers the real-target Markov composition theorem
to the complex Hilbert space used in the bounded corrector construction.
-/

noncomputable section
open MeasureTheory

namespace WassersteinMixing.CanonicalSemigroup

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The actual complex transition, restricted to real scalars, is exactly the
actual real transition on the same observable target. -/
theorem op_restrictScalars (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) :
    letI : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F
    (op (𝕜 := ℂ) (F := F) P V hV t).restrictScalars ℝ =
      op (𝕜 := ℝ) (F := F) P V hV t := by
  let : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F
  ext f : 1
  apply ext_inner_right ℝ
  intro g
  have hc := ObservableTransition.compression_inner
    (evaluation (𝕜 := ℂ) (F := F) P V hV 0) (evaluation P V hV t) f g
  have hr := ObservableTransition.compression_inner
    (evaluation (𝕜 := ℝ) (F := F) P V hV 0) (evaluation P V hV t) f g
  calc
    _ = (inner ℂ (op (𝕜 := ℂ) P V hV t f) g).re :=
      RealComplexEmbedding.real_inner_Lp_eq_re _ _ _
    _ = (inner ℂ (evaluation (𝕜 := ℂ) P V hV t f)
        (evaluation (𝕜 := ℂ) P V hV 0 g)).re := congrArg Complex.re hc
    _ = inner ℝ (evaluation (𝕜 := ℝ) P V hV t f)
        (evaluation (𝕜 := ℝ) P V hV 0 g) :=
      (RealComplexEmbedding.real_inner_Lp_eq_re _ _ _).symm
    _ = _ := hr.symm

end WassersteinMixing.CanonicalSemigroup
