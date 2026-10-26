import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # A globally Lipschitz C¹ field agreeing near a compact orbit

A compactly supported smooth scalar cutoff leaves the vector field unchanged
on an open neighborhood of the compact set. The cut-off field is C¹ and its
global Lipschitz constant is derived from the compact support of its actual
derivative. This is a localization tool, not a global Lipschitz assumption on
the original field.
-/
noncomputable section
open Set Metric
open scoped NNReal ContDiff
namespace PBGSO

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A primitive C¹ field has a C¹ globally Lipschitz replacement agreeing on
an open neighborhood of any given compact set. -/
theorem exists_global_lipschitz_C1_cutoff (f : E → F) (hf : ContDiff ℝ 1 f)
    (K : Set E) (hK : IsCompact K) :
    ∃ (g : E → F) (L : ℝ≥0) (U : Set E),
      IsOpen U ∧ K ⊆ U ∧ EqOn g f U ∧ ContDiff ℝ 1 g ∧
        LipschitzWith L g ∧ HasCompactSupport g := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : E)
  let r : ℝ := max R 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let b : ContDiffBump (0 : E) :=
    { rIn := r
      rOut := r + 1
      rIn_pos := hr
      rIn_lt_rOut := by linarith }
  let g : E → F := fun x => b x • f x
  have hc : ContDiff ℝ 1 g := b.contDiff.smul hf
  have hs : HasCompactSupport g := b.hasCompactSupport.smul_right
  obtain ⟨L, hL⟩ := hc.lipschitzWith_of_hasCompactSupport hs (by norm_num)
  refine ⟨g, L, ball 0 r, isOpen_ball, ?_, ?_, hc, hL, hs⟩
  · exact hR.trans (ball_subset_ball (le_max_left _ _))
  · intro x hx
    dsimp [g]
    rw [b.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]

end PBGSO
