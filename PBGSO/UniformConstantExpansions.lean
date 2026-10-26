import PBGSO.MomentumUniformDefect
import PBGSO.HOLRestartLocal

/-! # Closed arithmetic formulas for the uniform numerical constants

These definitions only expand coefficients already proved in the local-error
analysis.  The identities below make the displayed constants checkable without
following the internal consistency-budget definitions.
-/
noncomputable section
open scoped NNReal
namespace PBGSO.Methods

/-- Closed state-independent M-MFPO local-error coefficient. -/
def momentumExpandedConstant0 (L γ fzero Ξ β : ℝ) : ℝ :=
  ((γ + 1) / 2 + L / 4) * fzero +
    (L / 2 + Real.sqrt γ + (3 / 2 : ℝ) * γ * Real.sqrt γ) * Ξ +
    (2 / 3 : ℝ) * (L + γ + 1) *
      (fzero + (L + γ + 1) * Real.exp (L + γ + 2) * (fzero + β) + β)

/-- Closed initial-radius M-MFPO local-error coefficient. -/
def momentumExpandedConstant1 (L γ : ℝ) : ℝ :=
  (γ ^ 2 + γ + L) / 2 + ((γ + 1) / 2 + L / 4) * L +
    (2 / 3 : ℝ) * (L + γ + 1) ^ 2 * Real.exp (L + γ + 2)

theorem momentumUniformDefect_expanded (L γ : ℝ≥0) (fzero Ξ β : ℝ) :
    momentumUniformDefect L γ fzero Ξ β =
      (momentumExpandedConstant0 L γ fzero Ξ β,
       momentumExpandedConstant1 L γ) := by
  have he : (L : ℝ) + (γ : ℝ) + 1 + 1 = (L : ℝ) + (γ : ℝ) + 2 := by ring
  simp only [momentumUniformDefect, momentumDefectAffine,
    momentumExpandedConstant0, momentumExpandedConstant1, NNReal.coe_add,
    NNReal.coe_one, he]
  ext <;> ring

/-- The exact simplified HOL `μ32` remainder budget. -/
def holExpandedRemainder32 (α γ : ℝ) : ℝ :=
  2 * γ ^ 3 / α + γ ^ 3 / 2 + γ * α / 2

/-- The exact simplified HOL `μ33` remainder budget. -/
def holExpandedRemainder33 (α γ : ℝ) : ℝ :=
  3 * γ ^ 2 / 2 + α ^ 2 / 2 + α * γ ^ 2 / 2

theorem holRemainder32_expanded (α γ : ℝ) (hα : α ≠ 0) :
    (holRemainderConstants α γ).μ32 = holExpandedRemainder32 α γ := by
  dsimp [holRemainderConstants, holExpandedRemainder32]
  field_simp
  ring

theorem holRemainder33_expanded (α γ : ℝ) (hα : α ≠ 0) :
    (holRemainderConstants α γ).μ33 = holExpandedRemainder33 α γ := by
  dsimp [holRemainderConstants, holExpandedRemainder33]
  field_simp
  ring

/-- Closed deterministic HOL growth coefficient `A_H`. -/
def holExpandedGrowthConstant (α γ LF LG fzero gzero : ℝ) : ℝ :=
  ((1 + γ) / 2) * (gzero + 2 * LG + LG * (fzero + 2 * LF)) +
    (γ ^ 2 / (2 * α) + γ ^ 2 / 2 +
      2 * γ ^ 3 / α + γ ^ 3 / 2 + γ * α / 2) +
    (γ / 2 + γ * α / 2 + 3 * γ ^ 2 / 2 + α ^ 2 / 2 + α * γ ^ 2 / 2) +
    LG * (fzero + 2 * LF)

/-- Closed scalar HOL Gaussian-kernel coefficient `N_H`. -/
def holExpandedNoiseConstant (α γ : ℝ) : ℝ :=
  Real.sqrt (2 * α) *
    (3 * γ / 2 + α + 3 * γ ^ 2 / 2 + α ^ 2 / 2 + α * γ ^ 2 / 2)

theorem holLocalGrowthConstant_expanded (α γ LF LG fzero gzero : ℝ)
    (hα : α ≠ 0) :
    holLocalGrowthConstant α γ LF LG fzero gzero =
      holExpandedGrowthConstant α γ LF LG fzero gzero := by
  unfold holLocalGrowthConstant holLocalConsistencyConstant
  rw [holRemainder32_expanded α γ hα, holRemainder33_expanded α γ hα]
  dsimp [holRemainderConstants, holExpandedRemainder32,
    holExpandedRemainder33, holExpandedGrowthConstant]
  ring

theorem holScalarNoiseConstant_expanded (α γ : ℝ) (hα : α ≠ 0) :
    holScalarNoiseConstant α γ = holExpandedNoiseConstant α γ := by
  unfold holScalarNoiseConstant
  rw [holRemainder33_expanded α γ hα]
  dsimp [holExpandedRemainder33, holExpandedNoiseConstant]
  ring

/-- Closed HOL drift Lipschitz radius for nonnegative primitive constants. -/
def holExpandedDriftLip (α γ LF LG : ℝ) : ℝ :=
  4 * (LF + LG + 1 + 2 * γ + α)

theorem holDriftGlobalLip_expanded (α γ LF LG : ℝ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) :
    (holDriftGlobalLip LF LG α γ : ℝ) = holExpandedDriftLip α γ LF LG := by
  unfold holDriftGlobalLip holExpandedDriftLip
  rw [abs_of_nonneg hγ, abs_of_nonneg hα, Real.coe_toNNReal _ (by positivity)]

/-- Closed HOL constant part: `d` is the physical Brownian dimension. -/
def holExpandedConstant0 (d α γ LF LG fzero gzero bzero : ℝ) : ℝ :=
  let K := 4 * (LF + LG + 1 + 2 * γ + α)
  let β := Real.sqrt α * Real.sqrt (2 * d)
  holExpandedGrowthConstant α γ LF LG fzero gzero +
    Real.sqrt d * holExpandedNoiseConstant α γ +
    (8 / 3 : ℝ) * K * (bzero + K * Real.exp (K + 1) * (bzero + β) + β)

/-- Closed HOL initial-radius part. -/
def holExpandedConstant1 (α γ LF LG fzero gzero : ℝ) : ℝ :=
  let K := 4 * (LF + LG + 1 + 2 * γ + α)
  holExpandedGrowthConstant α γ LF LG fzero gzero +
    (8 / 3 : ℝ) * K ^ 2 * Real.exp (K + 1)

theorem holUniformLocalConstant0_expanded (I : Type*) [Fintype I]
    (α γ LF LG fzero gzero bzero : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) :
    holUniformLocalConstant0 I α γ LF LG fzero gzero bzero =
      holExpandedConstant0 (Fintype.card I) α γ LF LG fzero gzero bzero := by
  unfold holUniformLocalConstant0
  rw [holDriftGlobalLip_expanded α γ LF LG hα.le hγ hLF hLG,
    holLocalGrowthConstant_expanded α γ LF LG fzero gzero (ne_of_gt hα),
    holScalarNoiseConstant_expanded α γ (ne_of_gt hα)]
  rfl

theorem holUniformLocalConstant1_expanded (α γ LF LG fzero gzero : ℝ)
    (hα : 0 < α) (hγ : 0 ≤ γ) (hLF : 0 ≤ LF) (hLG : 0 ≤ LG) :
    holUniformLocalConstant1 α γ LF LG fzero gzero =
      holExpandedConstant1 α γ LF LG fzero gzero := by
  unfold holUniformLocalConstant1
  rw [holDriftGlobalLip_expanded α γ LF LG hα.le hγ hLF hLG,
    holLocalGrowthConstant_expanded α γ LF LG fzero gzero (ne_of_gt hα)]
  rfl

end PBGSO.Methods
