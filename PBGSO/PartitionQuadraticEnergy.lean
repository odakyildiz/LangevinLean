import PBGSO.QuadraticMartingale

/-! # Exact finite-partition energy from actual martingales
Only point-time L² random variables are used. No time-integrability of a drift,
quadratic forward equation, or supplied stochastic orthogonality is required.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.PartitionQuadraticEnergy
open QuadraticMartingale
variable {Ω Z : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [MeasurableSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ℝ mΩ)
  (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)

include hW

/-- A past-measurable L² variable is orthogonal to actual martingale increments.
The zero pairing is derived by the genuine conditional L² projection. -/
theorem increment_orthogonal (N : ℝ → Lp Z 2 Q) (m : ℝ → Ω → Z)
    (hm : Martingale m F Q) (hrep : ∀ t, m t =ᵐ[Q] N t)
    (s t : ℝ) (hst : s ≤ t) (Y : Lp Z 2 Q) (hY : AEStronglyMeasurable[F s] Y Q) :
    weightedPairing Q W Y (N t - N s) = 0 := by
  have ha : AEStronglyMeasurable[F s] (W.compLpL 2 Q Y) Q :=
    (W.continuous.comp_aestronglyMeasurable hY).congr (W.coeFn_compLpL Y).symm
  have hcond : (condExpL2 Z ℝ (F.le s) (N t - N s) : Lp Z 2 Q) = 0 := by
    simp only [map_sub, Submodule.coe_sub]
    rw [martingale_condExpL2 Q F N m hm hrep s t hst,
      martingale_condExpL2 Q F N m hm hrep s s le_rfl, sub_self]
  have hi := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (F.le s) (N t - N s) (W.compLpL 2 Q Y) ha
  rw [hcond, inner_zero_left] at hi
  rw [weightedPairing_left Q W hW, real_inner_comm, ← hi]

/-- Actual martingale orthogonality yields exact quadratic increment additivity,
without an assumed stochastic isometry or quadratic-variation formula. -/
theorem martingale_increment_energy (N : ℝ → Lp Z 2 Q) (m : ℝ → Ω → Z)
    (hm : Martingale m F Q) (hrep : ∀ t, m t =ᵐ[Q] N t)
    (s t : ℝ) (hst : s ≤ t) :
    weightedPairing Q W (N t - N s) (N t - N s) =
      weightedPairing Q W (N t) (N t) - weightedPairing Q W (N s) (N s) := by
  have ha : AEStronglyMeasurable[F s] (N s) Q :=
    (hm.stronglyAdapted s).aestronglyMeasurable.congr (hrep s)
  have ho := increment_orthogonal Q F W hW N m hm hrep s t hst (N s) ha
  have he := bilinear_increment (weightedPairing Q W) (weightedPairing_symmetric Q W hW) (N s) (N t)
  rw [ho, mul_zero, zero_add] at he
  exact he.symm

/-- One exact energy increment, derived from actual decomposition and past
adaptation. The finite-variation component need not be time-L¹ in L². -/
theorem energy_increment (X V N : ℝ → Lp Z 2 Q) (m : ℝ → Ω → Z)
    (hm : Martingale m F Q) (hrep : ∀ t, m t =ᵐ[Q] N t)
    (s t : ℝ) (hst : s ≤ t) (hs : X s = X 0 + V s + N s)
    (ht : X t = X 0 + V t + N t) (hX : AEStronglyMeasurable[F s] (X s) Q) :
    weightedPairing Q W (X t) (X t) - weightedPairing Q W (X s) (X s) =
      2 * weightedPairing Q W (X s) (V t - V s) +
      weightedPairing Q W (V t - V s) (V t - V s) +
      2 * weightedPairing Q W (V t - V s) (N t - N s) +
      (weightedPairing Q W (N t) (N t) - weightedPairing Q W (N s) (N s)) := by
  have ho := increment_orthogonal Q F W hW N m hm hrep s t hst (X s) hX
  have hv := martingale_increment_energy Q F W hW N m hm hrep s t hst
  have he := quadratic_increment_forward (weightedPairing Q W) (weightedPairing_symmetric Q W hW)
    X (fun r => X 0 + V r) N (fun r => weightedPairing Q W (N r) (N r)) s t hs ht ho hv
  have hd : (X 0 + V t) - (X 0 + V s) = V t - V s := by abel
  simpa only [hd] using he

/-- Exact expected quadratic energy on any finite monotone time partition.
Only point-time L² state, finite-variation and martingale values are required.
N₀=0 and the decomposition also imply V₀=0, so no redundant initial premise
for V is necessary. Both stochastic orthogonalities are proved above. -/
theorem finite_partition_identity (X V N : ℝ → Lp Z 2 Q) (m : ℝ → Ω → Z)
    (hm : Martingale m F Q) (hrep : ∀ t, m t =ᵐ[Q] N t)
    (T : ℝ) (τ : ℕ → ℝ) (hτ : Monotone τ) (n : ℕ) (hz : τ 0 = 0) (hend : τ n = T)
    (hN0 : N 0 = 0)
    (hdecomp : ∀ t ∈ Icc 0 T, X t = X 0 + V t + N t)
    (hX : ∀ t ∈ Icc 0 T, AEStronglyMeasurable[F t] (X t) Q) :
    weightedPairing Q W (X T) (X T) = weightedPairing Q W (X 0) (X 0) +
      2 * ∑ k ∈ Finset.range n, weightedPairing Q W (X (τ k)) (V (τ (k + 1)) - V (τ k)) +
      (∑ k ∈ Finset.range n, weightedPairing Q W (V (τ (k + 1)) - V (τ k)) (V (τ (k + 1)) - V (τ k))) +
      2 * ∑ k ∈ Finset.range n, weightedPairing Q W (V (τ (k + 1)) - V (τ k)) (N (τ (k + 1)) - N (τ k)) +
      weightedPairing Q W (N T) (N T) := by
  have hmem (k : ℕ) (hk : k ≤ n) : τ k ∈ Icc 0 T := by
    constructor
    · rw [← hz]
      exact hτ (Nat.zero_le k)
    · rw [← hend]
      exact hτ hk
  have hp : ∀ j, j ≤ n →
      weightedPairing Q W (X (τ j)) (X (τ j)) = weightedPairing Q W (X 0) (X 0) +
        2 * ∑ k ∈ Finset.range j, weightedPairing Q W (X (τ k)) (V (τ (k + 1)) - V (τ k)) +
        (∑ k ∈ Finset.range j, weightedPairing Q W (V (τ (k + 1)) - V (τ k)) (V (τ (k + 1)) - V (τ k))) +
        2 * ∑ k ∈ Finset.range j, weightedPairing Q W (V (τ (k + 1)) - V (τ k)) (N (τ (k + 1)) - N (τ k)) +
        weightedPairing Q W (N (τ j)) (N (τ j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp only [hz, hN0, Finset.range_zero, Finset.sum_empty, mul_zero, map_zero, add_zero]
    | succ j ih =>
      intro hj
      have hi := ih (Nat.le_of_succ_le hj)
      have he := energy_increment Q F W hW X V N m hm hrep (τ j) (τ (j + 1))
        (hτ (Nat.le_succ j)) (hdecomp _ (hmem j (Nat.le_of_succ_le hj)))
        (hdecomp _ (hmem (j + 1) hj)) (hX _ (hmem j (Nat.le_of_succ_le hj)))
      simp only [Finset.sum_range_succ]
      linarith
  simpa only [hend] using hp n le_rfl

end PBGSO.PartitionQuadraticEnergy
