import LatentDiffusion.Numerics
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Explicit averaging variance for heterogeneous particles and mini-batches

Orthogonality is a primitive centered cross-moment assumption in `L²`; it does
not require identically distributed copies. Thus particles belonging to
different data may have different laws. The mini-batch results below use
primitive first and pair inclusion probabilities, not an assumed oracle-error
bound.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal

namespace LatentDiffusion.MiniBatchVariance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Actual normalized sum, also used for `L²` random variables. -/
def average {K : ℕ} (g : Fin K → H) : H :=
  (1 / (K : ℝ)) • ∑ i, g i

/-- Pythagoras for a heterogeneous family with zero cross inner products. -/
theorem norm_sum_sq_of_orthogonal {K : ℕ} (g : Fin K → H)
    (hc : ∀ i j, i ≠ j → inner ℝ (g i) (g j) = 0) :
    ‖∑ i, g i‖ ^ 2 = ∑ i, ‖g i‖ ^ 2 := by
  have hi (i j : Fin K) : inner ℝ (g i) (g j) =
      if i = j then ‖g i‖ ^ 2 else 0 := by
    split_ifs with hij
    · subst j; exact real_inner_self_eq_norm_sq _
    · exact hc i j hij
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, hi]
  simp

/-- Exact second moment of a centered orthogonal particle average. -/
theorem mean_sq_sum_of_orthogonal {K : ℕ} (g : Fin K → H)
    (hc : ∀ i j, i ≠ j → inner ℝ (g i) (g j) = 0) :
    ‖average g‖ ^ 2 = (1 / (K : ℝ)) ^ 2 * ∑ i, ‖g i‖ ^ 2 := by
  rw [average, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_sum_sq_of_orthogonal g hc]

/-- A per-copy variance bound gives `V/K` without identical-distribution assumptions. -/
theorem mean_sq_sum_of_orthogonal_le {K : ℕ} (hK : 0 < K)
    (g : Fin K → H) (V : ℝ)
    (hc : ∀ i j, i ≠ j → inner ℝ (g i) (g j) = 0)
    (hV : ∀ i, ‖g i‖ ^ 2 ≤ V) : ‖average g‖ ^ 2 ≤ V / K := by
  have hsum : (∑ i, ‖g i‖ ^ 2) ≤ (K : ℝ) * V := by
    calc
      (∑ i, ‖g i‖ ^ 2) ≤ ∑ _ : Fin K, V := Finset.sum_le_sum (fun i _ ↦ hV i)
      _ = (K : ℝ) * V := by simp
  rw [mean_sq_sum_of_orthogonal g hc]
  calc
    (1 / (K : ℝ)) ^ 2 * ∑ i, ‖g i‖ ^ 2 ≤
        (1 / (K : ℝ)) ^ 2 * ((K : ℝ) * V) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = V / K := by field_simp

/-- Root mean-square version used for the empirical parameter-force residual. -/
theorem mean_sum_of_orthogonal_le {K : ℕ} (hK : 0 < K)
    (g : Fin K → H) (V : ℝ)
    (hc : ∀ i j, i ≠ j → inner ℝ (g i) (g j) = 0)
    (hV : ∀ i, ‖g i‖ ^ 2 ≤ V) : ‖average g‖ ≤ Real.sqrt (V / K) := by
  rw [← Real.sqrt_sq (norm_nonneg (average g))]
  exact Real.sqrt_le_sqrt (mean_sq_sum_of_orthogonal_le hK g V hc hV)

/-- Expanding the squared norm, retaining every heterogeneous cross term. -/
theorem norm_sum_smul_sq {M : ℕ} (c : Fin M → ℝ) (g : Fin M → H) :
    ‖∑ i, c i • g i‖ ^ 2 =
      ∑ i, ∑ j, (c i * c j) * inner ℝ (g i) (g j) := by
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [mul_assoc]

/-- Centering each heterogeneous vector by the full population average gives
exactly zero total; no assumption on the individual means is needed. -/
theorem centered_sum_eq_zero {M : ℕ} (hM : 0 < M) (g : Fin M → H) :
    (∑ i, (g i - average g)) = 0 := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ]
  unfold average
  rw [smul_smul, mul_one_div_cancel hm, one_smul, sub_self]

private theorem sum_cross_inner {M : ℕ} (g : Fin M → H) :
    (∑ i, ∑ j, inner ℝ (g i) (g j)) = ‖∑ i, g i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum]

/-- Exchangeable inclusion moments separate a diagonal variance and a mean term. -/
theorem equicorrelated_sum {M : ℕ} (p r : ℝ) (g : Fin M → H) :
    (∑ i, ∑ j, (if i = j then p else r) * inner ℝ (g i) (g j)) =
      (p - r) * (∑ i, ‖g i‖ ^ 2) + r * ‖∑ i, g i‖ ^ 2 := by
  classical
  have hs (i j : Fin M) :
      (if i = j then p else r) * inner ℝ (g i) (g j) =
        r * inner ℝ (g i) (g j) +
          (if i = j then (p - r) * inner ℝ (g i) (g j) else 0) := by
    split_ifs <;> ring
  simp_rw [hs, Finset.sum_add_distrib]
  have hd (i : Fin M) :
      (∑ j, if i = j then (p - r) * inner ℝ (g i) (g j) else 0) =
        (p - r) * ‖g i‖ ^ 2 := by simp [real_inner_self_eq_norm_sq]
  simp_rw [hd, ← Finset.mul_sum]
  rw [sum_cross_inner]
  ring

section FiniteBatch

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The indicator of selecting datum `i` in the actual sampled batch. -/
def inclusion {M : ℕ} (batch : Ω → Finset (Fin M)) (ω : Ω) (i : Fin M) : ℝ :=
  if i ∈ batch ω then 1 else 0

/-- Primitive uniform fixed-size sampling laws. These are first and pair
inclusion probabilities of an actual finite probability distribution, not a
variance bound or a recurrence assumption. -/
structure BatchInclusionLaw {M : ℕ} (B : ℕ) (batch : Ω → Finset (Fin M)) : Prop where
  size : ∀ ω, (batch ω).card = B
  first : ∀ i, (∫ ω, inclusion batch ω i ∂P) = (B : ℝ) / M
  pair : ∀ i j, i ≠ j →
    (∫ ω, inclusion batch ω i * inclusion batch ω j ∂P) =
      (B : ℝ) * ((B : ℝ) - 1) / ((M : ℝ) * ((M : ℝ) - 1))

/-- The actual mini-batch average of the supplied centered per-datum vectors. -/
def batchAverage {M : ℕ} (B : ℕ) (batch : Ω → Finset (Fin M))
    (g : Fin M → H) (ω : Ω) : H :=
  (1 / (B : ℝ)) • ∑ i, inclusion batch ω i • g i

/-- The sum of selection indicators is the actual batch cardinality. -/
theorem sum_inclusion {M : ℕ} (batch : Ω → Finset (Fin M)) (ω : Ω) :
    (∑ i, inclusion batch ω i) = ((batch ω).card : ℝ) := by
  classical
  simp [inclusion, ← Finset.sum_filter]

/-- Fixed batch cardinality makes centering commute with the sampled average. -/
theorem batchAverage_centered {M B : ℕ} (hB : 0 < B)
    (batch : Ω → Finset (Fin M)) (hbatch : BatchInclusionLaw P B batch)
    (g : Fin M → H) (ω : Ω) :
    batchAverage B batch (fun i ↦ g i - average g) ω =
      batchAverage B batch g ω - average g := by
  have hb : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  unfold batchAverage
  simp_rw [smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, sum_inclusion batch ω, hbatch.size ω,
    smul_sub, smul_smul, one_div_mul_cancel hb, one_smul]

/-- The two primitive inclusion laws determine every indicator-product moment. -/
theorem inclusion_product_moment {M B : ℕ} (batch : Ω → Finset (Fin M))
    (hbatch : BatchInclusionLaw P B batch) (i j : Fin M) :
    (∫ ω, inclusion batch ω i * inclusion batch ω j ∂P) =
      if i = j then (B : ℝ) / M else
        (B : ℝ) * ((B : ℝ) - 1) / ((M : ℝ) * ((M : ℝ) - 1)) := by
  classical
  split_ifs with hij
  · subst j
    have hid (ω : Ω) : inclusion batch ω i * inclusion batch ω i =
        inclusion batch ω i := by
      unfold inclusion
      split_ifs <;> norm_num
    simp_rw [hid]
    exact hbatch.first i
  · exact hbatch.pair i j hij

/-- Exact expectation of the unnormalized sampled sum; finite probability makes
all polynomial integrals genuine finite integrals. -/
theorem batch_sum_second_moment {M B : ℕ} (batch : Ω → Finset (Fin M))
    (hbatch : BatchInclusionLaw P B batch) (g : Fin M → H) :
    (∫ ω, ‖∑ i, inclusion batch ω i • g i‖ ^ 2 ∂P) =
      ((B : ℝ) / M -
        (B : ℝ) * ((B : ℝ) - 1) / ((M : ℝ) * ((M : ℝ) - 1))) *
          (∑ i, ‖g i‖ ^ 2) +
      ((B : ℝ) * ((B : ℝ) - 1) / ((M : ℝ) * ((M : ℝ) - 1))) *
        ‖∑ i, g i‖ ^ 2 := by
  simp_rw [norm_sum_smul_sq]
  rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  simp_rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  simp_rw [integral_mul_const, inclusion_product_moment P batch hbatch]
  exact equicorrelated_sum _ _ g

/-- Exact finite-population correction for mini-batching without replacement.
The vectors may be heterogeneous; only their total centered sum is zero. -/
theorem without_replacement_variance {M B : ℕ} (hM : 1 < M) (hB : 0 < B)
    (batch : Ω → Finset (Fin M)) (hbatch : BatchInclusionLaw P B batch)
    (g : Fin M → H) (hzero : ∑ i, g i = 0) :
    (∫ ω, ‖batchAverage B batch g ω‖ ^ 2 ∂P) =
      ((M : ℝ) - B) / ((B : ℝ) * ((M : ℝ) - 1)) *
        ((1 / (M : ℝ)) * ∑ i, ‖g i‖ ^ 2) := by
  have hMc : (M : ℝ) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  have hBc : (B : ℝ) ≠ 0 := by exact_mod_cast (by omega : B ≠ 0)
  have hM1 : (M : ℝ) - 1 ≠ 0 := by
    have hMc' : (1 : ℝ) < M := by exact_mod_cast hM
    linarith
  unfold batchAverage
  simp_rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, batch_sum_second_moment P batch hbatch g, hzero]
  simp only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero]
  field_simp [hMc, hBc, hM1]
  ring

/-- The familiar exact variance formula, directly for the raw gradient oracle
minus the full-data gradient, with finite-population correction. -/
theorem minibatch_gradient_variance {M B : ℕ} (hM : 1 < M) (hB : 0 < B)
    (batch : Ω → Finset (Fin M)) (hbatch : BatchInclusionLaw P B batch)
    (g : Fin M → H) :
    (∫ ω, ‖batchAverage B batch g ω - average g‖ ^ 2 ∂P) =
      ((M : ℝ) - B) / ((B : ℝ) * ((M : ℝ) - 1)) *
        ((1 / (M : ℝ)) * ∑ i, ‖g i - average g‖ ^ 2) := by
  simpa only [batchAverage_centered P hB batch hbatch g] using
    without_replacement_variance P hM hB batch hbatch (fun i ↦ g i - average g)
      (centered_sum_eq_zero (by omega) g)

/-- Explicit squared oracle-noise scale, computed from batch and data sizes. -/
def oracleVariance (M B : ℕ) (V : ℝ) : ℝ :=
  ((M : ℝ) - B) / ((B : ℝ) * ((M : ℝ) - 1)) * V

/-- A population gradient-dispersion bound gives the derived mini-batch oracle
variance used by the stochastic Euler theorem. -/
theorem minibatch_oracle_variance_bound {M B : ℕ}
    (hM : 1 < M) (hB : 0 < B) (hBM : B ≤ M)
    (batch : Ω → Finset (Fin M)) (hbatch : BatchInclusionLaw P B batch)
    (g : Fin M → H) (V : ℝ)
    (hV : ((1 / (M : ℝ)) * ∑ i, ‖g i - average g‖ ^ 2) ≤ V) :
    (∫ ω, ‖batchAverage B batch g ω - average g‖ ^ 2 ∂P) ≤
      oracleVariance M B V := by
  rw [minibatch_gradient_variance P hM hB batch hbatch g]
  unfold oracleVariance
  apply mul_le_mul_of_nonneg_left hV
  have hMc : (1 : ℝ) < M := by exact_mod_cast hM
  have hBc : (0 : ℝ) < B := by exact_mod_cast hB
  have hBMc : (B : ℝ) ≤ M := by exact_mod_cast hBM
  exact div_nonneg (sub_nonneg.mpr hBMc)
    (mul_nonneg hBc.le (by linarith))

end FiniteBatch

end LatentDiffusion.MiniBatchVariance
