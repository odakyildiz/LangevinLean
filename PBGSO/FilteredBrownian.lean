import PBGSO.PredictableIsometry
import Mathlib.Probability.BrownianMotion.Basic
import PBGSO.BrownianGridIsometry

/-! # Finite predictable integration for a filtered Brownian vector

Primitive inputs are Brownian coordinate laws, coordinate independence,
adapted evaluations, and independence of every future increment vector
from the filtration. The filtration can include independent initialization.
Quadratic moments and the martingale property are derived.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.FilteredBrownian
open PBGSO.PredictableIsometry
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The primitive filtered Brownian-driver properties. No stochastic
integral, moment-isometry or forward equation is included. -/
structure Driver where
  process : I → ℝ≥0 → Ω → ℝ
  brownian : ∀ i, IsPreBrownianReal (process i) Q
  filtration : Filtration ℝ≥0 mΩ
  adapted : ∀ i, StronglyAdapted filtration (process i)
  increment_coordinates : ∀ s t : ℝ≥0, s ≤ t →
    iIndepFun (fun i ω => process i t ω - process i s ω) Q
  future_independent : ∀ s t : ℝ≥0, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω i => process i t ω - process i s ω) inferInstance)
      (filtration s) Q

variable (D : Driver (I := I) Q)

def increment (s t : ℝ≥0) (i : I) (ω : Ω) : ℝ := D.process i t ω - D.process i s ω

theorem increment_law (s t : ℝ≥0) (hst : s ≤ t) (i : I) :
    HasLaw (increment Q D s t i) (gaussianReal 0 (t - s)) Q := by
  change HasLaw (fun ω => D.process i t ω - D.process i s ω) _ Q
  simpa only [add_tsub_cancel_of_le hst] using ((D.brownian i).shift s).hasLaw_eval (t - s)

theorem increment_memLp (s t : ℝ≥0) (hst : s ≤ t) (i : I) :
    MemLp (increment Q D s t i) 2 Q :=
  (increment_law Q D s t hst i).memLp (memLp_id_gaussianReal (2 : ℝ≥0))

theorem increment_mean (s t : ℝ≥0) (hst : s ≤ t) (i : I) :
    (∫ ω, increment Q D s t i ω ∂Q) = 0 :=
  ((increment_law Q D s t hst i).integral_comp (f := id) (by fun_prop)).trans integral_id_gaussianReal

theorem increment_measurable (s t : ℝ≥0) (i : I) : Measurable (increment Q D s t i) :=
  (((D.adapted i t).mono (D.filtration.le t)).measurable).sub
    (((D.adapted i s).mono (D.filtration.le s)).measurable)

/-- Primitive random coefficient columns measurable at one actual time. -/
structure Coefficient (t : ℝ≥0) where
  value : I → Ω → Z
  adapted : ∀ i, StronglyMeasurable[D.filtration t] (value i)
  square : ∀ i, MemLp (value i) 2 Q

abbrev Coefficients (τ : ℕ → ℝ≥0) := ∀ k, Coefficient (Z := Z) Q D (τ k)

theorem increment_independent (s t : ℝ≥0) (hst : s ≤ t) (A : Coefficient (Z := Z) Q D s) :
    IndepFun (fun ω i => increment Q D s t i ω) (fun ω i => A.value i ω) Q := by
  apply indep_of_indep_of_le_right (D.future_independent s t hst)
  have hm : @Measurable Ω (I → Z) (D.filtration s) inferInstance
      (fun ω i => A.value i ω) :=
    (@measurable_pi_iff Ω I (fun _ => Z) (D.filtration s) (fun _ => inferInstance)
      (fun ω i => A.value i ω)).mpr (fun i => (A.adapted i).measurable)
  exact hm.comap_le

theorem increment_cross_moment (s t : ℝ≥0) (hst : s ≤ t) (i j : I) :
    (∫ ω, increment Q D s t i ω * increment Q D s t j ω ∂Q) =
      if i = j then (t : ℝ) - s else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have he := ((increment_law Q D s t hst i).integral_comp
      (f := fun x : ℝ => x ^ 2) (by fun_prop)).trans
      (ULA.centered_gaussian_second_moment (t - s))
    simpa only [Function.comp_apply, pow_two, NNReal.coe_sub hst] using he
  · rw [ite_eq_right hij]
    have he := ((D.increment_coordinates s t hst).indepFun hij).integral_mul_eq_mul_integral
      (increment_memLp Q D s t hst i).aestronglyMeasurable
      (increment_memLp Q D s t hst j).aestronglyMeasurable
    have hi := increment_mean Q D s t hst i
    have hj := increment_mean Q D s t hst j
    change (∫ ω, increment Q D s t i ω * increment Q D s t j ω ∂Q) =
      (∫ ω, increment Q D s t i ω ∂Q) * (∫ ω, increment Q D s t j ω ∂Q) at he
    rw [hi, hj, zero_mul] at he
    exact he

def noiseStep (s t : ℝ≥0) (A : Coefficient (Z := Z) Q D s) (ω : Ω) : Z :=
  stepSum (increment Q D s t) A.value ω

theorem noiseStep_memLp (s t : ℝ≥0) (hst : s ≤ t) (A : Coefficient (Z := Z) Q D s) :
    MemLp (noiseStep Q D s t A) 2 Q :=
  stepSum_memLp Q _ _ (increment_memLp Q D s t hst) A.square (increment_independent Q D s t hst A)

theorem noiseStep_isometry (W : Z →L[ℝ] Z) (s t : ℝ≥0) (hst : s ≤ t)
    (A : Coefficient (Z := Z) Q D s) :
    (∫ ω, ⟪noiseStep Q D s t A ω, W (noiseStep Q D s t A ω)⟫_ℝ ∂Q) =
      ((t : ℝ) - s) * ∑ i, ∫ ω, ⟪A.value i ω, W (A.value i ω)⟫_ℝ ∂Q := by
  have hξ := increment_memLp Q D s t hst
  have hind := increment_independent Q D s t hst A
  have hm (i : I) : MemLp (fun ω => increment Q D s t i ω • A.value i ω) 2 Q :=
    independent_smul_memLp Q _ _ (hξ i) (A.square i)
      (hind.comp (measurable_pi_apply i) (measurable_pi_apply i))
  have hi (i j : I) : Integrable
      (fun ω => ⟪increment Q D s t i ω • A.value i ω,
        W (increment Q D s t j ω • A.value j ω)⟫_ℝ) Q :=
    pairing_integrable Q W _ _ (hm i) (hm j)
  have he : (fun ω => ⟪noiseStep Q D s t A ω, W (noiseStep Q D s t A ω)⟫_ℝ) =
      (fun ω => ∑ i, ∑ j, ⟪increment Q D s t i ω • A.value i ω,
        W (increment Q D s t j ω • A.value j ω)⟫_ℝ) := by
    funext ω
    simp only [noiseStep, stepSum, map_sum, sum_inner, inner_sum]
    exact Finset.sum_comm
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  simp_rw [weighted_cross_moment Q W _ _ hξ A.square hind,
    increment_cross_moment Q D s t hst]
  simp only [ite_mul, zero_mul]
  simp [Finset.mul_sum]

theorem noiseStep_condExp_zero (s t : ℝ≥0) (hst : s ≤ t) (A : Coefficient (Z := Z) Q D s) :
    Q[noiseStep Q D s t A | D.filtration s] =ᵐ[Q] (0 : Ω → Z) :=
  independent_step_condExp_zero Q (D.filtration s) (D.filtration.le s)
    (increment Q D s t) A.value (increment_measurable Q D s t)
    (increment_memLp Q D s t hst) A.square A.adapted
    (increment_independent Q D s t hst A) (D.future_independent s t hst)
    (increment_mean Q D s t hst)

def gridSum (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (ω : Ω) : Z :=
  ∑ k : Fin n, noiseStep Q D (τ k) (τ (k + 1)) (A k) ω

theorem gridSum_zero (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) (ω : Ω) :
    gridSum Q D τ A 0 ω = 0 := by simp [gridSum]

theorem gridSum_succ (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (ω : Ω) :
    gridSum Q D τ A (n + 1) ω = gridSum Q D τ A n ω +
      noiseStep Q D (τ n) (τ (n + 1)) (A n) ω := by
  simp only [gridSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem gridSum_memLp (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) : MemLp (gridSum Q D τ A n) 2 Q := by
  apply memLp_finsetSum Finset.univ
  intro k _
  exact noiseStep_memLp Q D _ _ (hτ (Nat.le_succ k)) (A k)

theorem gridSum_adapted (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    StronglyMeasurable[D.filtration (τ n)] (gridSum Q D τ A n) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro k _
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have h1 := (D.adapted i (τ (k + 1))).mono
    (D.filtration.mono (hτ (Nat.succ_le_of_lt k.isLt)))
  have h0 := (D.adapted i (τ k)).mono
    (D.filtration.mono (hτ (Nat.le_of_lt k.isLt)))
  exact (h1.sub h0).smul ((A k).adapted i |>.mono
    (D.filtration.mono (hτ (Nat.le_of_lt k.isLt))))

def gridFiltration (τ : ℕ → ℝ≥0) (hτ : Monotone τ) : Filtration ℕ mΩ where
  seq n := D.filtration (τ n)
  mono' _ _ h := D.filtration.mono (hτ h)
  le' n := D.filtration.le (τ n)

theorem gridSum_martingale (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) :
    Martingale (gridSum Q D τ A) (gridFiltration Q D τ hτ) Q := by
  apply martingale_of_condExp_sub_eq_zero_nat
    (show StronglyAdapted (gridFiltration Q D τ hτ) (gridSum Q D τ A) from
      gridSum_adapted Q D τ hτ A)
    (fun n => (gridSum_memLp Q D τ hτ A n).integrable (by norm_num))
  intro n
  have he : gridSum Q D τ A (n + 1) - gridSum Q D τ A n =
      noiseStep Q D (τ n) (τ (n + 1)) (A n) := by
    funext ω
    simp only [Pi.sub_apply, gridSum_succ, add_sub_cancel_left]
  rw [he]
  exact noiseStep_condExp_zero Q D _ _ (hτ (Nat.le_succ n)) (A n)



/-- Finite predictable Brownian integration has its exact weighted
quadratic moment for every selfadjoint bounded operator. -/
theorem gridSum_isometry (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) :
    (∫ ω, ⟪gridSum Q D τ A n ω, W (gridSum Q D τ A n ω)⟫_ℝ ∂Q) =
      ∑ k : Fin n, ((τ (k + 1) : ℝ) - τ k) *
        ∑ i, ∫ ω, ⟪(A k).value i ω, W ((A k).value i ω)⟫_ℝ ∂Q := by
  induction n with
  | zero => simp only [gridSum_zero, inner_zero_left, integral_zero,
      Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
    let Y := noiseStep Q D (τ n) (τ (n + 1)) (A n)
    have hX2 := gridSum_memLp Q D τ hτ A n
    have hY2 := noiseStep_memLp Q D _ _ (hτ (Nat.le_succ n)) (A n)
    have hcross := conditional_zero_pairing Q W (D.filtration (τ n))
      (D.filtration.le (τ n)) (gridSum Q D τ A n) Y hX2 hY2
      (gridSum_adapted Q D τ hτ A n).aestronglyMeasurable
      (noiseStep_condExp_zero Q D _ _ (hτ (Nat.le_succ n)) (A n))
    have hpoint : (fun ω => ⟪gridSum Q D τ A (n + 1) ω, W (gridSum Q D τ A (n + 1) ω)⟫_ℝ) =
        (fun ω => ⟪gridSum Q D τ A n ω, W (gridSum Q D τ A n ω)⟫_ℝ +
          2 * ⟪gridSum Q D τ A n ω, W (Y ω)⟫_ℝ + ⟪Y ω, W (Y ω)⟫_ℝ) := by
      funext ω
      rw [gridSum_succ]
      change ⟪gridSum Q D τ A n ω + Y ω, W (gridSum Q D τ A n ω + Y ω)⟫_ℝ = _
      simp only [map_add, inner_add_left, inner_add_right]
      have hs : ⟪Y ω, W (gridSum Q D τ A n ω)⟫_ℝ =
          ⟪gridSum Q D τ A n ω, W (Y ω)⟫_ℝ :=
        (real_inner_comm _ _).trans (hW _ _).symm
      rw [hs]
      ring
    have h00 := pairing_integrable Q W _ _ hX2 hX2
    have h01 := (pairing_integrable Q W _ _ hX2 hY2).const_mul 2
    have h11 := pairing_integrable Q W _ _ hY2 hY2
    have hint1 := integral_add (h00.add h01) h11
    have hint2 := integral_add h00 h01
    simp only [Pi.add_apply] at hint1 hint2
    rw [hpoint, hint1, hint2, integral_const_mul, hcross, mul_zero, add_zero, ih]
    rw [show (∫ ω, ⟪Y ω, W (Y ω)⟫_ℝ ∂Q) = _ from
      noiseStep_isometry Q D W _ _ (hτ (Nat.le_succ n)) (A n), Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]



/-- The finite vector sum equals the sum of its coordinate integrals. -/
theorem gridSum_columns (τ : ℕ → ℝ≥0) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (ω : Ω) :
    gridSum Q D τ A n ω = ∑ i, BrownianGridIsometry.gridSum (D.process i) τ
      (fun k => (A k).value i) n ω := by
  simp only [gridSum, noiseStep, stepSum, BrownianGridIsometry.gridSum]
  exact Finset.sum_comm

def subtract (τ : ℕ → ℝ≥0) (A C : Coefficients (Z := Z) Q D τ) :
    Coefficients (Z := Z) Q D τ := fun k =>
  ⟨fun i ω => (A k).value i ω - (C k).value i ω,
    fun i => ((A k).adapted i).sub ((C k).adapted i),
    fun i => ((A k).square i).sub ((C k).square i)⟩

theorem gridSum_sub (τ : ℕ → ℝ≥0) (A C : Coefficients (Z := Z) Q D τ) (n : ℕ) (ω : Ω) :
    gridSum Q D τ (subtract Q D τ A C) n ω = gridSum Q D τ A n ω - gridSum Q D τ C n ω := by
  simp only [gridSum, noiseStep, stepSum, subtract, smul_sub, Finset.sum_sub_distrib]

/-- Repeating coefficients on refined intervals preserves adaptedness. -/
def refine (τ υ : ℕ → ℝ≥0) (hυmono : Monotone υ) (d : ℕ) (_hd : 0 < d)
    (hυ : ∀ k, υ (d * k) = τ k) (A : Coefficients (Z := Z) Q D τ) :
    Coefficients (Z := Z) Q D υ := fun j =>
  ⟨(A (j / d)).value,
    fun i => ((A (j / d)).adapted i).mono (D.filtration.mono (by
      rw [← hυ (j / d)]
      exact hυmono (Nat.mul_div_le j d))), (A (j / d)).square⟩

/-- Exact pathwise vector refinement; every grid uses the same actual
coordinate Brownian paths. -/
theorem gridSum_refine (τ υ : ℕ → ℝ≥0) (hυmono : Monotone υ) (d : ℕ) (hd : 0 < d)
    (hυ : ∀ k, υ (d * k) = τ k) (A : Coefficients (Z := Z) Q D τ) (n : ℕ) (ω : Ω) :
    gridSum Q D υ (refine Q D τ υ hυmono d hd hυ A) (d * n) ω = gridSum Q D τ A n ω := by
  rw [gridSum_columns, gridSum_columns]
  apply Finset.sum_congr rfl
  intro i _
  exact BrownianGridIsometry.gridSum_refine_mul (D.process i) τ υ d hd hυ
    (fun k => (A k).value i) n ω

end PBGSO.FilteredBrownian
