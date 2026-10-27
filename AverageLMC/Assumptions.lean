import UnadjustedLangevin.Analysis.Smooth
import UnadjustedLangevin.StrongConvexity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.LinearAlgebra.Matrix.Trace

set_option linter.style.header false

/-!
# The potential and smoothness constants of Average LMC

All constants below are defined from the same real-valued potential on the
Euclidean state space. In particular, coordinate smoothness is the supremum
of the Taylor quotients in equation (coordM), rather than an additional
chosen bound or a hypothesis about a stochastic error.
-/

noncomputable section

open scoped NNReal BigOperators

namespace AverageLMC

/-- The paper's state space `ℝᵖ`, with its Euclidean norm. -/
abbrev State (p : ℕ) := EuclideanSpace ℝ (Fin p)

/-- The canonical coordinate vector `e_j`. -/
def coordinateVector {p : ℕ} (j : Fin p) : State p := EuclideanSpace.single j 1

/-- The coordinate Taylor quotient in (coordM), at a nonzero displacement. -/
def coordinateTaylorQuotient {p : ℕ} (f : State p → ℝ) (j : Fin p)
    (x : State p) (a : ℝ) : ℝ :=
  2 * (f (x + a • coordinateVector j) - f x - a * (gradient f x) j) / a ^ 2

/-- All nonzero-displacement Taylor quotients for one coordinate. -/
def coordinateTaylorQuotients {p : ℕ} (f : State p → ℝ) (j : Fin p) : Set ℝ :=
  {q | ∃ x a, a ≠ 0 ∧ q = coordinateTaylorQuotient f j x a}

/-- Exactly `M_j` in (coordM). Its defining set is bounded above whenever
the potential has a Lipschitz gradient. -/
def coordinateSmoothness {p : ℕ} (f : State p → ℝ) (j : Fin p) : ℝ :=
  sSup (coordinateTaylorQuotients f j)

/-- Exactly `M_av = p⁻¹ ∑ M_j` in (coordM). -/
def averageSmoothness {p : ℕ} (f : State p → ℝ) : ℝ :=
  (∑ j, coordinateSmoothness f j) / (p : ℝ)

/-- The global gradient Lipschitz seminorm from the notation section. -/
def globalSmoothness {p : ℕ} (f : State p → ℝ) : ℝ :=
  sSup {q : ℝ | ∃ x y : State p, x ≠ y ∧
    q = ‖gradient f x - gradient f y‖ / ‖x - y‖}

/-- The actual Hessian matrix of the potential, expressed in the canonical basis. -/
def hessian {p : ℕ} (f : State p → ℝ) (x : State p) :
    Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦ iteratedFDeriv ℝ 2 f x ![coordinateVector i, coordinateVector j]

/-- The actual Laplacian of the potential. -/
def laplacian {p : ℕ} (f : State p → ℝ) : State p → ℝ :=
  Laplacian.laplacian f

/-- The extra third-order condition (lip:2). No Hessian Lipschitz
condition is included: the paper assumes only the squared norm of `∇∆f`. -/
def LaplacianSmooth {p : ℕ} (f : State p → ℝ) (Mdelta : ℝ) : Prop :=
  ContDiff ℝ 3 f ∧ ∀ x, ‖gradient (laplacian f) x‖ ^ 2 ≤ Mdelta ^ 2 * (p : ℝ)

/-- Root mean square component-gradient smoothness in (eq:Mtwo). -/
def rmsComponentSmoothness {p n : ℕ} (f : Fin n → State p → ℝ) : ℝ :=
  Real.sqrt ((∑ i, globalSmoothness (f i) ^ 2) / (n : ℝ))

theorem coordinateTaylorQuotients_nonempty {p : ℕ} (f : State p → ℝ) (j : Fin p) :
    (coordinateTaylorQuotients f j).Nonempty :=
  ⟨coordinateTaylorQuotient f j 0 1, 0, 1, one_ne_zero, rfl⟩

@[simp] theorem norm_coordinateVector {p : ℕ} (j : Fin p) :
    ‖coordinateVector j‖ = 1 := by
  simp [coordinateVector]

@[simp] theorem inner_coordinateVector {p : ℕ} (x : State p) (j : Fin p) :
    inner ℝ x (coordinateVector j) = x j := by
  simp [coordinateVector, EuclideanSpace.inner_single_right]

/-- The literal supremum defining the global seminorm is bounded by every
gradient Lipschitz constant. The positive dimension is the paper's convention. -/
theorem globalSmoothness_le_bound {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f)) :
    globalSmoothness f ≤ (M : ℝ) := by
  let j : Fin p := ⟨0, hp⟩
  have he : (0 : State p) ≠ coordinateVector j := by
    intro h
    have hn := congrArg norm h
    simp at hn
  unfold globalSmoothness
  apply csSup_le
    (show {q : ℝ | ∃ x y : State p, x ≠ y ∧
      q = ‖gradient f x - gradient f y‖ / ‖x - y‖}.Nonempty from
      ⟨_, 0, coordinateVector j, he, rfl⟩)
  rintro q ⟨x, y, hxy, rfl⟩
  exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).mpr (hLip.norm_sub_le x y)

theorem globalSmoothness_nonneg {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f)) :
    0 ≤ globalSmoothness f := by
  let j : Fin p := ⟨0, hp⟩
  have he : (0 : State p) ≠ coordinateVector j := by
    intro h
    have hn := congrArg norm h
    simp at hn
  have hb : BddAbove {q : ℝ | ∃ x y : State p, x ≠ y ∧
      q = ‖gradient f x - gradient f y‖ / ‖x - y‖} := by
    refine ⟨(M : ℝ), ?_⟩
    rintro q ⟨x, y, hxy, rfl⟩
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).mpr
      (hLip.norm_sub_le x y)
  exact (div_nonneg (norm_nonneg _) (norm_nonneg _)).trans
    (le_csSup hb (show ‖gradient f 0 - gradient f (coordinateVector j)‖ /
      ‖(0 : State p) - coordinateVector j‖ ∈ {q : ℝ | ∃ x y : State p, x ≠ y ∧
      q = ‖gradient f x - gradient f y‖ / ‖x - y‖} from
        ⟨0, coordinateVector j, he, rfl⟩))

/-- A Lipschitz gradient is Lipschitz with its exact seminorm. This permits
using the literal `M_∞` of (coordM) throughout the deterministic results. -/
theorem gradient_lipschitz_globalSmoothness {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f)) :
    LipschitzWith ⟨globalSmoothness f, globalSmoothness_nonneg hp f M hLip⟩
      (gradient f) := by
  have hb : BddAbove {q : ℝ | ∃ x y : State p, x ≠ y ∧
      q = ‖gradient f x - gradient f y‖ / ‖x - y‖} := by
    refine ⟨(M : ℝ), ?_⟩
    rintro q ⟨x, y, hxy, rfl⟩
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).mpr
      (hLip.norm_sub_le x y)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  by_cases hxy : x = y
  · simp [hxy]
  · apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).mp
    exact le_csSup hb ⟨x, y, hxy, rfl⟩

theorem coordinateTaylorQuotient_le {p : ℕ} (f : State p → ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f))
    (j : Fin p) (x : State p) (a : ℝ) (ha : a ≠ 0) :
    coordinateTaylorQuotient f j x a ≤ (M : ℝ) := by
  have hu := ULA.Analysis.smooth_upper_bound f M hdiff hLip x
    (x + a • coordinateVector j)
  simp only [add_sub_cancel_left, inner_smul_right, inner_coordinateVector,
    norm_smul, Real.norm_eq_abs, norm_coordinateVector, mul_one] at hu
  rw [sq_abs] at hu
  unfold coordinateTaylorQuotient
  apply (div_le_iff₀ (sq_pos_of_ne_zero ha)).mpr
  nlinarith

theorem coordinateTaylorQuotients_bddAbove {p : ℕ} (f : State p → ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f)) (j : Fin p) :
    BddAbove (coordinateTaylorQuotients f j) := by
  refine ⟨(M : ℝ), ?_⟩
  rintro q ⟨x, a, ha, rfl⟩
  exact coordinateTaylorQuotient_le f M hdiff hLip j x a ha

theorem coordinateSmoothness_le_global_bound {p : ℕ} (f : State p → ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f)) (j : Fin p) :
    coordinateSmoothness f j ≤ (M : ℝ) := by
  apply csSup_le (coordinateTaylorQuotients_nonempty f j)
  rintro q ⟨x, a, ha, rfl⟩
  exact coordinateTaylorQuotient_le f M hdiff hLip j x a ha

/-- The supremum definition supplies the coordinate quadratic upper bound,
including the zero displacement. -/
theorem coordinate_upper_bound {p : ℕ} (f : State p → ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hLip : LipschitzWith M (gradient f))
    (j : Fin p) (x : State p) (a : ℝ) :
    f (x + a • coordinateVector j) ≤ f x + a * (gradient f x) j +
      coordinateSmoothness f j / 2 * a ^ 2 := by
  by_cases ha : a = 0
  · simp [ha]
  · have hs := le_csSup (coordinateTaylorQuotients_bddAbove f M hdiff hLip j)
      (show coordinateTaylorQuotient f j x a ∈ coordinateTaylorQuotients f j from
        ⟨x, a, ha, rfl⟩)
    change coordinateTaylorQuotient f j x a ≤ coordinateSmoothness f j at hs
    unfold coordinateTaylorQuotient at hs
    have h := (div_le_iff₀ (sq_pos_of_ne_zero ha)).mp hs
    nlinarith

theorem strongConvex_le_coordinateSmoothness {p : ℕ} (f : State p → ℝ)
    (m : ℝ) (M : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hsc : StrongConvexOn Set.univ m f) (hLip : LipschitzWith M (gradient f))
    (j : Fin p) : m ≤ coordinateSmoothness f j := by
  have hl := ULA.strong_first_order hdiff hsc (0 : State p) (coordinateVector j)
  have hu := coordinate_upper_bound f M hdiff hLip j 0 1
  simp only [sub_zero, norm_coordinateVector, one_pow, mul_one,
    inner_coordinateVector] at hl
  simp only [one_smul, zero_add, one_mul, one_pow, mul_one] at hu
  linarith

theorem averageSmoothness_le_global_bound {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f)) : averageSmoothness f ≤ (M : ℝ) := by
  unfold averageSmoothness
  apply (div_le_iff₀ (by exact_mod_cast hp : (0 : ℝ) < p)).mpr
  simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ)
    (fun j _ ↦ coordinateSmoothness_le_global_bound f M hdiff hLip j)

/-- Each coordinate constant is at most the exact global gradient seminorm. -/
theorem coordinateSmoothness_le_globalSmoothness {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f)) (j : Fin p) :
    coordinateSmoothness f j ≤ globalSmoothness f :=
  coordinateSmoothness_le_global_bound f
    ⟨globalSmoothness f, globalSmoothness_nonneg hp f M hLip⟩ hdiff
    (gradient_lipschitz_globalSmoothness hp f M hLip) j

/-- The paper's average coordinate constant is at most its exact global
gradient seminorm, without replacing either constant by a chosen bound. -/
theorem averageSmoothness_le_globalSmoothness {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (M : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f)) :
    averageSmoothness f ≤ globalSmoothness f :=
  averageSmoothness_le_global_bound hp f
    ⟨globalSmoothness f, globalSmoothness_nonneg hp f M hLip⟩ hdiff
    (gradient_lipschitz_globalSmoothness hp f M hLip)

theorem strongConvex_le_averageSmoothness {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (m : ℝ) (M : ℝ≥0) (hdiff : Differentiable ℝ f)
    (hsc : StrongConvexOn Set.univ m f) (hLip : LipschitzWith M (gradient f)) :
    m ≤ averageSmoothness f := by
  unfold averageSmoothness
  apply (le_div_iff₀ (by exact_mod_cast hp : (0 : ℝ) < p)).mpr
  simpa [mul_comm] using Finset.sum_le_sum (s := Finset.univ)
    (fun j _ ↦ strongConvex_le_coordinateSmoothness f m M hdiff hsc hLip j)

/-- The trace of the true Hessian equals the true Laplacian. -/
theorem trace_hessian {p : ℕ} (f : State p → ℝ) (x : State p) :
    Matrix.trace (hessian f x) = laplacian f x := by
  rw [laplacian, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin p) ℝ)]
  simp [Matrix.trace, hessian, coordinateVector, EuclideanSpace.basisFun_apply]

end AverageLMC
