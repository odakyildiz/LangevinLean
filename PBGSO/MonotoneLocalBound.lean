import Mathlib.Analysis.InnerProductSpace.PiL2

/-! An everywhere-defined monotone field is locally bounded in finite
dimension. The finite test points are fixed independently of an auxiliary
variable, so their common growth bound is preserved. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.MonotoneLocalBound
variable {E A ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι]

theorem norm_le_sum_abs_inner (b : OrthonormalBasis ι ℝ E) (v : E) :
    ‖v‖ ≤ ∑ i, |⟪b i, v⟫_ℝ| := by
  calc
    ‖v‖ = ‖∑ i, ⟪b i,v⟫_ℝ • b i‖ := congrArg norm (b.sum_repr' v).symm
    _ ≤ ∑ i, ‖⟪b i,v⟫_ℝ • b i‖ := norm_sum_le _ _
    _ = _ := by simp [norm_smul, b.orthonormal.norm_eq_one]

theorem norm_le_of_vertices (b : OrthonormalBasis ι ℝ E) (T : E → E)
    (hT : ∀ x y, 0 ≤ ⟪x-y, T x-T y⟫_ℝ)
    (x₀ x : E) (C : ℝ) (hC : 0 ≤ C)
    (hplus : ∀ i, ‖T (x₀+b i)‖ ≤ C)
    (hminus : ∀ i, ‖T (x₀-b i)‖ ≤ C)
    (hd : ‖x-x₀‖ ≤ 1)
    (hsmall : (Fintype.card ι : ℝ) * ‖x-x₀‖ ≤ 1/2) :
    ‖T x‖ ≤ 4 * (Fintype.card ι : ℝ) * C := by
  have hcomp (i : ι) : |⟪b i,T x⟫_ℝ| ≤ ‖x-x₀‖ * ‖T x‖ + 2*C := by
    have htest (v : E) (hv : ‖v‖ = 1) (hanchor : ‖T (x₀+v)‖ ≤ C) :
        ⟪v,T x⟫_ℝ ≤ ‖x-x₀‖ * ‖T x‖ + 2*C := by
      have hm := hT x (x₀+v)
      have hi : ⟪x-(x₀+v),T x-T (x₀+v)⟫_ℝ =
          ⟪x-x₀,T x⟫_ℝ - ⟪v,T x⟫_ℝ - ⟪x-(x₀+v),T (x₀+v)⟫_ℝ := by
        have he : x-(x₀+v) = (x-x₀)-v := by abel
        rw [inner_sub_right, he, inner_sub_left]
      have hn : ‖x-(x₀+v)‖ ≤ 2 := by
        calc
          _ = ‖(x-x₀)-v‖ := by congr 1; abel
          _ ≤ ‖x-x₀‖ + ‖v‖ := norm_sub_le _ _
          _ ≤ 2 := by linarith
      have h1 := real_inner_le_norm (x-x₀) (T x)
      have h2 : -⟪x-(x₀+v),T (x₀+v)⟫_ℝ ≤ 2*C := by
        calc
          _ ≤ ‖x-(x₀+v)‖ * ‖T (x₀+v)‖ :=
            (neg_le_abs _).trans (abs_real_inner_le_norm _ _)
          _ ≤ 2*C := mul_le_mul hn hanchor (norm_nonneg _) (by norm_num)
      rw [hi] at hm
      linarith
    apply abs_le.mpr
    constructor
    · have hm := htest (-b i) (by simp [b.orthonormal.norm_eq_one])
        (by simpa only [sub_eq_add_neg] using hminus i)
      simp only [inner_neg_left] at hm
      linarith
    · exact htest (b i) (b.orthonormal.norm_eq_one i) (hplus i)
  have hs : ‖T x‖ ≤ (Fintype.card ι : ℝ) * (‖x-x₀‖*‖T x‖ + 2*C) := by
    calc
      _ ≤ ∑ i, |⟪b i,T x⟫_ℝ| := norm_le_sum_abs_inner b _
      _ ≤ ∑ _ : ι, (‖x-x₀‖*‖T x‖ + 2*C) := Finset.sum_le_sum (fun i _ => hcomp i)
      _ = _ := by simp; ring
  have hm := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (T x))
  nlinarith

theorem uniform_growth_on_compact [FiniteDimensional ℝ E]
    (T : A → E → E) (w : A → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hT : ∀ a x y, 0 ≤ ⟪x-y,T a x-T a y⟫_ℝ)
    (hg : ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖T a x‖ ≤ C*w a)
    (K : Set E) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ a, ‖T a x‖ ≤ C*w a := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let d : ℝ := Module.finrank ℝ E
  have hd : 0 ≤ d := Nat.cast_nonneg _
  let δ : ℝ := 1/(2*(d+1))
  have hden : 0 < 2*(d+1) := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hδ1 : δ ≤ 1 := (div_le_one hden).mpr (by linarith)
  choose C hC hCg using hg
  let B : E → ℝ := fun x₀ => ∑ i, (C (x₀+b i) + C (x₀-b i))
  have hB : ∀ x₀, 0 ≤ B x₀ := fun x₀ =>
    Finset.sum_nonneg (fun i _ => add_nonneg (hC _) (hC _))
  have hlocal (x₀ x : E) (hx : x ∈ Metric.ball x₀ δ) (a : A) :
      ‖T a x‖ ≤ (4*d*B x₀)*w a := by
    have hdist : ‖x-x₀‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hsmall : d * ‖x-x₀‖ ≤ 1/2 := by
      have hp : ‖x-x₀‖ * (2*(d+1)) < 1 := (lt_div_iff₀ hden).mp hdist
      nlinarith [norm_nonneg (x-x₀)]
    have hvertex (i : Fin (Module.finrank ℝ E)) :
        C (x₀+b i) ≤ B x₀ ∧ C (x₀-b i) ≤ B x₀ := by
      have hh : C (x₀+b i)+C (x₀-b i) ≤ B x₀ :=
        Finset.single_le_sum (f := fun j => C (x₀+b j)+C (x₀-b j))
          (fun j _ => add_nonneg (hC _) (hC _)) (Finset.mem_univ i)
      constructor <;> linarith [hC (x₀+b i),hC (x₀-b i)]
    have hh := norm_le_of_vertices b (T a) (hT a) x₀ x (B x₀*w a)
      (mul_nonneg (hB _) (hw _))
      (fun i => (hCg _ a).trans (mul_le_mul_of_nonneg_right (hvertex i).1 (hw _)))
      (fun i => (hCg _ a).trans (mul_le_mul_of_nonneg_right (hvertex i).2 (hw _)))
      (hdist.le.trans hδ1) (by simpa only [Fintype.card_fin] using hsmall)
    simpa only [Fintype.card_fin, d, mul_assoc] using hh
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun x₀ => Metric.ball x₀ δ)
    (fun _ => Metric.isOpen_ball) (fun x _ => Set.mem_iUnion.mpr ⟨x,Metric.mem_ball_self hδ⟩)
  have hB' (x₀ : E) : 0 ≤ 4*d*B x₀ := mul_nonneg (mul_nonneg (by norm_num) hd) (hB _)
  refine ⟨∑ x₀ ∈ s,4*d*B x₀,Finset.sum_nonneg (fun x₀ _ => hB' _),?_⟩
  intro x hx a
  obtain ⟨x₀,hx₀⟩ := Set.mem_iUnion.mp (hs hx)
  obtain ⟨hx₀s,hball⟩ := Set.mem_iUnion.mp hx₀
  exact (hlocal x₀ x hball a).trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun y => 4*d*B y) (fun y _ => hB' _) hx₀s) (hw a))

end PBGSO.MonotoneLocalBound
