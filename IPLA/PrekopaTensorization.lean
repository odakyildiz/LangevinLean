import IPLA.PrekopaLeindler
import UnadjustedLangevin.Gibbs
import Mathlib.MeasureTheory.Integral.Pi

set_option linter.style.header false

/-! # Finite-dimensional Prékopa--Leindler for Gaussian-tailed positive weights

Gaussian domination is preserved by integrating a coordinate. It supplies all
integrability and continuity needed to iterate the proved one-dimensional
transport inequality. Strongly convex Gibbs weights satisfy this domination.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace IPLA.Prekopa

abbrev Coordinates (n : ℕ) := Fin n → ℝ

/-- The class of positive continuous weights with a Gaussian upper bound. -/
structure GaussianWeight (n : ℕ) (f : Coordinates n → ℝ) : Prop where
  continuous : Continuous f
  positive : ∀ x, 0 < f x
  gaussian_bound : ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
    ∀ x, f x ≤ C * Real.exp (-a * ∑ i, (x i) ^ 2)

namespace GaussianWeight
variable {n : ℕ} {f : Coordinates n → ℝ} (hf : GaussianWeight n f)
include hf

theorem integrable : Integrable f volume := by
  obtain ⟨C, a, hC, ha, hb⟩ := hf.gaussian_bound
  have hi := (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_of_integrable
    (ULA.integrable_exp_neg_mul_norm_sq (H := EuclideanSpace ℝ (Fin n)) a ha)
  have hig : Integrable (fun x : Coordinates n ↦
      C * Real.exp (-a * ∑ i, (x i) ^ 2)) volume := by
    simpa only [Function.comp_apply, EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply]
      using hi.const_mul C
  apply hig.mono' hf.continuous.aestronglyMeasurable
  exact ae_of_all _ fun x ↦ by simpa [Real.norm_eq_abs, abs_of_pos (hf.positive x)] using hb x

theorem integral_pos : 0 < ∫ x, f x ∂volume :=
  integral_positive hf.positive hf.integrable

theorem const_mul (c : ℝ) (hc : 0 < c) : GaussianWeight n (fun x ↦ c * f x) := by
  obtain ⟨C, a, hC, ha, hb⟩ := hf.gaussian_bound
  refine ⟨continuous_const.mul hf.continuous, fun x ↦ mul_pos hc (hf.positive x),
    c * C, a, mul_pos hc hC, ha, ?_⟩
  intro x
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb x) hc.le

end GaussianWeight

/-- Continuity of inserting the first real coordinate. -/
theorem continuous_cons {n : ℕ} :
    Continuous (fun p : ℝ × Coordinates n ↦ (Fin.cons p.1 p.2 : Coordinates (n + 1))) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simpa using (continuous_fst : Continuous (Prod.fst : ℝ × Coordinates n → ℝ))
  · change Continuous (fun p : ℝ × Coordinates n ↦ p.2 i)
    fun_prop

/-- Integrate out the first coordinate of a weight. -/
def firstMarginal {n : ℕ} (f : Coordinates (n + 1) → ℝ) (x : Coordinates n) : ℝ :=
  ∫ z : ℝ, f (Fin.cons z x) ∂volume

namespace GaussianWeight
variable {n : ℕ} {f : Coordinates (n + 1) → ℝ} (hf : GaussianWeight (n + 1) f)
include hf

theorem slice_integrable (x : Coordinates n) :
    Integrable (fun z : ℝ ↦ f (Fin.cons z x)) volume := by
  obtain ⟨C, a, hC, ha, hb⟩ := hf.gaussian_bound
  have hi : Integrable (fun z : ℝ ↦ C * Real.exp (-a * z ^ 2)) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (ULA.integrable_exp_neg_mul_norm_sq (H := ℝ) a ha).const_mul C
  apply hi.mono'
  · exact (hf.continuous.comp
      (continuous_cons.comp (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hf.positive _)]
    have hbz := hb (Fin.cons z x)
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hbz
    apply hbz.trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    have hs : 0 ≤ ∑ i : Fin n, (x i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    nlinarith

theorem firstMarginal_continuous : Continuous (firstMarginal f) := by
  obtain ⟨C, a, hC, ha, hb⟩ := hf.gaussian_bound
  apply continuous_of_dominated (bound := fun z : ℝ ↦ C * Real.exp (-a * z ^ 2))
  · exact fun x ↦ (hf.slice_integrable x).aestronglyMeasurable
  · intro x
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_of_pos (hf.positive _)]
    apply (hb (Fin.cons z x)).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hs : 0 ≤ ∑ i : Fin n, (x i) ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    nlinarith
  · simpa only [Real.norm_eq_abs, sq_abs] using
      (ULA.integrable_exp_neg_mul_norm_sq (H := ℝ) a ha).const_mul C
  · apply ae_of_all
    intro z
    exact hf.continuous.comp
      (continuous_cons.comp (continuous_const.prodMk continuous_id))

theorem firstMarginal_gaussian : GaussianWeight n (firstMarginal f) := by
  obtain ⟨C, a, hC, ha, hb⟩ := hf.gaussian_bound
  have hi : Integrable (fun z : ℝ ↦ Real.exp (-a * z ^ 2)) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      ULA.integrable_exp_neg_mul_norm_sq (H := ℝ) a ha
  refine ⟨hf.firstMarginal_continuous,
    fun x ↦ integral_positive (fun z ↦ hf.positive (Fin.cons z x)) (hf.slice_integrable x),
    C * (∫ z : ℝ, Real.exp (-a * z ^ 2)), a,
    mul_pos hC (integral_positive (fun z ↦ Real.exp_pos _) hi), ha, ?_⟩
  intro x
  have hb' (z : ℝ) : f (Fin.cons z x) ≤
      (C * Real.exp (-a * ∑ i, (x i) ^ 2)) * Real.exp (-a * z ^ 2) := by
    have h := hb (Fin.cons z x)
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h
    convert h using 1
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h := integral_mono (hf.slice_integrable x)
    (hi.const_mul (C * Real.exp (-a * ∑ i, (x i) ^ 2))) hb'
  rw [integral_const_mul] at h
  change firstMarginal f x ≤ _ at h
  convert h using 1
  ring

theorem integral_firstMarginal : ∫ x, firstMarginal f x ∂volume = ∫ x, f x ∂volume := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).symm
  have he (p : ℝ × Coordinates n) : e.symm p = Fin.cons p.1 p.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  have hi : Integrable (fun p : ℝ × Coordinates n ↦ f (Fin.cons p.1 p.2)) volume := by
    convert hp.integrable_comp_of_integrable hf.integrable using 1
    funext p
    exact congrArg f (he p).symm
  have h := hp.integral_comp' f
  have heq : (∫ p : ℝ × Coordinates n, f (Fin.cons p.1 p.2) ∂volume) =
      ∫ x, f x ∂volume := by
    convert h using 1
    apply integral_congr_ae
    apply ae_of_all
    intro p
    exact congrArg f (he p).symm
  change Integrable (fun p : ℝ × Coordinates n ↦ f (Fin.cons p.1 p.2))
    ((volume : Measure ℝ).prod (volume : Measure (Coordinates n))) at hi
  change (∫ p : ℝ × Coordinates n, f (Fin.cons p.1 p.2)
    ∂(volume : Measure ℝ).prod (volume : Measure (Coordinates n))) = _ at heq
  rw [integral_prod _ hi, integral_integral_swap hi] at heq
  exact heq

end GaussianWeight

/-- The finite-dimensional Prékopa--Leindler inequality. The induction uses
the proved real-line transport theorem and integrates one coordinate at a time. -/
theorem prekopa_leindler {n : ℕ} {f g h : Coordinates n → ℝ}
    (hf : GaussianWeight n f) (hg : GaussianWeight n g) (hh : GaussianWeight n h)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hpoint : ∀ x y, Real.exp ((1 - t) * Real.log (f x) + t * Real.log (g y)) ≤
      h (fun i ↦ (1 - t) * x i + t * y i)) :
    Real.exp ((1 - t) * Real.log (∫ x, f x) + t * Real.log (∫ x, g x)) ≤ ∫ x, h x := by
  induction n with
  | zero =>
    let z : Coordinates 0 := fun i ↦ Fin.elim0 i
    have hi (u : Coordinates 0 → ℝ) : (∫ x, u x ∂volume) = u z := by
      have he : u = fun _ ↦ u z := by
        funext x
        congr 1
        funext i
        exact Fin.elim0 i
      rw [he, integral_const]
      simp [measureReal_def, volume_pi, Measure.pi_empty_univ]
    rw [hi f, hi g, hi h]
    convert hpoint z z using 1
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    have hm : ∀ x y : Coordinates n,
        Real.exp ((1 - t) * Real.log (firstMarginal f x) +
          t * Real.log (firstMarginal g y)) ≤
        firstMarginal h (fun i ↦ (1 - t) * x i + t * y i) := by
      intro x y
      apply prekopa_leindler_real
        (hf.continuous.comp (continuous_cons.comp (continuous_id.prodMk continuous_const)))
        (fun s ↦ hf.positive (Fin.cons s x)) (hf.slice_integrable x)
        (hg.continuous.comp (continuous_cons.comp (continuous_id.prodMk continuous_const)))
        (fun s ↦ hg.positive (Fin.cons s y)) (hg.slice_integrable y)
        (hh.slice_integrable _) (fun s ↦ (hh.positive _).le) t ht ht1
      intro s r
      convert hpoint (Fin.cons s x) (Fin.cons r y) using 1
      · rfl
      · apply congrArg h
        funext i
        refine Fin.cases ?_ (fun i ↦ ?_) i <;> rfl
    have h := ih hf.firstMarginal_gaussian hg.firstMarginal_gaussian
      hh.firstMarginal_gaussian hm
    rwa [hf.integral_firstMarginal, hg.integral_firstMarginal,
      hh.integral_firstMarginal] at h

end IPLA.Prekopa
