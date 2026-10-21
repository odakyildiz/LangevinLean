import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option linter.style.header false

/-! # The one-dimensional transport proof of Prékopa--Leindler

All transport maps in this file are constructed from cumulative integrals. No
transport existence, marginal log-concavity, or concentration statement is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace IPLA.Prekopa

/-- A positive, continuous probability density on the real line. -/
structure Density (f : ℝ → ℝ) : Prop where
  continuous : Continuous f
  positive : ∀ x, 0 < f x
  integrable : Integrable f volume
  integral_one : ∫ x, f x ∂volume = 1

/-- Cumulative integral of an ordinary real density. -/
def cumulative (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in Iic x, f t ∂volume

namespace Density

variable {f g : ℝ → ℝ} (hf : Density f)
include hf

theorem cumulative_hasStrictDerivAt (x : ℝ) :
    HasStrictDerivAt (cumulative f) (f x) x := by
  have heq : cumulative f = fun y ↦ cumulative f 0 + ∫ t in (0 : ℝ)..y, f t := by
    funext y
    have h := intervalIntegral.integral_Iic_sub_Iic
      (hf.integrable.integrableOn (s := Iic 0)) (hf.integrable.integrableOn (s := Iic y))
    change cumulative f y - cumulative f 0 = _ at h
    linarith
  rw [heq]
  exact (hf.continuous.integral_hasStrictDerivAt 0 x).const_add _

theorem cumulative_continuous : Continuous (cumulative f) := by
  exact continuous_iff_continuousAt.mpr fun x ↦
    (hf.cumulative_hasStrictDerivAt x).hasDerivAt.continuousAt

theorem cumulative_strictMono : StrictMono (cumulative f) :=
  strictMono_of_hasDerivAt_pos (fun x ↦ (hf.cumulative_hasStrictDerivAt x).hasDerivAt) hf.positive

omit hf in
theorem cumulative_tendsto_atBot : Tendsto (cumulative f) atBot (𝓝 0) :=
  tendsto_integral_Iic_zero tendsto_id

theorem cumulative_tendsto_atTop : Tendsto (cumulative f) atTop (𝓝 1) := by
  have heq (x : ℝ) : cumulative f x = 1 - ∫ t in Ioi x, f t := by
    have h := intervalIntegral.integral_Iic_add_Ioi
      (hf.integrable.integrableOn (s := Iic x)) (hf.integrable.integrableOn (s := Ioi x))
    rw [hf.integral_one] at h
    change cumulative f x + _ = _ at h
    linarith
  rw [show cumulative f = fun x ↦ 1 - ∫ t in Ioi x, f t from funext heq]
  simpa using (tendsto_integral_Ioi_zero (f := f) (μ := volume) tendsto_id).const_sub 1

theorem cumulative_mem_Ioo (x : ℝ) : cumulative f x ∈ Ioo (0 : ℝ) 1 := by
  have hnonneg (y : ℝ) : 0 ≤ cumulative f y := integral_nonneg fun t ↦ (hf.positive t).le
  have hle (y : ℝ) : cumulative f y ≤ 1 := by
    have h := intervalIntegral.integral_Iic_add_Ioi
      (hf.integrable.integrableOn (s := Iic y)) (hf.integrable.integrableOn (s := Ioi y))
    rw [hf.integral_one] at h
    have hp : 0 ≤ ∫ t in Ioi y, f t := integral_nonneg fun t ↦ (hf.positive t).le
    change cumulative f y + _ = _ at h
    linarith
  constructor
  · exact lt_of_le_of_lt (hnonneg (x - 1)) (hf.cumulative_strictMono (by linarith))
  · exact lt_of_lt_of_le (hf.cumulative_strictMono (by linarith : x < x + 1)) (hle (x + 1))

theorem cumulative_range : range (cumulative f) = Ioo (0 : ℝ) 1 := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact hf.cumulative_mem_Ioo x
  · intro y hy
    apply mem_range_of_exists_le_of_exists_ge hf.cumulative_continuous
    · obtain ⟨x, hx⟩ := (cumulative_tendsto_atBot.eventually_lt_const hy.1).exists
      exact ⟨x, hx.le⟩
    · obtain ⟨x, hx⟩ := (hf.cumulative_tendsto_atTop.eventually_const_lt hy.2).exists
      exact ⟨x, hx.le⟩

end Density

/-- The monotone transport from density `f` to density `g`. -/
def transport (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  Function.invFun (cumulative g) (cumulative f x)

namespace Density

variable {f g : ℝ → ℝ} (hf : Density f) (hg : Density g)
include hf hg

theorem cumulative_transport (x : ℝ) :
    cumulative g (transport f g x) = cumulative f x := by
  have hx : cumulative f x ∈ range (cumulative g) := by
    rw [hg.cumulative_range]
    exact hf.cumulative_mem_Ioo x
  obtain ⟨y, hy⟩ := hx
  unfold transport
  rw [← hy]
  exact Function.apply_invFun_apply

theorem transport_hasStrictDerivAt (x : ℝ) :
    HasStrictDerivAt (transport f g) (f x / g (transport f g x)) x := by
  have hinv := (hg.cumulative_hasStrictDerivAt (transport f g x)).to_local_left_inverse
    (g := Function.invFun (cumulative g)) (hg.positive _).ne'
    (Filter.Eventually.of_forall (Function.leftInverse_invFun hg.cumulative_strictMono.injective))
  rw [hf.cumulative_transport hg x] at hinv
  convert hinv.comp x (hf.cumulative_hasStrictDerivAt x) using 1
  · rfl
  · simp only [div_eq_mul_inv, mul_comm]

theorem transport_strictMono : StrictMono (transport f g) :=
  strictMono_of_hasDerivAt_pos
    (fun x ↦ (hf.transport_hasStrictDerivAt hg x).hasDerivAt)
    (fun x ↦ div_pos (hf.positive x) (hg.positive _))

end Density

/-- The normalized one-dimensional Prékopa--Leindler inequality, proved by
the constructed monotone transport. The third weight need not be continuous or
integrable; the conclusion is an extended nonnegative integral. -/
theorem normalized_prekopa_leindler
    {f g : ℝ → ℝ} (hf : Density f) (hg : Density g)
    (h : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hpoint : ∀ x y, Real.exp ((1 - t) * Real.log (f x) + t * Real.log (g y)) ≤
      h ((1 - t) * x + t * y)) :
    (1 : ℝ≥0∞) ≤ ∫⁻ z, ENNReal.ofReal (h z) ∂volume := by
  let S : ℝ → ℝ := fun x ↦ (1 - t) * x + t * transport f g x
  let S' : ℝ → ℝ := fun x ↦ (1 - t) + t * (f x / g (transport f g x))
  have ht0 : 0 ≤ 1 - t := by linarith
  have hS' (x : ℝ) : HasDerivAt S (S' x) x := by
    convert
      ((hasDerivAt_id x).const_mul (1 - t)).add
        ((hf.transport_hasStrictDerivAt hg x).hasDerivAt.const_mul t) using 1
    · rfl
    · dsimp [S']
      ring
  have hSpos (x : ℝ) : 0 < S' x := by
    have hp : 0 < f x / g (transport f g x) := div_pos (hf.positive x) (hg.positive _)
    dsimp [S']
    rcases eq_or_lt_of_le ht with he | ht
    · simp [← he]
    · exact add_pos_of_nonneg_of_pos ht0 (mul_pos ht hp)
  have hSmono : StrictMono S := strictMono_of_hasDerivAt_pos hS' hSpos
  have hpt (x : ℝ) : f x ≤ S' x * h (S x) := by
    have hc := hpoint x (transport f g x)
    change Real.exp _ ≤ h (S x) at hc
    have hj := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
      (Set.mem_univ (Real.log (f x) - Real.log (g (transport f g x))))
      ht0 ht (by ring : 1 - t + t = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
      Real.exp_sub, Real.exp_log (hf.positive x), Real.exp_log (hg.positive _)] at hj
    change Real.exp _ ≤ S' x at hj
    have he : Real.exp ((1 - t) * Real.log (f x) + t * Real.log (g (transport f g x))) *
        Real.exp (t * (Real.log (f x) - Real.log (g (transport f g x)))) = f x := by
      rw [← Real.exp_add]
      convert Real.exp_log (hf.positive x) using 1
      congr 1
      ring
    rw [← he]
    exact (mul_le_mul hc hj (Real.exp_nonneg _) (le_trans (Real.exp_nonneg _) hc)).trans_eq
      (mul_comm _ _)
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ ↦ (hS' x).hasDerivWithinAt) hSmono.injective.injOn
    (fun z ↦ ENNReal.ofReal (h z))
  calc
    (1 : ℝ≥0∞) = ∫⁻ x, ENNReal.ofReal (f x) ∂volume := by
      simpa only [hf.integral_one, ENNReal.ofReal_one] using
        (ofReal_integral_eq_lintegral_ofReal hf.integrable
          (ae_of_all _ fun x ↦ (hf.positive x).le))
    _ ≤ ∫⁻ x, ENNReal.ofReal |S' x| * ENNReal.ofReal (h (S x)) ∂volume := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (f x) ≤ ENNReal.ofReal |S' x| * ENNReal.ofReal (h (S x))
      rw [abs_of_pos (hSpos x), ← ENNReal.ofReal_mul (hSpos x).le]
      exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ∫⁻ z in S '' Set.univ, ENNReal.ofReal (h z) ∂volume := by
      simpa only [setLIntegral_univ] using hchange.symm
    _ ≤ ∫⁻ z, ENNReal.ofReal (h z) ∂volume := by
      simpa only [setLIntegral_univ] using
        (lintegral_mono_set (f := fun z ↦ ENNReal.ofReal (h z))
          (μ := volume) (Set.subset_univ (S '' Set.univ)))

/-- Strict positivity of the real integral of an everywhere positive integrable
function, including the zero-dimensional product space used in tensorization. -/
theorem integral_positive {E : Type*} [MeasureSpace E]
    [NeZero (volume : Measure E)] {f : E → ℝ}
    (hpos : ∀ x, 0 < f x) (hi : Integrable f volume) : 0 < ∫ x, f x ∂volume := by
  rw [integral_pos_iff_support_of_nonneg (fun x ↦ (hpos x).le) hi]
  have hs : Function.support f = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hpos x).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr (NeZero.ne _)

/-- Prékopa--Leindler on the real line for arbitrary positive continuous
integrable first and second weights. No normalization is assumed. -/
theorem prekopa_leindler_real
    {f g h : ℝ → ℝ} (hfcont : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hfint : Integrable f volume) (hgcont : Continuous g) (hgpos : ∀ x, 0 < g x)
    (hgint : Integrable g volume) (hhint : Integrable h volume) (hhpos : ∀ x, 0 ≤ h x)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hpoint : ∀ x y, Real.exp ((1 - t) * Real.log (f x) + t * Real.log (g y)) ≤
      h ((1 - t) * x + t * y)) :
    Real.exp ((1 - t) * Real.log (∫ x, f x) + t * Real.log (∫ x, g x)) ≤ ∫ x, h x := by
  let A := ∫ x, f x
  let B := ∫ x, g x
  let C := Real.exp ((1 - t) * Real.log A + t * Real.log B)
  have hA : 0 < A := integral_positive hfpos hfint
  have hB : 0 < B := integral_positive hgpos hgint
  have hC : 0 < C := Real.exp_pos _
  have hf : Density (fun x ↦ f x / A) :=
    ⟨hfcont.div_const A, fun x ↦ div_pos (hfpos x) hA, hfint.div_const A,
      by rw [integral_div]; exact div_self hA.ne'⟩
  have hg : Density (fun x ↦ g x / B) :=
    ⟨hgcont.div_const B, fun x ↦ div_pos (hgpos x) hB, hgint.div_const B,
      by rw [integral_div]; exact div_self hB.ne'⟩
  have hnorm := normalized_prekopa_leindler hf hg (fun x ↦ h x / C) t ht ht1 (by
    intro x y
    have he : Real.exp ((1 - t) * Real.log (f x / A) + t * Real.log (g y / B)) =
        Real.exp ((1 - t) * Real.log (f x) + t * Real.log (g y)) / C := by
      dsimp [C]
      rw [Real.log_div (hfpos x).ne' hA.ne', Real.log_div (hgpos y).ne' hB.ne',
        ← Real.exp_sub]
      congr 1
      ring
    rw [he]
    exact div_le_div_of_nonneg_right (hpoint x y) hC.le)
  rw [← ofReal_integral_eq_lintegral_ofReal (hhint.div_const C)
    (ae_of_all _ fun x ↦ div_nonneg (hhpos x) hC.le), ENNReal.one_le_ofReal,
    integral_div] at hnorm
  change C ≤ _
  simpa only [one_mul] using (le_div_iff₀ hC).mp hnorm

end IPLA.Prekopa
