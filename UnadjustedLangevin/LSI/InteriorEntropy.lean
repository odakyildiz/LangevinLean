import UnadjustedLangevin.LSI.EntropyDecay
import UnadjustedLangevin.LSI.Regularity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option linter.style.header false

/-! # Entropy comparison from positive-time derivatives

Gaussian convolution is smooth at positive times even when the initial law
has no smooth positive density. The comparison below needs continuity at the
initial time and ordinary derivatives only on the open time interval. Thus
an entropy argument need not manufacture a two-sided smooth continuation
through time zero merely to perform its scalar comparison.
-/

namespace ULA.LSI

open Set MeasureTheory Filter
open scoped Topology

/-- Affine entropy comparison using derivatives only in the interior.
Endpoint continuity is sufficient; neither endpoint requires a derivative. -/
theorem affine_decay_of_deriv_le_interior (H H' : ℝ → ℝ) (a b T : ℝ)
    (ha : 0 < a) (hcont : ContinuousOn H (Icc 0 T))
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt H (H' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, H' t ≤ -a * H t + b) :
    ∀ t ∈ Icc 0 T,
      H t ≤ Real.exp (-a * t) * H 0 + b / a * (1 - Real.exp (-a * t)) := by
  let F : ℝ → ℝ := fun t ↦ Real.exp (a * t) * (H t - b / a)
  have hFcont : ContinuousOn F (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (hcont.sub continuousOn_const)
  have hFderiv (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt F (Real.exp (a * t) * (a * (H t - b / a) + H' t)) t := by
    have he := ((hasDerivAt_id t).const_mul a).exp
    convert he.mul ((hderiv t ht).sub_const (b / a)) using 1
    · ext x
      simp [F]
    · simp only [id_eq, mul_one]
      ring
  have hFnonpos (t : ℝ) (ht : t ∈ Ioo 0 T) :
      Real.exp (a * t) * (a * (H t - b / a) + H' t) ≤ 0 := by
    have hab : a * (b / a) = b := by field_simp
    have h := hbound t ht
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _)
    nlinarith
  have hanti : AntitoneOn F (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hFcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hFderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFderiv t ht).deriv]
      exact hFnonpos t ht
  intro t ht
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have h := hanti hzero ht ht.1
  have hexp : Real.exp (-a * t) * Real.exp (a * t) = 1 := by
    rw [← Real.exp_add, show -a * t + a * t = 0 by ring, Real.exp_zero]
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_nonneg (-a * t))
  dsimp [F] at hm
  simp only [mul_zero, Real.exp_zero, one_mul] at hm
  rw [← mul_assoc, hexp, one_mul] at hm
  nlinarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
/-- Positive-time local regularity gives an ordinary derivative of actual KL.
This result requests no density, differentiability or domination data at time
zero; the scalar comparison above only needs entropy continuity there. -/
theorem densityEntropy_hasDerivAt_of_regular_interior
    (ν : Measure E) [IsProbabilityMeasure ν] (r rdot : ℝ → E → ℝ) (T t : ℝ)
    (ht : t ∈ Ioo 0 T)
    (data : ∀ u ∈ Ioo 0 T, LocalEntropyRegularity ν r rdot u)
    (hpos : ∀ u ∈ Ioo 0 T, ∀ x, 0 < r u x)
    (hsmooth : ∀ u ∈ Ioo 0 T, ContDiff ℝ 1 (r u))
    (hprob : ∀ u ∈ Ioo 0 T, IsProbabilityMeasure (tiltedMeasure ν (r u))) :
    HasDerivAt (fun u ↦ densityEntropy ν (r u))
      (∫ x, rdot t x * (Real.log (r t x) + 1) ∂ν) t := by
  have hnear : (fun u ↦ densityEntropy ν (r u)) =ᶠ[𝓝 t]
      (fun u ↦ ∫ x, r u x * Real.log (r u x) ∂ν) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact densityEntropy_eq_integral ν (r u) (hsmooth u hu).continuous.measurable
      (fun x ↦ (hpos u hu x).le) (hprob u hu) (data u hu).integrable
  exact (data t ht).hasDerivAt_entropy.2.congr_of_eventuallyEq hnear

end ULA.LSI
