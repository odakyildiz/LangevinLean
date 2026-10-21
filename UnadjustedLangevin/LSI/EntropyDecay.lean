import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar entropy-decay comparison

This file proves scalar differential comparisons only. In particular, it does
not assert that a measure-valued Langevin evolution has differentiable relative
entropy, or that its entropy derivative equals minus its Fisher information.
Such analytic facts must be established separately before applying these lemmas.

The last theorem combines an explicitly supplied dissipation identity with the
scalar inequality `2 * α * H ≤ I`, in the normalization commonly used for a
log-Sobolev inequality, to obtain exponential decay at rate `2 * α`.
-/

namespace ULA.LSI

open Set

/-- A scalar differential inequality with negative linear drift gives the exact
finite-time affine comparison. Continuity and every right derivative are
explicit assumptions. No sign assumption on the function or forcing is needed. -/
theorem affine_decay_of_deriv_right_le (H H' : ℝ → ℝ) (a b T : ℝ)
    (ha : 0 < a) (hcont : ContinuousOn H (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt H (H' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico 0 T, H' t ≤ -a * H t + b) :
    ∀ t ∈ Icc 0 T,
      H t ≤ Real.exp (-a * t) * H 0 + b / a * (1 - Real.exp (-a * t)) := by
  have hcompare := le_gronwallBound_of_liminf_deriv_right_le hcont
    (fun t ht r hr ↦ (hderiv t ht).liminf_right_slope_le hr)
    (le_refl (H 0)) hbound
  intro t ht
  have h := hcompare t ht
  rw [gronwallBound_of_K_ne_0 (neg_ne_zero.mpr ha.ne'), sub_zero] at h
  convert h using 1
  ring

/-- A scalar dissipation identity and the scalar LSI inequality imply entropy
decay. The theorem does not itself identify `H` or `I` with measure-theoretic
relative entropy or Fisher information, nor prove their dissipation identity. -/
theorem entropy_decay_of_dissipation (H I : ℝ → ℝ) (α T : ℝ)
    (hα : 0 < α) (hcont : ContinuousOn H (Icc 0 T))
    (hdissipation : ∀ t ∈ Ico 0 T, HasDerivWithinAt H (-I t) (Ici t) t)
    (hlsi : ∀ t ∈ Ico 0 T, 2 * α * H t ≤ I t) :
    ∀ t ∈ Icc 0 T, H t ≤ Real.exp (-(2 * α) * t) * H 0 := by
  have hcompare := affine_decay_of_deriv_right_le H (fun t ↦ -I t)
    (2 * α) 0 T (by linarith) hcont hdissipation
    (fun t ht ↦ by have := hlsi t ht; linarith)
  simpa only [zero_div, zero_mul, add_zero] using hcompare

end ULA.LSI
