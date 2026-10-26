import LatentDiffusion.Variational
import Mathlib.Analysis.ODE.Gronwall

/-! Conditional continuous-time entropy theory for the actual normalized free
energy. The first-order transport inequality and the entropy dissipation identity
are explicit analytic bridge hypotheses. This module does not construct a
Wasserstein gradient flow or derive these bridges from density smoothness. -/
noncomputable section
open MeasureTheory Set Filter
namespace LatentDiffusion

/-- Completing the square derives extended LSI from a first-order strong
convexity bound toward an optimizer. `r` is the transport distance and `I` the
squared metric slope (Fisher information in the gradient-flow application). -/
theorem extendedLSI_of_firstOrder {gap I r rho : ℝ} (hrho : 0 < rho)
    (hI : 0 ≤ I) (hfirst : gap ≤ Real.sqrt I * r - rho / 2 * r ^ 2) :
    2 * rho * gap ≤ I := by
  have hs := sq_nonneg (Real.sqrt I - rho * r)
  have hroot := Real.sq_sqrt hI
  nlinarith

namespace PosteriorFamily
variable {A Z : Type*} [MeasurableSpace Z] {M : ℕ}

/-- Free-energy decay along a path of actual probability measures. The slope
inequality is derived from first-order transport control, rather than assumed
as an extended LSI. Entropy differentiation remains an explicit hypothesis. -/
theorem freeEnergy_decay_of_firstOrder
    (P : PosteriorFamily A Z M) (a : ℝ → A)
    (q : ℝ → Fin M → ProbabilityMeasure Z) (Fstar rho T : ℝ)
    (I r : ℝ → ℝ) (hrho : 0 < rho)
    (hadm : ∀ t ∈ Icc 0 T, P.Admissible (a t) (q t))
    (hcont : ContinuousOn (fun t => P.freeEnergy (a t) (q t) - Fstar) (Icc 0 T))
    (hdiss : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => P.freeEnergy (a s) (q s) - Fstar) (-I t) (Ici t) t)
    (hI : ∀ t ∈ Ico 0 T, 0 ≤ I t)
    (hfirst : ∀ t ∈ Ico 0 T,
      P.freeEnergy (a t) (q t) - Fstar ≤ Real.sqrt (I t) * r t - rho / 2 * (r t) ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    P.Admissible (a t) (q t) ∧
    P.freeEnergy (a t) (q t) - Fstar ≤
      (P.freeEnergy (a 0) (q 0) - Fstar) * Real.exp (-2 * rho * t) := by
  refine ⟨hadm t ht, ?_⟩
  have h := le_gronwallBound_of_liminf_deriv_right_le (K := -2 * rho) (ε := 0) hcont
    (fun s hs c hc => (hdiss s hs).liminf_right_slope_le hc)
    (le_refl (P.freeEnergy (a 0) (q 0) - Fstar))
    (fun s hs => by
      have hh := extendedLSI_of_firstOrder hrho (hI s hs) (hfirst s hs)
      linarith) t ht
  simpa only [gronwallBound_ε0, sub_zero] using h

/-- The actual average posterior KL is controlled by the free-energy excess
above any global evidence maximizer. -/
theorem posteriorKL_le_excess
    (P : PosteriorFamily A Z M) (astar a : A)
    (hmax : ∀ b, P.logEvidence b ≤ P.logEvidence astar)
    (q : Fin M → ProbabilityMeasure Z) :
    (M : ℝ)⁻¹ * ∑ i, (InformationTheory.klDiv (q i : Measure Z)
      (P.posterior a i : Measure Z)).toReal ≤
    P.freeEnergy a q - P.freeEnergy astar (P.posterior astar) := by
  rw [P.posterior_freeEnergy]
  unfold freeEnergy
  have h := hmax a
  linarith

/-- Exponential decay of actual average posterior KL, after specializing the
reference energy to the posterior at an evidence maximizer. -/
theorem posteriorKL_decay_of_firstOrder
    (P : PosteriorFamily A Z M) (a : ℝ → A)
    (q : ℝ → Fin M → ProbabilityMeasure Z) (astar : A) (rho T : ℝ)
    (I r : ℝ → ℝ) (hrho : 0 < rho)
    (hmax : ∀ b, P.logEvidence b ≤ P.logEvidence astar)
    (hadm : ∀ t ∈ Icc 0 T, P.Admissible (a t) (q t))
    (hcont : ContinuousOn (fun t => P.freeEnergy (a t) (q t) -
      P.freeEnergy astar (P.posterior astar)) (Icc 0 T))
    (hdiss : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s => P.freeEnergy (a s) (q s) -
        P.freeEnergy astar (P.posterior astar)) (-I t) (Ici t) t)
    (hI : ∀ t ∈ Ico 0 T, 0 ≤ I t)
    (hfirst : ∀ t ∈ Ico 0 T,
      P.freeEnergy (a t) (q t) - P.freeEnergy astar (P.posterior astar) ≤
        Real.sqrt (I t) * r t - rho / 2 * (r t) ^ 2)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (M : ℝ)⁻¹ * ∑ i, (InformationTheory.klDiv (q t i : Measure Z)
      (P.posterior (a t) i : Measure Z)).toReal ≤
    (P.freeEnergy (a 0) (q 0) - P.freeEnergy astar (P.posterior astar)) *
      Real.exp (-2 * rho * t) := by
  exact (P.posteriorKL_le_excess astar (a t) hmax (q t)).trans
    (P.freeEnergy_decay_of_firstOrder a q _ rho T I r hrho hadm hcont hdiss hI hfirst t ht).2

end PosteriorFamily
end LatentDiffusion
