import UnadjustedLangevin.LSI.FunctionalInequality
import UnadjustedLangevin.LSI.EntropyDecay

set_option linter.style.header false

/-! # Relative entropy decay conditional on entropy dissipation

This theorem uses actual KL divergence and relative Fisher information. LSI
supplies the functional inequality. Continuity of entropy, finiteness, and
the entropy-dissipation identity are separate, explicit analytic hypotheses.
In particular, this file does not identify a stochastic Langevin solution or
ULA interpolation as satisfying those hypotheses.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]

/-- The real KL entropy of an explicitly specified relative density.
Use this only with a proof that the underlying extended KL value is finite. -/
def densityEntropy (ν : Measure E) (r : E → ℝ) : ℝ :=
  (InformationTheory.klDiv (tiltedMeasure ν r) ν).toReal

/-- The continuous-time LSI comparison for an admissible density path.
Every entropy regularity and dissipation obligation is displayed here; none
is inferred merely from a weak Fokker-Planck equation or an SDE definition. -/
theorem relative_entropy_decay_of_dissipation
    (ν : Measure E) (α T : ℝ) (hα : 0 < α) (hLSI : IsLogSobolev ν α)
    (r : ℝ → E → ℝ)
    (hr : ∀ t ∈ Icc 0 T, ∀ x, 0 < r t x)
    (hdiff : ∀ t ∈ Icc 0 T, ContDiff ℝ 1 (r t))
    (hprob : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (tiltedMeasure ν (r t)))
    (hKL : ∀ t ∈ Icc 0 T,
      InformationTheory.klDiv (tiltedMeasure ν (r t)) ν ≠ ⊤)
    (hFI : ∀ t ∈ Icc 0 T, relativeFisher ν (r t) ≠ ⊤)
    (hcont : ContinuousOn (fun t ↦ densityEntropy ν (r t)) (Icc 0 T))
    (hdissipation : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (fun s ↦ densityEntropy ν (r s))
        (-(relativeFisher ν (r t)).toReal) (Ici t) t) :
    ∀ t ∈ Icc 0 T,
      densityEntropy ν (r t) ≤ Real.exp (-(2 * α) * t) * densityEntropy ν (r 0) := by
  apply entropy_decay_of_dissipation
    (fun t ↦ densityEntropy ν (r t))
    (fun t ↦ (relativeFisher ν (r t)).toReal) α T hα hcont hdissipation
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  exact hLSI.entropy_le_fisher hα.le (r t) (hr t ht') (hdiff t ht')
    (hprob t ht') (hKL t ht') (hFI t ht')

end ULA.LSI
