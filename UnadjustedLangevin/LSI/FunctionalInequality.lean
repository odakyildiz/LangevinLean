import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option linter.style.header false

/-! # The log-Sobolev inequality for smooth positive relative densities

The entropy is Mathlib's extended-valued `InformationTheory.klDiv`, rather than
an arbitrary error functional. A test function `r` is the density relative to
the target `ν`; its induced measure is `ν.withDensity (ENNReal.ofReal ∘ r)`.
The relative Fisher information integrates `‖∇ log r‖²` against that measure.

`IsLogSobolev` is the smooth positive density formulation of LSI, with the
normalization `2 * α * KL ≤ Fisher`. It is a property of the target measure
and does not assume any Langevin or ULA convergence statement. The positivity,
continuous differentiability, and probability conditions are explicit in its test class.
No assertion about approximation by this test class is made here.

Real-valued consequences require finite entropy and finite Fisher information.
This avoids treating the `toReal` value of infinity as a finite entropy.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ULA.LSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E]

/-- The probability candidate with density `r` relative to the target `ν`. -/
def tiltedMeasure (ν : Measure E) (r : E → ℝ) : Measure E :=
  ν.withDensity (fun x ↦ ENNReal.ofReal (r x))

/-- Relative Fisher information for the specified smooth relative density.
Using `r` explicitly avoids differentiating a merely almost-everywhere
representative of the Radon-Nikodym derivative. -/
def relativeFisher (ν : Measure E) (r : E → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖gradient (fun y ↦ Real.log (r y)) x‖ ^ 2)
    ∂tiltedMeasure ν r

/-- LSI tested on continuously differentiable, strictly positive probability densities
relative to `ν`. The constant convention agrees with Wibisono's papers. -/
def IsLogSobolev [BorelSpace E] (ν : Measure E) (α : ℝ) : Prop :=
  IsProbabilityMeasure ν ∧
  ∀ r : E → ℝ, (∀ x, 0 < r x) → ContDiff ℝ 1 r →
    IsProbabilityMeasure (tiltedMeasure ν r) →
    ENNReal.ofReal (2 * α) * InformationTheory.klDiv (tiltedMeasure ν r) ν ≤
      relativeFisher ν r

/-- A finite test of the genuine LSI gives its ordinary real inequality.
Both finiteness guards are retained, so neither extended value is discarded. -/
theorem IsLogSobolev.entropy_le_fisher [BorelSpace E]
    {ν : Measure E} {α : ℝ} (hLSI : IsLogSobolev ν α) (hα : 0 ≤ α)
    (r : E → ℝ) (hr : ∀ x, 0 < r x) (hdiff : ContDiff ℝ 1 r)
    (hprob : IsProbabilityMeasure (tiltedMeasure ν r))
    (hKL : InformationTheory.klDiv (tiltedMeasure ν r) ν ≠ ⊤)
    (hFI : relativeFisher ν r ≠ ⊤) :
    2 * α * (InformationTheory.klDiv (tiltedMeasure ν r) ν).toReal ≤
      (relativeFisher ν r).toReal := by
  have h := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKL) hFI).mpr
      (hLSI.2 r hr hdiff hprob)
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * α)]
    using h

end ULA.LSI
