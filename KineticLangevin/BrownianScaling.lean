import UnadjustedLangevin.CanonicalBrownian
import Mathlib.Probability.BrownianMotion.Basic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace KineticLangevin

/-- The actual canonical Brownian coordinate at a changed clock, with the compensating square-root amplitude. -/
def clockBrownian {ι : Type*} (c : ℝ≥0) (i : ι) (t : ℝ≥0)
    (ω : ULA.CanonicalBrownian.VectorSample ι) : ℝ :=
  (Real.sqrt (c:ℝ)) * ULA.CanonicalBrownian.coordinate i (c⁻¹*t) ω

/-- Brownian scaling is a proved finite-dimensional law of the actual source. -/
theorem clockBrownian_isPreBrownian {ι : Type*} (c : ℝ≥0) (hc : c≠0) (i : ι) :
    IsPreBrownianReal (clockBrownian c i) (ULA.CanonicalBrownian.vectorProbability ι) := by
  have hb := (ULA.CanonicalBrownian.coordinate_isPreBrownian i).smul (inv_ne_zero hc)
  change IsPreBrownianReal (fun t ω => Real.sqrt (c:ℝ)*ULA.CanonicalBrownian.coordinate i (c⁻¹*t) ω) _
  simpa only [NNReal.coe_inv,Real.sqrt_inv,inv_inv] using hb

/-- The entire changed-clock coordinate paths remain mutually independent. -/
theorem clockBrownian_paths_independent (ι : Type*) (c : ℝ≥0) :
    iIndepFun (fun i (ω : ULA.CanonicalBrownian.VectorSample ι) t => clockBrownian c i t ω)
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  exact (ULA.CanonicalBrownian.coordinate_paths_independent ι).comp
    (fun _ p t => Real.sqrt (c:ℝ)*p (c⁻¹*t))
    (fun _ => measurable_pi_iff.mpr (fun _ => measurable_const.mul (measurable_pi_apply _)))

/-- A unit-temperature kinetic diffusion at clock c gives exactly temperature 1/c² in physical time. -/
theorem kinetic_clock_noise_amplitude (c γ : ℝ) (hc : 0<c) (hγ : 0≤γ) :
    c⁻¹*Real.sqrt (2*(c*γ))=Real.sqrt (2*γ/c^2)*Real.sqrt c := by
  have he : 2*(c*γ)=(2*γ)*c := by ring
  rw [he,Real.sqrt_mul (by positivity : 0≤2*γ),Real.sqrt_div (by positivity : 0≤2*γ),Real.sqrt_sq hc.le]
  ring

end KineticLangevin
