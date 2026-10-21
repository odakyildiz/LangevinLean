import UnadjustedLangevin.BrownianReference
import UnadjustedLangevin.PotentialAssumptions

set_option linter.style.header false

/-! # Dalalyan with a constructed Brownian reference

All integral-equation, continuity and moment fields are discharged. Scalar
Brownian-coordinate laws suffice for these estimates; cross-coordinate and
initial-state independence are not asserted by this auxiliary endpoint. The
remaining stationarity assumption is displayed explicitly: the constructed
solution has not yet been proved to preserve the Gibbs law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace ULA.Hilbert

/-- An analytic ULA endpoint for the supplied Brownian-coordinate noise:
no supplied reference structure, score bound,
noise bound, integral equation, or separate `m ≤ L` assumption. The full
stationarity theorem remains the explicit `hstationary` premise. -/
theorem dalalyan_of_constructed_brownian_reference
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : EuclideanSpace ℝ ι → ℝ) (m h : ℝ) (L : ℝ≥0)
    (hm : 0 < m) (hdiff : Differentiable ℝ U)
    (hsc : StrongConvexOn Set.univ m U) (hLip : LipschitzWith L (gradient U))
    (hh : 0 < h) (hsmall : h ≤ 2 / (m + (L : ℝ)))
    (initial referenceInitial : Lp (EuclideanSpace ℝ ι) 2 P)
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (hstationary : ∀ n t, t ∈ Icc 0 h →
      P.map (brownianSegments P U L hLip W hW h hh.le referenceInitial n t) =
        ULA.gibbsMeasure U) (k : ℕ) :
    ULA.wasserstein2Real
      (P.map (lpChain P U h hLip initial (brownianEulerNoise P W hW h) k))
      (ULA.gibbsMeasure U) ≤
      (1 - m * h) ^ k * ‖initial - referenceInitial‖ +
        (33 / 20 : ℝ) * ((L : ℝ) / m) * Real.sqrt (h * (Fintype.card ι : ℝ)) := by
  have hb := dalalyan_small_step_of_integral_reference P (Fintype.card ι)
    U m h L hdiff hsc hLip hm (ULA.strongConvex_le_lipschitz hdiff hsc hLip)
    hh hsmall initial (brownianEulerNoise P W hW h) (ULA.gibbsMeasure U)
    (brownianReference_of_strongConvex P U m L hm hdiff hsc hLip W hW h hh
      referenceInitial hstationary) k
  simpa only [brownianReference_of_strongConvex, brownianReference,
    brownianSegments_initial] using hb

end ULA.Hilbert
