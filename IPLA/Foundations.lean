import IPLA.Model
import UnadjustedLangevin.Gibbs
import UnadjustedLangevin.GibbsScore
import UnadjustedLangevin.TransportMoments

set_option linter.style.header false

/-! # Derived foundational facts for the IPLA target

The joint assumptions on `U(θ,x)` imply normalization and finite moments for
the actual lifted Gibbs measure. Finite initial W₂ then implies finite initial
second moment. Neither normalization nor moments are separate hypotheses.

These are direct applications of the shared ULA Gibbs and transport-moment
theorems to the lifted potential. Brownian construction and stationarity stay
in ULA and enter the final theorem through its Gaussian ULA estimate.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace IPLA

/-- IPLA's target is exactly the general normalized Gibbs density. -/
theorem gibbsTarget_eq_gibbsMeasure {N dθ dx : ℕ} (U : Joint dθ dx → ℝ) :
    @gibbsTarget N dθ dx U = ULA.gibbsMeasure (@potential N dθ dx U) := rfl

/-- Normalization of the lifted target follows from strong convexity of the
original joint potential; no separate Gibbs normalization hypothesis. -/
theorem gibbsTarget_isProbability {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    IsProbabilityMeasure (@gibbsTarget N dθ dx U) := by
  rw [gibbsTarget_eq_gibbsMeasure]
  apply ULA.isProbabilityMeasure_gibbsMeasure (potential U) ((N : ℝ) * m)
    (mul_pos (by exact_mod_cast hN) hm)
    (potential_differentiable hdiff) (potential_strongConvex hsc)

/-- The lifted target has a finite second moment from the original joint
strong-convexity assumption. Gradient Lipschitz continuity is not needed. -/
theorem gibbsTarget_memLp {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    MemLp (fun z : State N dθ dx ↦ z) 2 (gibbsTarget U) := by
  rw [gibbsTarget_eq_gibbsMeasure]
  exact ULA.memLp_id_gibbsMeasure (potential U) ((N : ℝ) * m)
    (mul_pos (by exact_mod_cast hN) hm)
    (potential_differentiable hdiff) (potential_strongConvex hsc)

/-- An actual measurable initialization at finite W₂ from the lifted Gibbs
measure automatically belongs to L². This justifies the L² representation used
by the main analytic theorem without an independent moment assumption. -/
theorem initial_memLp_of_finite_transport
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N dθ dx : ℕ} (hN : 0 < N) (U : Joint dθ dx → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (initial : Ω → State N dθ dx) (hinit : AEMeasurable initial P)
    (hfinite : ULA.wasserstein2 (P.map initial) (gibbsTarget U) ≠ ⊤) :
    MemLp initial 2 P :=
  ULA.memLp_of_wasserstein2_map_ne_top P initial hinit (gibbsTarget U) hfinite
    (gibbsTarget_memLp hN U m hm hdiff hsc)

/-- The lifted Gibbs score moment also follows from the original joint
potential assumptions; no separate score hypothesis or Hessian is introduced. -/
theorem gibbsTarget_score_moment {N dθ dx : ℕ} (hN : 0 < N)
    (U : Joint dθ dx → ℝ) (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U)) :
    (∫ z : State N dθ dx, ‖gradient (potential U) z‖ ^ 2 ∂gibbsTarget U) ≤
      ((N : ℝ) * (L : ℝ)) * ((dθ + N * dx : ℕ) : ℝ) := by
  rw [gibbsTarget_eq_gibbsMeasure]
  have hb := ULA.integral_norm_sq_gradient_gibbs_le_of_strongConvex
    (@potential N dθ dx U) ((N : ℝ) * m) ((N : ℝ≥0) * L)
    (mul_pos (by exact_mod_cast hN) hm)
    (potential_differentiable hdiff) (potential_strongConvex hsc)
    (potential_gradient_lipschitz hdiff hLip)
  simpa only [finrank_state, NNReal.coe_mul, NNReal.coe_natCast] using hb

end IPLA
