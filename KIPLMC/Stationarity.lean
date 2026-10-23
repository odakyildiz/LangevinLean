import KIPLMC.Continuous

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KIPLMC
open KineticLangevin

/-- The actual full physical KIPLD phase flow preserves its normalized Gaussian-times-Gibbs target. -/
theorem kipldBrownianFlow_stationary {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx→ℝ) (m : ℝ) (hm : 0<m) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (T : ℝ) (hT : 0≤T) :
    letI := ULA.isProbabilityMeasure_gibbsMeasure (@IPLA.potential N dθ dx U) ((N:ℝ)*m)
      (mul_pos (by exact_mod_cast hN) hm) (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
    let π := ULA.gibbsMeasure (@IPLA.potential N dθ dx U)
    let hπ := ULA.memLp_id_gibbsMeasure (@IPLA.potential N dθ dx U) ((N:ℝ)*m)
      (mul_pos (by exact_mod_cast hN) hm) (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
    HasLaw (lpPhaseCoe (π.prod (kipldBrownianSource N dθ dx))
      (kipldBrownianFlow hN U L γ hdiff hLip π hπ T hT T)) (gibbsPhaseTarget U)
      (π.prod (kipldBrownianSource N dθ dx)) := by
  letI := ULA.isProbabilityMeasure_gibbsMeasure (@IPLA.potential N dθ dx U) ((N:ℝ)*m)
    (mul_pos (by exact_mod_cast hN) hm) (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
  let π := ULA.gibbsMeasure (@IPLA.potential N dθ dx U)
  let hπ := ULA.memLp_id_gibbsMeasure (@IPLA.potential N dθ dx U) ((N:ℝ)*m)
    (mul_pos (by exact_mod_cast hN) hm) (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
  let Q := kipldBrownianSource N dθ dx
  let Y := ProductContinuous.flow Q π hπ
    (CanonicalContinuous.velocity (Coordinate N dθ dx) (stdGaussian (State N dθ dx)) IsGaussian.memLp_two_id)
    (CanonicalContinuous.input (Coordinate N dθ dx) (stdGaussian (State N dθ dx)) (kipldClockFriction N γ))
    (CanonicalContinuous.continuous_input _ _ _) (gradient (@IPLA.potential N dθ dx U))
    ((N:ℝ≥0)*L) (kipldClockFriction N γ) (IPLA.potential_gradient_lipschitz hdiff hLip)
    (T/Real.sqrt N) (div_nonneg hT (Real.sqrt_nonneg _))
  have hl := CanonicalContinuous.phaseFlow_gibbs_stationary (Coordinate N dθ dx)
    (@IPLA.potential N dθ dx U) ((N:ℝ)*m) (mul_pos (by exact_mod_cast hN) hm)
    ((N:ℝ≥0)*L) (kipldClockFriction N γ) (IPLA.potential_differentiable hdiff)
    (IPLA.potential_strongConvex hsc) (IPLA.potential_gradient_lipschitz hdiff hLip)
    (T/Real.sqrt N) (div_nonneg hT (Real.sqrt_nonneg _))
  have hmarg : (kineticGibbsTarget (@IPLA.potential N dθ dx U)).map (rescaleVelocity (Real.sqrt N)⁻¹)=
      gibbsPhaseTarget U := by
    rw [gibbsPhaseTarget,IPLA.gibbsTarget_eq_gibbsMeasure U]
    have hp := Measure.map_prod_map (stdGaussian (State N dθ dx)) π
      (f:=fun v => (Real.sqrt N)⁻¹ • v) (g:=id) (by fun_prop) measurable_id
    change ((stdGaussian (State N dθ dx)).prod π).map (Prod.map (fun v => (Real.sqrt N)⁻¹ • v) id)=_
    simpa only [Measure.map_id,velocityTarget] using hp.symm
  have hmap : HasLaw (rescaleVelocity (Real.sqrt N)⁻¹) (gibbsPhaseTarget U)
      (kineticGibbsTarget (@IPLA.potential N dθ dx U)) := ⟨(by unfold rescaleVelocity;fun_prop),hmarg⟩
  apply (hmap.comp hl).congr
  filter_upwards [Lp.coeFn_smul ((Real.sqrt N)⁻¹) (Y (T/Real.sqrt N)).1] with ω hs
  exact Prod.ext (by simpa only [kipldBrownianFlow,lpPhaseCoe,rescaleVelocity,Function.comp_apply,Pi.smul_apply,Y,Q,
    kipldBrownianSource,CanonicalContinuous.probability] using hs) rfl

end KIPLMC
