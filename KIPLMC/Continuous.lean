import KIPLMC.KineticClock
import KIPLMC.CanonicalExponential
import KineticLangevin.ContinuousGibbs
import KineticLangevin.TransportMap

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KIPLMC
open KineticLangevin

/-- The exact unit-temperature clock friction of the particle diffusion. -/
def kipldClockFriction (N : ℕ) (γ : ℝ≥0) : ℝ≥0 := ⟨Real.sqrt N * γ, by positivity⟩

/-- The genuine independent Gaussian velocity and vector Brownian source. -/
abbrev kipldBrownianSource (N dθ dx : ℕ) :=
  CanonicalContinuous.probability (Coordinate N dθ dx) (stdGaussian (State N dθ dx))

/-- The selected actual physical-time KIPLD solution; only velocity and time change. -/
def kipldBrownianFlow {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν)
    (T : ℝ) (hT : 0≤T) (t : ℝ) :=
  rescaleVelocity (Real.sqrt N)⁻¹
    (ProductContinuous.flow (kipldBrownianSource N dθ dx) ν hν
      (CanonicalContinuous.velocity (Coordinate N dθ dx) (stdGaussian (State N dθ dx)) IsGaussian.memLp_two_id)
      (CanonicalContinuous.input (Coordinate N dθ dx) (stdGaussian (State N dθ dx)) (kipldClockFriction N γ))
      (CanonicalContinuous.continuous_input _ _ _) (gradient (@IPLA.potential N dθ dx U))
      ((N:ℝ≥0)*L) (kipldClockFriction N γ) (IPLA.potential_gradient_lipschitz hdiff hLip)
      (T/Real.sqrt N) (div_nonneg hT (Real.sqrt_nonneg _)) (t/Real.sqrt N))

/-- The actual physical-time Brownian position law, as the genuine flow's endpoint pushforward. -/
def kipldBrownianPositionLaw {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν)
    (T : ℝ) (hT : 0≤T) : Measure (State N dθ dx) :=
  (ν.prod (kipldBrownianSource N dθ dx)).map (kipldBrownianFlow hN U L γ hdiff hLip ν hν T hT T).2

/-- The physical endpoint is exactly the canonical diffusion endpoint at the transformed clock. -/
theorem kipldBrownianPositionLaw_eq_canonical {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν)
    (T : ℝ) (hT : 0≤T) :
    kipldBrownianPositionLaw hN U L γ hdiff hLip ν hν T hT =
      CanonicalContinuous.positionLaw (Coordinate N dθ dx) (stdGaussian (State N dθ dx))
        IsGaussian.memLp_two_id ν hν (@IPLA.potential N dθ dx U) ((N:ℝ≥0)*L)
        (kipldClockFriction N γ) (IPLA.potential_gradient_lipschitz hdiff hLip)
        (T/Real.sqrt N) (div_nonneg hT (Real.sqrt_nonneg _)) := rfl

/-- The actual initial phase has exactly independent thermal velocity and the supplied position law. -/
theorem kipldBrownianFlow_initial_hasLaw {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν) (T : ℝ) (hT : 0≤T) :
    HasLaw (lpPhaseCoe (ν.prod (kipldBrownianSource N dθ dx))
      (kipldBrownianFlow hN U L γ hdiff hLip ν hν T hT 0))
      ((velocityTarget N dθ dx).prod ν) (ν.prod (kipldBrownianSource N dθ dx)) := by
  let Q := kipldBrownianSource N dθ dx
  let V := CanonicalContinuous.velocity (Coordinate N dθ dx) (stdGaussian (State N dθ dx)) IsGaussian.memLp_two_id
  let Z := ProductContinuous.initial Q ν hν V
  have hj := CanonicalContinuous.initial_ouInput_jointLaw (Coordinate N dθ dx) ν hν 0 (by norm_num) 0
  have hi := (measurePreserving_fst : MeasurePreserving Prod.fst
    (((stdGaussian (State N dθ dx)).prod ν).prod
      (Measure.infinitePi (fun _ : ℕ => ouThermalLaw (E := State N dθ dx) 0 0)))
    ((stdGaussian (State N dθ dx)).prod ν)).hasLaw.comp hj
  have hm : ((stdGaussian (State N dθ dx)).prod ν).map (rescaleVelocity (Real.sqrt N)⁻¹) =
      (velocityTarget N dθ dx).prod ν := by
    have hp := Measure.map_prod_map (stdGaussian (State N dθ dx)) ν
      (f:=fun v => (Real.sqrt N)⁻¹ • v) (g:=id) (by fun_prop) measurable_id
    change ((stdGaussian (State N dθ dx)).prod ν).map
      (Prod.map (fun v => (Real.sqrt N)⁻¹ • v) id) = _
    simpa only [Measure.map_id,velocityTarget] using hp.symm
  have hh : HasLaw (rescaleVelocity (Real.sqrt N)⁻¹) ((velocityTarget N dθ dx).prod ν)
      ((stdGaussian (State N dθ dx)).prod ν) := ⟨(by unfold rescaleVelocity;fun_prop),hm⟩
  have he := hh.comp hi
  have hspec := ProductContinuous.flow_spec Q ν hν V
    (CanonicalContinuous.input (Coordinate N dθ dx) (stdGaussian (State N dθ dx)) (kipldClockFriction N γ))
    (CanonicalContinuous.continuous_input _ _ _) (CanonicalContinuous.input_zero _ _ _)
    (gradient (@IPLA.potential N dθ dx U)) ((N:ℝ≥0)*L) (kipldClockFriction N γ)
    (IPLA.potential_gradient_lipschitz hdiff hLip) (T/Real.sqrt N) (div_nonneg hT (Real.sqrt_nonneg _))
  have hS0 : kipldBrownianFlow hN U L γ hdiff hLip ν hν T hT 0 = rescaleVelocity (Real.sqrt N)⁻¹ Z := by
    unfold kipldBrownianFlow
    rw [zero_div,hspec.2.1]
  apply he.congr
  rw [hS0]
  filter_upwards [Lp.coeFn_smul ((Real.sqrt N)⁻¹) Z.1] with ω hs
  exact Prod.ext (by simpa only [lpPhaseCoe,rescaleVelocity,Function.comp_apply,Pi.smul_apply,Z,V,Q,kipldBrownianSource,CanonicalContinuous.probability] using hs) rfl

/-- Clock rescaling cancels all particle-number factors from the physical decay exponent. -/
theorem kipld_scaled_exponent (N : ℕ) (hN : 0<N) (m γ T : ℝ) :
    (-((N:ℝ)*m)/(Real.sqrt N*γ))*(T/Real.sqrt N)=(-m/γ)*T := by
  have hc : Real.sqrt N≠0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  by_cases hg : γ=0
  · simp [hg]
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  ring

/-- Actual KIPLD converges to the proved stationary Gibbs position law, at the paper's physical-time rate. -/
theorem kipldBrownianPositionLaw_wasserstein_bound {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m≤(L:ℝ)) (hm : 0<m)
    (hγ : 0<(γ:ℝ)) (hfriction : m+(L:ℝ)≤(γ:ℝ)^2)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν) (T : ℝ) (hT : 0≤T) :
    ULA.wasserstein2Real (kipldBrownianPositionLaw hN U L γ hdiff hLip ν hν T hT)
      (IPLA.gibbsTarget U) ≤ Real.sqrt 2*Real.exp ((-m/(γ:ℝ))*T)*
        ULA.wasserstein2Real ν (IPLA.gibbsTarget U) := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have hc : 0<Real.sqrt N := Real.sqrt_pos.2 hn
  have hfr : (N:ℝ)*m+((N:ℝ≥0)*L:ℝ≥0)≤(kipldClockFriction N γ:ℝ)^2 := by
    change (N:ℝ)*m+(N:ℝ)*(L:ℝ)≤(Real.sqrt N*(γ:ℝ))^2
    nlinarith [mul_le_mul_of_nonneg_left hfriction hn.le,Real.sq_sqrt hn.le]
  have hb := CanonicalContinuous.wasserstein2_gibbs (Coordinate N dθ dx) ν hν
    (@IPLA.potential N dθ dx U) ((N:ℝ)*m) ((N:ℝ≥0)*L) (kipldClockFriction N γ)
    (mul_pos hn hm) (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
    (IPLA.potential_gradient_lipschitz hdiff hLip)
    (by simpa using mul_le_mul_of_nonneg_left hmL hn.le)
    (mul_pos hc hγ) hfr (T/Real.sqrt N) (div_nonneg hT hc.le)
  rw [kipldBrownianPositionLaw_eq_canonical,IPLA.gibbsTarget_eq_gibbsMeasure U]
  change ULA.wasserstein2Real _ _ ≤ Real.sqrt 2*Real.exp ((-((N:ℝ)*m)/(Real.sqrt N*(γ:ℝ)))*(T/Real.sqrt N))*ULA.wasserstein2Real ν _ at hb
  rw [kipld_scaled_exponent N hN] at hb
  exact hb

/-- The actual physical-time endpoint law has a finite quadratic moment. -/
theorem kipldBrownianPositionLaw_memLp {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν) (T : ℝ) (hT : 0≤T) :
    MemLp (id : State N dθ dx → State N dθ dx) 2
      (kipldBrownianPositionLaw hN U L γ hdiff hLip ν hν T hT) := by
  exact ProductContinuous.positionLaw_memLp _ ν hν _ _ _ _ _ _ _ _ _

/-- The genuine KIPLD output is a probability measure. -/
theorem kipldBrownianPositionLaw_probability {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν) (T : ℝ) (hT : 0≤T) :
    IsProbabilityMeasure (kipldBrownianPositionLaw hN U L γ hdiff hLip ν hν T hT) := by
  exact ProductContinuous.positionLaw_probability _ ν hν _ _ _ _ _ _ _ _ _

/-- The actual physical-time diffusion-to-target distance is finite. -/
theorem kipldBrownianPositionLaw_wasserstein2_ne_top {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0<m)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν) (T : ℝ) (hT : 0≤T) :
    ULA.wasserstein2 (kipldBrownianPositionLaw hN U L γ hdiff hLip ν hν T hT)
      (IPLA.gibbsTarget U) ≠ ⊤ := by
  letI := IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  letI := kipldBrownianPositionLaw_probability hN U L γ hdiff hLip ν hν T hT
  exact ULA.wasserstein2_ne_top_of_memLp _ _
    (kipldBrownianPositionLaw_memLp hN U L γ hdiff hLip ν hν T hT)
    (ULA.memLp_id_gibbsMeasure (@IPLA.potential N dθ dx U) ((N:ℝ)*m)
      (mul_pos (by exact_mod_cast hN) hm) (IPLA.potential_differentiable hdiff)
      (IPLA.potential_strongConvex hsc))

/-- The lifted sum force transforms to exactly the actual particle force, not a surrogate drift. -/
theorem kipld_lpForce_clock {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {N dθ dx : ℕ} (hN : 0<N) (U : IPLA.Joint dθ dx → ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) :
    (fun X => ((Real.sqrt N)^2)⁻¹ • ULA.lpDrift P (gradient (@IPLA.potential N dθ dx U))
      (IPLA.potential_gradient_lipschitz hdiff hLip) X) =
      ULA.lpDrift P (force U) (force_lipschitz hN hdiff hLip) := by
  funext X
  apply Lp.ext_iff.mpr
  filter_upwards [Lp.coeFn_smul (((Real.sqrt N)^2)⁻¹)
      (ULA.lpDrift P (gradient (@IPLA.potential N dθ dx U)) (IPLA.potential_gradient_lipschitz hdiff hLip) X),
    ULA.lpDrift_coe P (gradient (@IPLA.potential N dθ dx U)) (IPLA.potential_gradient_lipschitz hdiff hLip) X,
    ULA.lpDrift_coe P (force U) (force_lipschitz hN hdiff hLip) X] with ω hs hg hf
  rw [hs]
  simp only [Pi.smul_apply,hg,hf,inverse_sqrt_sq]
  rfl

/-- The constructed Brownian flow satisfies the actual physical KIPLD integral equation in L². -/
theorem kipldBrownianFlow_integral {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν) (T : ℝ) (hT : 0≤T) :
    let P := ν.prod (kipldBrownianSource N dθ dx)
    let S := kipldBrownianFlow hN U L γ hdiff hLip ν hν T hT
    let B := ProductContinuous.input (kipldBrownianSource N dθ dx) ν
      (CanonicalContinuous.input (Coordinate N dθ dx) (stdGaussian (State N dθ dx)) (kipldClockFriction N γ))
    Continuous S ∧ ∀ t ∈ Icc 0 T, S t-S 0 =
      -(∫ s in 0..t,kineticNegativeDrift (ULA.lpDrift P (force U) (force_lipschitz hN hdiff hLip)) γ 1 (S s))+
      ((Real.sqrt N)⁻¹ • B (t/Real.sqrt N),0) := by
  let Q := kipldBrownianSource N dθ dx
  let V := CanonicalContinuous.velocity (Coordinate N dθ dx) (stdGaussian (State N dθ dx)) IsGaussian.memLp_two_id
  let B := CanonicalContinuous.input (Coordinate N dθ dx) (stdGaussian (State N dθ dx)) (kipldClockFriction N γ)
  let g := ULA.lpDrift (ν.prod Q) (gradient (@IPLA.potential N dθ dx U)) (IPLA.potential_gradient_lipschitz hdiff hLip)
  let Y := ProductContinuous.flow Q ν hν V B (CanonicalContinuous.continuous_input _ _ _)
    (gradient (@IPLA.potential N dθ dx U)) ((N:ℝ≥0)*L) (kipldClockFriction N γ)
    (IPLA.potential_gradient_lipschitz hdiff hLip) (T/Real.sqrt N) (div_nonneg hT (Real.sqrt_nonneg _))
  have hspec := ProductContinuous.flow_spec Q ν hν V B (CanonicalContinuous.continuous_input _ _ _)
    (CanonicalContinuous.input_zero _ _ _) (gradient (@IPLA.potential N dθ dx U))
    ((N:ℝ≥0)*L) (kipldClockFriction N γ) (IPLA.potential_gradient_lipschitz hdiff hLip)
    (T/Real.sqrt N) (div_nonneg hT (Real.sqrt_nonneg _))
  have hc : 0<Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have he := kinetic_integral_clock g
    (ULA.lpDrift_lipschitz _ _ (IPLA.potential_gradient_lipschitz hdiff hLip)).continuous
    (Real.sqrt N) γ T hc (Y 0) (ProductContinuous.input Q ν B) Y hspec.1 hspec.2.2
  rw [kipld_lpForce_clock (ν.prod Q) hN U L hdiff hLip] at he
  refine ⟨?_,?_⟩
  · change Continuous (fun t => velocityScaleLinear (Real.sqrt N)⁻¹ (Y (t/Real.sqrt N)))
    exact (velocityScaleLinear (Real.sqrt N)⁻¹).continuous.comp (hspec.1.comp (continuous_id.div_const _))
  · simpa only [kipldBrownianFlow,zero_div] using he

/-- The printed KIPLD parameter-marginal convergence theorem, with its explicit independent initial coupling. -/
theorem kipld_parameter_sampling_bound {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m≤(L:ℝ)) (hm : 0<m)
    (hγ : 0<(γ:ℝ)) (hfriction : m+(L:ℝ)≤(γ:ℝ)^2)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν) (T : ℝ) (hT : 0≤T) :
    ULA.wasserstein2Real
      ((kipldBrownianPositionLaw hN U L γ hdiff hLip ν hν T hT).map IPLA.parameterCLM)
      (IPLA.marginalTarget N U) ≤ Real.sqrt 2*Real.exp ((-m/(γ:ℝ))*T)*
        Real.sqrt (∫ p : State N dθ dx×State N dθ dx, ‖p.1-p.2‖^2 ∂ν.prod (IPLA.gibbsTarget U)) := by
  letI := IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  letI := kipldBrownianPositionLaw_probability hN U L γ hdiff hLip ν hν T hT
  have hf := kipldBrownianPositionLaw_wasserstein2_ne_top hN U m L γ hdiff hsc hLip hm ν hν T hT
  have hp := wasserstein2Real_map_lipschitz (@IPLA.parameterCLM N dθ dx)
    IPLA.parameterCLM.continuous.measurable 1
    (fun x y => by simpa only [NNReal.coe_one,one_mul,← map_sub] using IPLA.norm_parameterCLM_apply_le (x-y))
    (kipldBrownianPositionLaw hN U L γ hdiff hLip ν hν T hT) (IPLA.gibbsTarget U) hf
  rw [IPLA.gibbsTarget_parameter_marginal hN U m hm hdiff hsc,NNReal.coe_one,one_mul] at hp
  have hb := kipldBrownianPositionLaw_wasserstein_bound hN U m L γ hdiff hsc hLip hmL hm hγ hfriction ν hν T hT
  have hπ := ULA.memLp_id_gibbsMeasure (@IPLA.potential N dθ dx U) ((N:ℝ)*m)
    (mul_pos (by exact_mod_cast hN) hm) (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
  exact hp.trans (hb.trans (mul_le_mul_of_nonneg_left
    (independent_initial_wasserstein_bound ν (IPLA.gibbsTarget U) hν hπ) (by positivity)))

/-- Actual KIPLD parameter RMS error adds only the sharp statistical concentration term. -/
theorem kipld_parameter_RMS_bound {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m≤(L:ℝ)) (hm : 0<m)
    (hγ : 0<(γ:ℝ)) (hfriction : m+(L:ℝ)≤(γ:ℝ)^2)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν) (T : ℝ) (hT : 0≤T)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z-θStar‖^2
      ∂kipldBrownianPositionLaw hN U L γ hdiff hLip ν hν T hT) ≤
      Real.sqrt 2*Real.exp ((-m/(γ:ℝ))*T)*ULA.wasserstein2Real ν (IPLA.gibbsTarget U)+
      Real.sqrt ((dθ:ℝ)/((N:ℝ)*m)) := by
  have hb := kipldBrownianPositionLaw_wasserstein_bound hN U m L γ hdiff hsc hLip hmL hm hγ hfriction ν hν T hT
  have hf := kipldBrownianPositionLaw_wasserstein2_ne_top hN U m L γ hdiff hsc hLip hm ν hν T hT
  have hc := parameter_concentration hN U m hm hdiff hsc θStar hmax
  have hp := IPLA.projectedRMSReal_le_wasserstein2Real_add
    (@IPLA.parameterCLM N dθ dx) IPLA.norm_parameterCLM_le_one θStar
    _ (Real.sqrt_nonneg _) hf hc
  have hfin := IPLA.projectedRMS_ne_top (@IPLA.parameterCLM N dθ dx)
    IPLA.norm_parameterCLM_le_one θStar _ hf hc
  rw [IPLA.projectedRMSReal_eq_sqrt_integral _ _ _ hfin] at hp
  exact hp.trans (add_le_add_left hb _)

end KIPLMC
