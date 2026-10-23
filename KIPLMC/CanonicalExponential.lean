import KIPLMC.ExponentialRescaling
import KIPLMC.ReferenceBound
import KineticLangevin.ProductMarkovLaw
import KineticLangevin.GenericCanonicalKLMC

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KIPLMC
open KineticLangevin

/-- On the actual particle coordinate set, the canonical KLMC law equals its actual Gaussian Markov position law. -/
theorem canonicalKLMC_eq_gaussianPositionLaw {N dθ dx : ℕ}
    (f : State N dθ dx→ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (γ : ℝ) (h : ℝ≥0) (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] (n : ℕ) :
    GenericCanonicalCoupling.klmcLaw f γ h ν n =
      (ULA.markovLaws (klmcStep (gradient f) γ h) (exponentialNoise N dθ dx γ h)
        ((stdGaussian (State N dθ dx)).prod ν) n).map Prod.snd := by
  exact productKLMCLaw_eq_markovLaws
    (ULA.CanonicalBrownian.vectorProbability (Coordinate N dθ dx)) (stdGaussian (State N dθ dx)) ν
    f M hLip γ h (exponentialNoise N dθ dx γ h)
    (fun ω n ↦ GenericCanonicalSource.canonicalKLMCInnovation (Coordinate N dθ dx) γ h n ω)
    (measurable_pi_iff.mpr (GenericCanonicalSource.measurable_canonicalKLMCInnovation _ γ h))
    (GenericCanonicalSource.canonicalKLMCInnovation_streamLaw _ γ h) n

/-- The physical-time particle output is the actual canonical kinetic output at the transformed clock. -/
theorem kiplmc1GaussianPositionLaws_eq_canonical {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx→ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (γ : ℝ) (h : ℝ≥0) (hγ : 0≤γ)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] (n : ℕ) :
    (kiplmc1GaussianLaws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd =
      GenericCanonicalCoupling.klmcLaw (@IPLA.potential N dθ dx U) (Real.sqrt N*γ)
        ⟨(h:ℝ)/Real.sqrt N,div_nonneg h.coe_nonneg (Real.sqrt_nonneg _)⟩ ν n := by
  rw [canonicalKLMC_eq_gaussianPositionLaw _ ((N:ℝ≥0)*L)
    (IPLA.potential_gradient_lipschitz hdiff hLip)]
  exact kiplmc1GaussianPositionLaws_unitTemperature hN U L hdiff hLip γ h hγ h.coe_nonneg ν n

/-- Curvature, friction and step assumptions transform with precisely matching powers of particle count. -/
theorem kiplmc1_scaled_conditions (N : ℕ) (hN : 0<N) (m : ℝ) (L γ h : ℝ≥0)
    (hm : 0<m) (hmL : m≤(L:ℝ)) (hγ : 0<(γ:ℝ))
    (hfriction : m+(L:ℝ)≤(γ:ℝ)^2) (hh : 0<(h:ℝ))
    (hstep : 4*(γ:ℝ)*(L:ℝ)*(h:ℝ)≤m) :
    0<(N:ℝ)*m ∧ (N:ℝ)*m≤((N:ℝ≥0)*L:ℝ≥0) ∧
    0<Real.sqrt N*(γ:ℝ) ∧
    (N:ℝ)*m+((N:ℝ≥0)*L:ℝ≥0)≤(Real.sqrt N*(γ:ℝ))^2 ∧
    0<(h:ℝ)/Real.sqrt N ∧
    4*(Real.sqrt N*(γ:ℝ))*((N:ℝ≥0)*L:ℝ≥0)*((h:ℝ)/Real.sqrt N)≤(N:ℝ)*m := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have hc : 0<Real.sqrt N := Real.sqrt_pos.2 hn
  simp only [NNReal.coe_mul,NNReal.coe_natCast]
  refine ⟨mul_pos hn hm,mul_le_mul_of_nonneg_left hmL hn.le,mul_pos hc hγ,?_,div_pos hh hc,?_⟩
  · have hs := mul_le_mul_of_nonneg_left hfriction hn.le
    nlinarith [Real.sq_sqrt hn.le]
  · have he : 4*(Real.sqrt N*(γ:ℝ))*((N:ℝ)*(L:ℝ))*((h:ℝ)/Real.sqrt N) =
        (N:ℝ)*(4*(γ:ℝ)*(L:ℝ)*(h:ℝ)) := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hstep hn.le

/-- The exponential rate is unchanged in physical time. -/
theorem kiplmc1_scaled_rate (N : ℕ) (hN : 0<N) (m γ h : ℝ) :
    1-3*((N:ℝ)*m)*(h/Real.sqrt N)/(4*(Real.sqrt N*γ))=1-3*m*h/(4*γ) := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.2 hN.ne'
  have hc : Real.sqrt N≠0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  by_cases hγ : γ=0
  · simp [hγ]
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  ring

/-- The shared kinetic bias becomes the exact thermal particle dimension factor. -/
theorem kiplmc1_scaled_bias (N dθ dx : ℕ) (hN : 0<N) (m L h : ℝ) :
    ((N:ℝ)*L)*(h/Real.sqrt N)*Real.sqrt (2*((dθ:ℝ)+(N:ℝ)*(dx:ℝ)))/((N:ℝ)*m) =
      L*h*(Real.sqrt 2*Real.sqrt (((dθ:ℝ)+(N:ℝ)*(dx:ℝ))/(N:ℝ)))/m := by
  have hn : (N:ℝ)≠0 := Nat.cast_ne_zero.2 hN.ne'
  have hc : Real.sqrt N≠0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  by_cases hm : m=0
  · simp [hm]
  field_simp


/-- The actual KIPLMC1 output has finite quadratic transport distance from its true target. -/
theorem kiplmc1GaussianPositionLaws_wasserstein2_ne_top {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx→ℝ) (m : ℝ) (hm : 0<m) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (h : ℝ≥0)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] (hν : MemLp (id : State N dθ dx→State N dθ dx) 2 ν)
    (n : ℕ) :
    ULA.wasserstein2 ((kiplmc1GaussianLaws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd)
      (IPLA.gibbsTarget U)≠⊤ := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have hdiff' := IPLA.potential_differentiable (N:=N) hdiff
  have hsc' := IPLA.potential_strongConvex (N:=N) hsc
  have hLip' := IPLA.potential_gradient_lipschitz (N:=N) hdiff hLip
  have hπ := ULA.memLp_id_gibbsMeasure (@IPLA.potential N dθ dx U) ((N:ℝ)*m) (mul_pos hn hm) hdiff' hsc'
  letI := IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  have hfinite := ULA.wasserstein2_ne_top_of_memLp ν (IPLA.gibbsTarget U) hν hπ
  let γ' : ℝ≥0 := ⟨Real.sqrt N*(γ:ℝ),by positivity⟩
  let h' : ℝ≥0 := ⟨(h:ℝ)/Real.sqrt N,by positivity⟩
  have hglobal := fun (c : ULA.Coupling ν (ULA.gibbsMeasure (@IPLA.potential N dθ dx U))) ↦ GenericCanonicalCoupling.globalReferenceFlow_stationary
    (@IPLA.potential N dθ dx U) ((N:ℝ)*m) (mul_pos hn hm) ((N:ℝ≥0)*L) γ' hdiff' hsc' hLip' c hπ
  have ho := GenericCanonicalCoupling.klmcLaw_wasserstein2_ne_top hπ
    (@IPLA.potential N dθ dx U) ((N:ℝ≥0)*L) γ' hLip' h' hfinite hglobal n
  rw [kiplmc1GaussianPositionLaws_eq_canonical hN U L hdiff hLip γ h γ.coe_nonneg ν n]
  exact ho

/-- The shared unit-temperature KLMC theorem gives the physical-time particle Wasserstein estimate. -/
theorem kiplmc1GaussianPositionLaws_wasserstein_bound {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx→ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m≤(L:ℝ)) (hm : 0<m)
    (hγ : 0<(γ:ℝ)) (hfriction : m+(L:ℝ)≤(γ:ℝ)^2)
    (h : ℝ≥0) (hh : 0<(h:ℝ)) (hstep : 4*(γ:ℝ)*(L:ℝ)*(h:ℝ)≤m)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] (hν : MemLp (id : State N dθ dx→State N dθ dx) 2 ν)
    (n : ℕ) :
    ULA.wasserstein2Real ((kiplmc1GaussianLaws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd)
      (IPLA.gibbsTarget U) ≤
      Real.sqrt 2*(1-3*m*(h:ℝ)/(4*(γ:ℝ)))^n*ULA.wasserstein2Real ν (IPLA.gibbsTarget U)+
      (L:ℝ)*(h:ℝ)*(Real.sqrt 2*Real.sqrt (((dθ:ℝ)+(N:ℝ)*(dx:ℝ))/(N:ℝ)))/m := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have hdiff' := IPLA.potential_differentiable (N:=N) hdiff
  have hsc' := IPLA.potential_strongConvex (N:=N) hsc
  have hLip' := IPLA.potential_gradient_lipschitz (N:=N) hdiff hLip
  have hπ := ULA.memLp_id_gibbsMeasure (@IPLA.potential N dθ dx U) ((N:ℝ)*m) (mul_pos hn hm) hdiff' hsc'
  letI := IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  have hfinite := ULA.wasserstein2_ne_top_of_memLp ν (IPLA.gibbsTarget U) hν hπ
  let γ' : ℝ≥0 := ⟨Real.sqrt N*(γ:ℝ),by positivity⟩
  let h' : ℝ≥0 := ⟨(h:ℝ)/Real.sqrt N,by positivity⟩
  obtain ⟨hm',hmL',hγ',hfriction',hh',hstep'⟩ := kiplmc1_scaled_conditions N hN m L γ h hm hmL hγ hfriction hh hstep
  have hb := GenericCanonicalCoupling.klmc_wasserstein_bound (@IPLA.potential N dθ dx U) ((N:ℝ)*m)
    ((N:ℝ≥0)*L) γ' hdiff' hsc' hLip' hmL' hm' hγ' hfriction' h' hh' hstep' hfinite n
  rw [kiplmc1GaussianPositionLaws_eq_canonical hN U L hdiff hLip γ h γ.coe_nonneg ν n]
  change ULA.wasserstein2Real (GenericCanonicalCoupling.klmcLaw (@IPLA.potential N dθ dx U) γ' h' ν n)
    (ULA.gibbsMeasure (@IPLA.potential N dθ dx U))≤_
  have heγ : (γ':ℝ)=Real.sqrt N*(γ:ℝ) := rfl
  have heh : (h':ℝ)=(h:ℝ)/Real.sqrt N := rfl
  rw [IPLA.gibbsTarget_eq_gibbsMeasure U]
  simpa only [heγ,heh,NNReal.coe_mul,NNReal.coe_natCast,Fintype.card_sum,
    Fintype.card_fin,Fintype.card_prod,Nat.cast_add,Nat.cast_mul,kiplmc1_scaled_rate N hN,
    kiplmc1_scaled_bias N dθ dx hN] using hb

/-- The unconditional KIPLMC1 parameter RMS theorem for the actual correlated-Gaussian sampler. -/
theorem kiplmc1_parameter_bound {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx→ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m≤(L:ℝ)) (hm : 0<m)
    (hγ : 0<(γ:ℝ)) (hfriction : m+(L:ℝ)≤(γ:ℝ)^2)
    (h : ℝ≥0) (hh : 0<(h:ℝ)) (hstep : 4*(γ:ℝ)*(L:ℝ)*(h:ℝ)≤m)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] (hν : MemLp (id : State N dθ dx→State N dθ dx) 2 ν)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z-θStar‖^2
      ∂(kiplmc1GaussianLaws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd) ≤
      Real.sqrt 2*(1-3*m*(h:ℝ)/(4*(γ:ℝ)))^n*ULA.wasserstein2Real ν (IPLA.gibbsTarget U)+
      (L:ℝ)*(h:ℝ)*(Real.sqrt 2*Real.sqrt (((dθ:ℝ)+(N:ℝ)*(dx:ℝ))/(N:ℝ)))/m+
      Real.sqrt ((dθ:ℝ)/((N:ℝ)*m)) := by
  have hb := kiplmc1GaussianPositionLaws_wasserstein_bound hN U m L γ hdiff hsc hLip hmL hm hγ hfriction
    h hh hstep ν hν n
  have hfinite := kiplmc1GaussianPositionLaws_wasserstein2_ne_top hN U m hm L γ hdiff hsc hLip h ν hν n
  have hc := parameter_concentration hN U m hm hdiff hsc θStar hmax
  have hp := IPLA.projectedRMSReal_le_wasserstein2Real_add
    (@IPLA.parameterCLM N dθ dx) IPLA.norm_parameterCLM_le_one θStar
    _ (Real.sqrt_nonneg _) hfinite hc
  have hf := IPLA.projectedRMS_ne_top (@IPLA.parameterCLM N dθ dx)
    IPLA.norm_parameterCLM_le_one θStar _ hfinite hc
  rw [IPLA.projectedRMSReal_eq_sqrt_integral _ _ _ hf] at hp
  exact hp.trans (add_le_add_left hb _)


/-- The printed initial constant uses a genuine independent coupling and dominates the true transport distance. -/
theorem independent_initial_wasserstein_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν π : Measure E) [IsProbabilityMeasure ν] [IsProbabilityMeasure π]
    (hν : MemLp (id : E→E) 2 ν) (hπ : MemLp (id : E→E) 2 π) :
    ULA.wasserstein2Real ν π ≤ Real.sqrt (∫ p : E×E, ‖p.1-p.2‖^2 ∂ν.prod π) := by
  have hmem : MemLp (fun p : E×E ↦ p.1-p.2) 2 (ν.prod π) :=
    (hν.comp_measurePreserving measurePreserving_fst).sub
      (hπ.comp_measurePreserving measurePreserving_snd)
  have hb := ULA.wasserstein2_le_random_cost_real (ν.prod π) Prod.fst Prod.snd
    measurable_fst measurable_snd hmem
  simp only [Measure.map_fst_prod,Measure.map_snd_prod,measure_univ,one_smul] at hb
  have heq := hmem.eLpNorm_eq_integral_rpow_norm (by norm_num : (2:ℝ≥0∞)≠0)
    (by norm_num : (2:ℝ≥0∞)≠⊤)
  have heq' : eLpNorm (fun p : E×E ↦ p.1-p.2) 2 (ν.prod π) =
      ENNReal.ofReal (Real.sqrt (∫ p : E×E, ‖p.1-p.2‖^2 ∂ν.prod π)) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.sqrt_eq_rpow,one_div] using heq
  rw [heq',ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hb
  exact hb

/-- Under the stated kinetic restrictions, the actual physical-time geometric rate is nonnegative. -/
theorem kiplmc1_rate_nonneg (m : ℝ) (L γ : ℝ≥0) (hmL : m≤(L:ℝ)) (hm : 0<m)
    (hγ : 0<(γ:ℝ)) (hfriction : m+(L:ℝ)≤(γ:ℝ)^2)
    (h : ℝ≥0) (hstep : 4*(γ:ℝ)*(L:ℝ)*(h:ℝ)≤m) :
    0≤1-3*m*(h:ℝ)/(4*(γ:ℝ)) := by
  obtain ⟨hc,hs⟩ := KineticLangevin.kinetic_scalar_conditions m L γ h hm hmL hγ hfriction h.coe_nonneg hstep
  have hcoeff := KineticLangevin.firstOrder_coefficient_bound (m/(γ:ℝ)) L h (div_nonneg hm.le hγ.le)
    L.coe_nonneg h.coe_nonneg hc hs
  have he := Real.exp_pos (-(m/(γ:ℝ))*(h:ℝ))
  have hp : 0≤(3/4:ℝ)*(L:ℝ)*(h:ℝ)^2 := by positivity
  have hid : 1-3*m*(h:ℝ)/(4*(γ:ℝ))=1-(3/4:ℝ)*(m/(γ:ℝ))*(h:ℝ) := by ring
  rw [hid]
  linarith

/-- The paper’s printed KIPLMC1 theorem, including its independent initial-position coupling constant. -/
theorem kiplmc1_parameter_bound_independent {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx→ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m≤(L:ℝ)) (hm : 0<m)
    (hγ : 0<(γ:ℝ)) (hfriction : m+(L:ℝ)≤(γ:ℝ)^2)
    (h : ℝ≥0) (hh : 0<(h:ℝ)) (hstep : 4*(γ:ℝ)*(L:ℝ)*(h:ℝ)≤m)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] (hν : MemLp (id : State N dθ dx→State N dθ dx) 2 ν)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z-θStar‖^2
      ∂(kiplmc1GaussianLaws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd) ≤
      Real.sqrt 2*(1-3*m*(h:ℝ)/(4*(γ:ℝ)))^n*
        Real.sqrt (∫ p : State N dθ dx×State N dθ dx, ‖p.1-p.2‖^2 ∂ν.prod (IPLA.gibbsTarget U))+
      (L:ℝ)*(h:ℝ)*(Real.sqrt 2*Real.sqrt (((dθ:ℝ)+(N:ℝ)*(dx:ℝ))/(N:ℝ)))/m+
      Real.sqrt ((dθ:ℝ)/((N:ℝ)*m)) := by
  letI := IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  have hπ := ULA.memLp_id_gibbsMeasure (@IPLA.potential N dθ dx U) ((N:ℝ)*m) (mul_pos hn hm)
    (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
  have hw := independent_initial_wasserstein_bound ν (IPLA.gibbsTarget U) hν hπ
  have hq := kiplmc1_rate_nonneg m L γ hmL hm hγ hfriction h hstep
  have hc := mul_le_mul_of_nonneg_left hw
    (mul_nonneg (Real.sqrt_nonneg 2) (pow_nonneg hq n))
  have hb := kiplmc1_parameter_bound hN U m L γ hdiff hsc hLip hmL hm hγ hfriction
    h hh hstep ν hν θStar hmax n
  exact hb.trans (add_le_add (add_le_add hc le_rfl) le_rfl)

end KIPLMC
