import KIPLMC.OBABORescaling
import KIPLMC.Moments
import KIPLMC.Target
import KineticLangevin.OBABOBiasScalar
import KineticLangevin.OBABOBias
import KineticLangevin.OBABOPosition

/-! # Particle OBABO sampling bounds from the actual shared sampler -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KIPLMC

/-- Independent thermal initialization becomes independent standard Gaussian
velocity at the paper's transformed clock. -/
theorem obaboThermalInitial_unitTemperature {N dθ dx : ℕ} (hN : 0<N)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] :
    ((velocityTarget N dθ dx).prod ν).map (rescaleVelocity (Real.sqrt N)) =
      (stdGaussian (State N dθ dx)).prod ν := by
  have hp := Measure.map_prod_map (velocityTarget N dθ dx) ν
    (f := fun v ↦ Real.sqrt N • v) (g := id) (by fun_prop) measurable_id
  rw [velocityTarget_unscale hN,Measure.map_id] at hp
  change (((velocityTarget N dθ dx).prod ν).map (fun p ↦ (Real.sqrt N • p.1,p.2))) = _
  simpa only [Prod.map_def,id_eq] using hp.symm

/-- The actual particle position law equals the actual unit-temperature
OBABO position law; initialization is the independent thermal product. -/
theorem kiplmc2PositionLaw_unitTemperature {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) (γ h : ℝ)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] (n : ℕ) :
    (kiplmc2Laws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd =
      (KineticLangevin.obaboLaws (gradient (@IPLA.potential N dθ dx U))
        (Real.sqrt N*γ) (h/Real.sqrt N)
        (Real.sqrt (KineticLangevin.obaboVariance (Real.sqrt N*γ) (h/Real.sqrt N)))
        ((stdGaussian (State N dθ dx)).prod (stdGaussian (State N dθ dx)))
        ((stdGaussian (State N dθ dx)).prod ν) n).map Prod.snd := by
  have hc := kiplmc2Laws_unitTemperature hN U L hdiff hLip γ h
    ((velocityTarget N dθ dx).prod ν) n
  rw [obaboThermalInitial_unitTemperature hN ν] at hc
  have hp := congrArg (fun ρ : Measure (State N dθ dx × State N dθ dx) ↦ ρ.map Prod.snd) hc
  rw [Measure.map_map measurable_snd (by unfold rescaleVelocity; fun_prop)] at hp
  exact hp

/-- The actual contraction rate is invariant under the exact clock change. -/
theorem obaboRate_unitTemperature (c m γ h : ℝ) (hc : c≠0) :
    KineticLangevin.obaboContractionRate (c^2*m) (c*γ) (h/c) =
      KineticLangevin.obaboContractionRate m γ h := by
  apply NNReal.eq
  change Real.sqrt (1-(c^2*m)*(h/c)/(3*(c*γ))) = Real.sqrt (1-m*h/(3*γ))
  congr 2
  field_simp
  <;> ring

/-- Curvature and clock scaling preserve the paper's friction threshold. -/
theorem obaboFriction_unitTemperature (c L γ : ℝ) (h : 4*L≤γ^2) :
    4*(c^2*L)≤(c*γ)^2 := by
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg c)]

/-- The exact clock scaling also preserves the original step-size threshold. -/
theorem obaboStepSize_unitTemperature (c m γ h : ℝ) (hc : c≠0)
    (hs : 33*γ^3*h≤m) : 33*(c*γ)^3*(h/c)≤c^2*m := by
  have he : 33*(c*γ)^3*(h/c)=c^2*(33*γ^3*h) := by field_simp <;> ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hs (sq_nonneg c)

/-- The standard-temperature OBABO bias scales to the intensive particle
radius sqrt(d/N), with all constants kept explicit. -/
theorem obaboBias_unitTemperature (c m L γ h d : ℝ) (hc : 0<c) :
    (6*(c*γ)/(c^2*m))*(h/c)*Real.sqrt d*(4*Real.sqrt (c^2*L)+(c^2*L)*(h/c)/2) =
      (6*γ/m)*h*(Real.sqrt d/c)*(4*Real.sqrt L+L*h/2) := by
  rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc.le]
  field_simp
  <;> ring

/-- An unconditional sampling bound for the actual particle OBABO position
law. The intensive dimension appears by the proved clock/noise conjugacy. -/
theorem kiplmc2_position_sampling_bound {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (m γ h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0<m) (hmL : m≤(L : ℝ))
    (hγ : 0<γ) (hh : 0<h) (hfriction : 4*(L : ℝ)≤γ^2) (hstep : 33*γ^3*h≤m)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hfinite : ULA.wasserstein2 ν (IPLA.gibbsTarget U)≠⊤) (n : ℕ) :
    let ρ := (kiplmc2Laws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd
    ULA.wasserstein2 ρ (IPLA.gibbsTarget U)≠⊤ ∧
      ULA.wasserstein2Real ρ (IPLA.gibbsTarget U) ≤
        Real.sqrt 2*(KineticLangevin.obaboContractionRate m γ h : ℝ)^n*
          ULA.wasserstein2Real ν (IPLA.gibbsTarget U) +
        Real.sqrt 2*((6*γ/m)*h*(Real.sqrt ((dθ : ℝ)+(N : ℝ)*(dx : ℝ))/Real.sqrt N)*
          (4*Real.sqrt (L : ℝ)+(L : ℝ)*h/2)) := by
  intro ρ
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hc : 0<Real.sqrt N := Real.sqrt_pos.2 hn
  have hm' : 0<(N : ℝ)*m := mul_pos hn hm
  have hγ' : 0<Real.sqrt N*γ := mul_pos hc hγ
  have hh' : 0<h/Real.sqrt N := div_pos hh hc
  have hmL' : (N : ℝ)*m≤((N : ℝ≥0)*L : ℝ≥0) := by
    simp only [NNReal.coe_mul,NNReal.coe_natCast]
    exact mul_le_mul_of_nonneg_left hmL hn.le
  have hfric' : 4*(((N : ℝ≥0)*L : ℝ≥0) : ℝ)≤(Real.sqrt N*γ)^2 := by
    simpa only [Real.sq_sqrt hn.le,NNReal.coe_mul,NNReal.coe_natCast] using
      obaboFriction_unitTemperature (Real.sqrt N) L γ hfriction
  have hstep' : 33*(Real.sqrt N*γ)^3*(h/Real.sqrt N)≤(N : ℝ)*m := by
    simpa only [Real.sq_sqrt hn.le] using
      obaboStepSize_unitTemperature (Real.sqrt N) m γ h hc.ne' hstep
  let σ := Real.sqrt (KineticLangevin.obaboVariance (Real.sqrt N*γ) (h/Real.sqrt N))
  have hv : KineticLangevin.obaboDamping (Real.sqrt N*γ) (h/Real.sqrt N)^2+σ^2=1 := by
    rw [show σ^2=KineticLangevin.obaboVariance (Real.sqrt N*γ) (h/Real.sqrt N) from
      Real.sq_sqrt (KineticLangevin.obaboVariance_nonneg hγ'.le hh'.le)]
    unfold KineticLangevin.obaboVariance
    ring
  have hb := KineticLangevin.obabo_position_sampling_bound
    (@IPLA.potential N dθ dx U) ((N : ℝ)*m) (Real.sqrt N*γ) (h/Real.sqrt N) σ ((N : ℝ≥0)*L)
    (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
    (IPLA.potential_gradient_lipschitz hdiff hLip) hm' hmL' hγ' hh' hfric' hstep' hv ν hfinite n
  have hlaw := kiplmc2PositionLaw_unitTemperature hN U L hdiff hLip γ h ν n
  have hrate := obaboRate_unitTemperature (Real.sqrt N) m γ h hc.ne'
  rw [Real.sq_sqrt hn.le] at hrate
  dsimp only at hb
  change ULA.wasserstein2 ρ (IPLA.gibbsTarget U)≠⊤ ∧ _
  dsimp only [ρ]
  rw [hlaw]
  refine ⟨hb.1,?_⟩
  have hcost := hb.2
  rw [hrate] at hcost
  simp only [NNReal.coe_mul,NNReal.coe_natCast,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    Nat.cast_add,Nat.cast_mul] at hcost
  have hcancel := obaboBias_unitTemperature (Real.sqrt N) m L γ h
    ((dθ : ℝ)+(N : ℝ)*(dx : ℝ)) hc
  rw [Real.sq_sqrt hn.le] at hcancel
  apply hcost.trans_eq
  congr 1
  calc
    _ = Real.sqrt 2*((6*(Real.sqrt N*γ)/((N : ℝ)*m))*(h/Real.sqrt N)*
      Real.sqrt ((dθ : ℝ)+(N : ℝ)*(dx : ℝ))*(4*Real.sqrt ((N : ℝ)*(L : ℝ))+
        ((N : ℝ)*(L : ℝ))*(h/Real.sqrt N)/2)) := by ring
    _ = _ := congrArg (fun x : ℝ ↦ Real.sqrt 2*x) hcancel

/-- The unconditional KIPLMC2 parameter error splits into geometric
relaxation, the actual OBABO discretization bias, and sharp MMLE concentration. -/
theorem kiplmc2_parameter_bound {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (m γ h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0<m) (hmL : m≤(L : ℝ))
    (hγ : 0<γ) (hh : 0<h) (hfriction : 4*(L : ℝ)≤γ^2) (hstep : 33*γ^3*h≤m)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) (n : ℕ) :
    Real.sqrt (∫ z,‖IPLA.parameterCLM z-θStar‖^2
      ∂(kiplmc2Laws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd) ≤
        Real.sqrt 2*(KineticLangevin.obaboContractionRate m γ h : ℝ)^n*
          ULA.wasserstein2Real ν (IPLA.gibbsTarget U) +
        Real.sqrt 2*((6*γ/m)*h*(Real.sqrt ((dθ : ℝ)+(N : ℝ)*(dx : ℝ))/Real.sqrt N)*
          (4*Real.sqrt (L : ℝ)+(L : ℝ)*h/2)) +
        Real.sqrt ((dθ : ℝ)/((N : ℝ)*m)) := by
  haveI := IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  have hπ : MemLp (id : State N dθ dx → State N dθ dx) 2 (IPLA.gibbsTarget U) := by
    change MemLp id 2 (ULA.gibbsMeasure (@IPLA.potential N dθ dx U))
    exact ULA.memLp_id_gibbsMeasure _ ((N : ℝ)*m) (by positivity)
      (IPLA.potential_differentiable hdiff) (IPLA.potential_strongConvex hsc)
  have hfinite : ULA.wasserstein2 ν (IPLA.gibbsTarget U)≠⊤ :=
    ULA.wasserstein2_ne_top_of_memLp ν (IPLA.gibbsTarget U) hν hπ
  have hb := kiplmc2_position_sampling_bound hN U m γ h L hdiff hsc hLip hm hmL
    hγ hh hfriction hstep ν hfinite n
  have hc := parameter_concentration hN U m hm hdiff hsc θStar hmax
  have hp := IPLA.projectedRMSReal_le_wasserstein2Real_add
    (@IPLA.parameterCLM N dθ dx) IPLA.norm_parameterCLM_le_one θStar
    _ (Real.sqrt_nonneg _) hb.1 hc
  have hf := IPLA.projectedRMS_ne_top (@IPLA.parameterCLM N dθ dx)
    IPLA.norm_parameterCLM_le_one θStar _ hb.1 hc
  rw [IPLA.projectedRMSReal_eq_sqrt_integral _ _ _ hf] at hp
  exact hp.trans (add_le_add_left hb.2 _)

end KIPLMC