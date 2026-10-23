import KIPLMC.Rescaling
import KIPLMC.Laws
import KIPLMC.Target
import KIPLMC.Moments
import KineticLangevin.OBABOLaw
import KineticLangevin.Gaussian

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal RealInnerProductSpace
namespace KIPLMC
open KineticLangevin

/-- The scalar Brownian clock changes a two-component kinetic block diagonally. -/
def kineticBlockScale (c : ℝ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal (fun i : Fin 2 ↦ (Real.sqrt c*c^(i:ℕ))⁻¹))

@[simp] theorem kineticBlockScale_apply (c : ℝ) (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    kineticBlockScale c z i = (Real.sqrt c*c^(i:ℕ))⁻¹*z i := by
  simp [kineticBlockScale,Matrix.ofLp_toEuclideanCLM,Matrix.mulVec_diagonal]

theorem klmcKernels_apply (γ t : ℝ) (i : Fin 2) : klmcKernels γ i t=psi γ (i:ℕ) t := by
  fin_cases i <;> rfl

/-- Both covariance powers follow from the same change of Brownian clock. -/
theorem klmcCovariance_clock (c γ h : ℝ) (hc : 0<c) (i j : Fin 2) :
    klmcCovariance (c*γ) (h/c) i j =
      (Real.sqrt c*c^(i:ℕ))⁻¹ * (Real.sqrt c*c^(j:ℕ))⁻¹ * klmcCovariance γ h i j := by
  have hcn : c≠0 := hc.ne'
  have hsn : Real.sqrt c≠0 := (Real.sqrt_pos.2 hc).ne'
  have hss := Real.sq_sqrt hc.le
  simp only [klmcCovariance,gramCovariance,klmcKernels_apply]
  simp_rw [psi_scale c γ _ hcn]
  simp_rw [mul_mul_mul_comm]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun t ↦ psi γ (i:ℕ) t*psi γ (j:ℕ) t) hcn]
  have he : c*(h/c)=h := by field_simp
  rw [he,mul_zero,smul_eq_mul]
  have hcoeff : c⁻¹^ (i:ℕ) * c⁻¹^(j:ℕ) * c⁻¹ =
      (Real.sqrt c*c^(i:ℕ))⁻¹ * (Real.sqrt c*c^(j:ℕ))⁻¹ := by
    fin_cases i <;> fin_cases j <;> norm_num
    all_goals field_simp
    all_goals nlinarith [hss]
  rw [← mul_assoc,hcoeff]

/-- The actual correlated Gaussian measure obeys the Brownian clock identity. -/
theorem klmcGaussian_clock (c γ h : ℝ) (hc : 0<c) (hh : 0≤h) :
    (klmcGaussian γ h).map (kineticBlockScale c) = klmcGaussian (c*γ) (h/c) := by
  letI : IsGaussian (klmcGaussian γ h) := by unfold klmcGaussian; infer_instance
  letI : IsGaussian (klmcGaussian (c*γ) (h/c)) := by unfold klmcGaussian; infer_instance
  apply IsGaussian.ext
  · change (∫ x, x ∂(klmcGaussian γ h).map (kineticBlockScale c))=(∫ x,x ∂klmcGaussian (c*γ) (h/c))
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp [klmcGaussian,kernelGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis fun i j ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply,ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov,covariance_map]
  · have he (i : Fin 2) : (fun x : EuclideanSpace ℝ (Fin 2) ↦
        ⟪(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i,x⟫) ∘ kineticBlockScale c =
        fun x ↦ (Real.sqrt c*c^(i:ℕ))⁻¹*x i := by
      funext x
      simp [PiLp.inner_apply]
    simp_rw [he,covariance_const_mul_left,covariance_const_mul_right]
    have hb (a b : Fin 2) : covarianceBilin (klmcGaussian (c*γ) (h/c))
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis a)
        ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis b) = klmcCovariance (c*γ) (h/c) a b := by
      rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id]
      have hei (a : Fin 2) : (fun x : EuclideanSpace ℝ (Fin 2) ↦
          ⟪(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis a,x⟫) = fun x ↦ x a := by
        funext x; simp [PiLp.inner_apply]
      simp_rw [hei]
      exact kernelGaussian_covariance _ (continuous_klmcKernels _) (div_nonneg hh hc.le) _ _
    rw [show cov[fun x : EuclideanSpace ℝ (Fin 2) ↦ x i,
        fun x ↦ x j; klmcGaussian γ h]=klmcCovariance γ h i j from
      kernelGaussian_covariance _ (continuous_klmcKernels γ) hh i j,hb i j,
      klmcCovariance_clock c γ h hc i j]
    ring
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

section PhaseScale
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The same Brownian clock map on full velocity-position vectors. -/
def phaseClockScale (c : ℝ) (z : E×E) : E×E :=
  ((Real.sqrt c)⁻¹ • z.1,(Real.sqrt c*c)⁻¹ • z.2)
end PhaseScale

/-- The actual particle-vector innovation retains its exact correlated clock law. -/
theorem exponentialNoise_clock (N dθ dx : ℕ) (c γ h : ℝ) (hc : 0<c) (hh : 0≤h) :
    (exponentialNoise N dθ dx γ h).map (phaseClockScale c) =
      exponentialNoise N dθ dx (c*γ) (h/c) := by
  have hp : (exponentialNoiseBlocks N dθ dx γ h).map
      (fun ω i ↦ kineticBlockScale c (ω i)) = exponentialNoiseBlocks N dθ dx (c*γ) (h/c) := by
    rw [exponentialNoiseBlocks,Measure.pi_map_pi (fun _ ↦ (kineticBlockScale c).measurable.aemeasurable)]
    simp_rw [klmcGaussian_clock c γ h hc hh]
    rfl
  rw [exponentialNoise,Measure.map_map (by unfold phaseClockScale; fun_prop) (assembleExponentialNoise_measurable N dθ dx)]
  have he : (phaseClockScale c ∘ (@assembleExponentialNoise N dθ dx)) =
      assembleExponentialNoise ∘ (fun ω i ↦ kineticBlockScale c (ω i)) := by
    funext ω
    ext i <;> simp [phaseClockScale,assembleExponentialNoise,kineticBlockScale_apply]
  rw [he,← Measure.map_map (assembleExponentialNoise_measurable N dθ dx) (by fun_prop),hp]
  rfl

/-- Unit-temperature KLMC and physical-time KIPLMC1 have identical actual updates after changing the clock. -/
theorem kiplmc1Step_unitTemperature {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ) (hγ : 0≤γ)
    (z ξ : State N dθ dx×State N dθ dx) :
    klmcStep (gradient (@IPLA.potential N dθ dx U)) (Real.sqrt N*γ) (h/Real.sqrt N)
      (rescaleVelocity (Real.sqrt N) z) (phaseClockScale (Real.sqrt N) ξ) =
      rescaleVelocity (Real.sqrt N) (kiplmc1Step U γ h z ξ) := by
  have hc : 0<Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hs : Real.sqrt (Real.sqrt N)≠0 := (Real.sqrt_pos.2 hc).ne'
  have he : Real.sqrt (2*(Real.sqrt N*γ))=Real.sqrt (Real.sqrt N)*Real.sqrt (2*γ) := by
    rw [← Real.sqrt_mul hc.le]
    congr 1
    ring
  have hv : Real.sqrt (2*(Real.sqrt N*γ))*(Real.sqrt (Real.sqrt N))⁻¹ =
      Real.sqrt N*kineticAmplitude N γ := by
    rw [he,unscale_kineticAmplitude hN γ]
    field_simp
  have hx : Real.sqrt (2*(Real.sqrt N*γ))*(Real.sqrt (Real.sqrt N)*Real.sqrt N)⁻¹ =
      kineticAmplitude N γ := by
    rw [he]
    have hn := unscale_kineticAmplitude hN γ
    field_simp
    nlinarith [hn]
  have hnoise : Real.sqrt (2*(Real.sqrt N*γ)) • phaseClockScale (Real.sqrt N) ξ =
      rescaleVelocity (Real.sqrt N) (kineticAmplitude N γ • ξ) := by
    ext <;> simp only [phaseClockScale,rescaleVelocity,Prod.smul_fst,Prod.smul_snd,smul_smul,hv,hx]
  unfold klmcStep kiplmc1Step
  rw [hnoise,exponentialStep_conjugate _ _ γ h hc.ne']
  simp only [Real.sq_sqrt (Nat.cast_nonneg N)]
  rfl

section NoiseMap
variable {A B Z : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Z]

/-- Pushing the innovation law forward is exactly substituting that map in every actual transition. -/
theorem markovLaws_noise_map (G : A→B→A) (R : Z→B)
    (hG : Measurable (Function.uncurry G)) (hR : Measurable R)
    (μ : Measure A) (Q : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure Q] (n : ℕ) :
    ULA.markovLaws (fun x ξ ↦ G x (R ξ)) Q μ n = ULA.markovLaws G (Q.map R) μ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((ULA.markovLaws (fun x ξ ↦ G x (R ξ)) Q μ n).prod Q).map
      (Function.uncurry (fun x ξ ↦ G x (R ξ))) =
        ((ULA.markovLaws G (Q.map R) μ n).prod (Q.map R)).map (Function.uncurry G)
    rw [ih]
    letI : IsProbabilityMeasure (Q.map R) := (Measure.isProbabilityMeasure_map_iff hR.aemeasurable).mpr inferInstance
    letI : IsProbabilityMeasure (ULA.markovLaws G (Q.map R) μ n) := ULA.markovLaws_isProbability G hG μ (Q.map R) n
    have hp := Measure.map_prod_map (ULA.markovLaws G (Q.map R) μ n) Q measurable_id hR
    rw [Measure.map_id] at hp
    rw [hp,Measure.map_map hG (measurable_id.prodMap hR)]
    rfl
end NoiseMap

/-- The exact law conjugacy includes the actual correlated Gaussian measures at the two clocks. -/
theorem kiplmc1GaussianLaws_unitTemperature {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) (γ h : ℝ)
    (hγ : 0≤γ) (hh : 0≤h)
    (μ : Measure (State N dθ dx×State N dθ dx)) [IsProbabilityMeasure μ] (n : ℕ) :
    (kiplmc1GaussianLaws U γ h μ n).map (rescaleVelocity (Real.sqrt N)) =
      ULA.markovLaws (klmcStep (gradient (@IPLA.potential N dθ dx U)) (Real.sqrt N*γ) (h/Real.sqrt N))
        (exponentialNoise N dθ dx (Real.sqrt N*γ) (h/Real.sqrt N))
        (μ.map (rescaleVelocity (Real.sqrt N))) n := by
  have hg := (IPLA.potential_gradient_lipschitz (N:=N) hdiff hLip).continuous
  have hstep : Measurable (Function.uncurry (klmcStep (gradient (@IPLA.potential N dθ dx U))
      (Real.sqrt N*γ) (h/Real.sqrt N))) := by
    apply Continuous.measurable
    unfold Function.uncurry klmcStep exponentialStep
    fun_prop
  have hscale : Measurable (@phaseClockScale (State N dθ dx) _ _ (Real.sqrt N)) := by
    unfold phaseClockScale
    fun_prop
  have hpair : Measurable (fun p : (State N dθ dx×State N dθ dx)×(State N dθ dx×State N dθ dx) ↦
      (p.1,phaseClockScale (Real.sqrt N) p.2)) :=
    measurable_fst.prodMk (hscale.comp measurable_snd)
  have hscaled : Measurable (Function.uncurry (fun (z ξ : State N dθ dx×State N dθ dx) ↦ klmcStep
      (gradient (@IPLA.potential N dθ dx U)) (Real.sqrt N*γ) (h/Real.sqrt N)
      z (phaseClockScale (Real.sqrt N) ξ))) := hstep.comp hpair
  have hc := markovLaws_map_conjugacy (kiplmc1Step U γ h)
    (fun z ξ ↦ klmcStep (gradient (@IPLA.potential N dθ dx U)) (Real.sqrt N*γ) (h/Real.sqrt N)
      z (phaseClockScale (Real.sqrt N) ξ)) (rescaleVelocity (Real.sqrt N))
    (kiplmc1Step_measurable hN hdiff hLip γ h) hscaled
    (by unfold rescaleVelocity; fun_prop)
    (fun z ξ ↦ (kiplmc1Step_unitTemperature hN U γ h hγ z ξ).symm)
    μ (exponentialNoise N dθ dx γ h) n
  change (ULA.markovLaws (kiplmc1Step U γ h) (exponentialNoise N dθ dx γ h) μ n).map
    (rescaleVelocity (Real.sqrt N)) = _
  rw [hc]
  rw [markovLaws_noise_map _ _ hstep hscale]
  rw [exponentialNoise_clock N dθ dx (Real.sqrt N) γ h (Real.sqrt_pos.2 (by exact_mod_cast hN)) hh]

/-- The actual independently thermal initialization becomes the standard kinetic initialization. -/
theorem thermalInitial_unitTemperature {N dθ dx : ℕ} (hN : 0<N)
    (ν : Measure (State N dθ dx)) [SFinite ν] :
    ((velocityTarget N dθ dx).prod ν).map (rescaleVelocity (Real.sqrt N)) =
      (stdGaussian (State N dθ dx)).prod ν := by
  have hp := Measure.map_prod_map (velocityTarget N dθ dx) ν
    (f:=fun v ↦ Real.sqrt N • v) (g:=id) (by fun_prop) measurable_id
  rw [Measure.map_id,velocityTarget_unscale hN] at hp
  exact hp.symm

/-- The position law of the actual particle sampler is exactly the standard-temperature
kinetic Markov position law at the changed clock. -/
theorem kiplmc1GaussianPositionLaws_unitTemperature {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) (γ h : ℝ)
    (hγ : 0≤γ) (hh : 0≤h)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] (n : ℕ) :
    (kiplmc1GaussianLaws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd =
      (ULA.markovLaws (klmcStep (gradient (@IPLA.potential N dθ dx U)) (Real.sqrt N*γ) (h/Real.sqrt N))
        (exponentialNoise N dθ dx (Real.sqrt N*γ) (h/Real.sqrt N))
        ((stdGaussian (State N dθ dx)).prod ν) n).map Prod.snd := by
  have hc := kiplmc1GaussianLaws_unitTemperature hN U L hdiff hLip γ h hγ hh
    ((velocityTarget N dθ dx).prod ν) n
  rw [thermalInitial_unitTemperature hN ν] at hc
  have hs := congrArg (fun ρ : Measure (State N dθ dx×State N dθ dx) ↦ ρ.map Prod.snd) hc
  rw [Measure.map_map measurable_snd (by unfold rescaleVelocity; fun_prop)] at hs
  exact hs

end KIPLMC
