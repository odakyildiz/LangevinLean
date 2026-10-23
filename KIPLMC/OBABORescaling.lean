import KIPLMC.Rescaling
import KIPLMC.Laws
import KIPLMC.Target
import KineticLangevin.GibbsTarget
import KineticLangevin.OBABOLaw

/-! # Exact transfer of particle OBABO to unit temperature

The time change by `sqrt N`, together with velocity multiplication by the
same factor, conjugates the actual KIPLMC2 chain to standard-temperature
OBABO for the sum potential. The position is unchanged. This identity also
transports the actual independent-noise laws and their Gibbs target.
-/
noncomputable section
set_option linter.style.header false
open MeasureTheory
open scoped NNReal
namespace KIPLMC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The velocity change intertwines the actual thermostat maps. -/
theorem ornsteinStep_conjugate (c δ σ : ℝ) (z : E × E) (ξ : E) :
    KineticLangevin.ornsteinStep δ (c*σ) ξ (rescaleVelocity c z) =
      rescaleVelocity c (KineticLangevin.ornsteinStep δ σ ξ z) := by
  ext <;> simp only [KineticLangevin.ornsteinStep,rescaleVelocity] <;> module

/-- The drift keeps the position fixed under the changed kinetic clock. -/
theorem driftStep_conjugate (c h : ℝ) (hc : c ≠ 0) (z : E×E) :
    KineticLangevin.driftStep (h/c) (rescaleVelocity c z) =
      rescaleVelocity c (KineticLangevin.driftStep h z) := by
  have he : h/c*c=h := by field_simp
  ext <;> simp [KineticLangevin.driftStep,rescaleVelocity,smul_smul,he]

/-- The force gains precisely the square of the clock factor. -/
theorem kickStep_conjugate (g : E → E) (c h : ℝ) (hc : c ≠ 0) (z : E×E) :
    KineticLangevin.kickStep g (h/c) (rescaleVelocity c z) =
      rescaleVelocity c (KineticLangevin.kickStep (fun x ↦ (c^2)⁻¹ • g x) h z) := by
  have he : c*(h*(c^2)⁻¹)=h/c := by field_simp
  ext <;> simp [KineticLangevin.kickStep,rescaleVelocity,smul_sub,smul_smul,he]

/-- The entire five-subflow map is conjugated, including both fresh noises. -/
theorem obaboStep_conjugate (g : E → E) (c h δ σ : ℝ) (hc : c ≠ 0)
    (z : E×E) (ξ ξ' : E) :
    KineticLangevin.obaboStep g (h/c) δ (c*σ) (rescaleVelocity c z) ξ ξ' =
      rescaleVelocity c
        (KineticLangevin.obaboStep (fun x ↦ (c^2)⁻¹ • g x) h δ σ z ξ ξ') := by
  have he : h/c/2=(h/2)/c := by ring
  unfold KineticLangevin.obaboStep
  rw [he,ornsteinStep_conjugate,kickStep_conjugate g c (h/2) hc,
    driftStep_conjugate c h hc,kickStep_conjugate g c (h/2) hc,
    ornsteinStep_conjugate]

/-- The weighted phase energy is unchanged by the paper's clock/velocity
rescaling when curvature and friction are rescaled as well. -/
theorem weightedPhaseEnergy_rescaleVelocity
    (c L γ : ℝ) (hc : 0<c) (z : E×E) :
    KineticLangevin.weightedPhaseEnergy (1/(c^2*L)) (1/(c*γ)) (rescaleVelocity c z) =
      KineticLangevin.weightedPhaseEnergy (1/L) (1/γ) z := by
  simp only [KineticLangevin.weightedPhaseEnergy,rescaleVelocity,inner_smul_right,
    norm_smul,Real.norm_eq_abs,abs_of_pos hc,mul_pow]
  field_simp
  <;> ring

/-- KIPLMC2 is exactly unit-temperature OBABO at the transformed clock. -/
theorem kiplmc2Step_unitTemperature {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx) (ξ ξ' : State N dθ dx) :
    KineticLangevin.obaboStep (gradient (@IPLA.potential N dθ dx U))
      (h/Real.sqrt N) (KineticLangevin.obaboDamping (Real.sqrt N*γ) (h/Real.sqrt N))
      (Real.sqrt (KineticLangevin.obaboVariance (Real.sqrt N*γ) (h/Real.sqrt N)))
      (rescaleVelocity (Real.sqrt N) z) ξ ξ' =
        rescaleVelocity (Real.sqrt N) (kiplmc2Step U γ h z ξ ξ') := by
  have hc : Real.sqrt N ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hN)).ne'
  rw [obaboDamping_scaled _ γ h hc]
  have hv : KineticLangevin.obaboVariance (Real.sqrt N*γ) (h/Real.sqrt N) =
      KineticLangevin.obaboVariance γ h := by
    unfold KineticLangevin.obaboVariance
    rw [obaboDamping_scaled _ γ h hc]
  rw [hv,← unscale_thermalAmplitude hN γ h,obaboStep_conjugate _ _ h _ _ hc]
  simp only [Real.sq_sqrt (Nat.cast_nonneg N)]
  rfl

/-- The transformed particle chain is the actual standard-temperature
OBABO recursion, step for step and for the same paired innovations. -/
theorem kiplmc2Chain_unitTemperature {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx)
    (noise : ℕ → State N dθ dx × State N dθ dx) (n : ℕ) :
    rescaleVelocity (Real.sqrt N) (kiplmc2Chain U γ h z noise n) =
      ULA.noiseDrivenChain (fun s ξ ↦ KineticLangevin.obaboStep
        (gradient (@IPLA.potential N dθ dx U)) (h/Real.sqrt N)
        (KineticLangevin.obaboDamping (Real.sqrt N*γ) (h/Real.sqrt N))
        (Real.sqrt (KineticLangevin.obaboVariance (Real.sqrt N*γ) (h/Real.sqrt N)))
        s ξ.1 ξ.2) (rescaleVelocity (Real.sqrt N) z) noise n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold kiplmc2Chain at ih ⊢
    rw [ULA.noiseDrivenChain_succ,ULA.noiseDrivenChain_succ,← ih]
    exact (kiplmc2Step_unitTemperature hN U γ h _ _ _).symm

/-- Rescaling the independent canonical phase target changes exactly the
velocity temperature. The configuration Gibbs law stays the same. -/
theorem kineticTarget_rescaleVelocity {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (hm : 0<m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U) :
    (KineticLangevin.kineticGibbsTarget (@IPLA.potential N dθ dx U)).map
      (rescaleVelocity (Real.sqrt N)⁻¹) = gibbsPhaseTarget U := by
  letI : IsProbabilityMeasure (ULA.gibbsMeasure (@IPLA.potential N dθ dx U)) := by
    change IsProbabilityMeasure (@IPLA.gibbsTarget N dθ dx U)
    exact IPLA.gibbsTarget_isProbability hN U m hm hdiff hsc
  have hr := Measure.map_prod_map
    (ProbabilityTheory.stdGaussian (State N dθ dx))
    (ULA.gibbsMeasure (@IPLA.potential N dθ dx U))
    (f := fun v ↦ (Real.sqrt N)⁻¹ • v) (g := id) (by fun_prop) measurable_id
  rw [Measure.map_id] at hr
  change ((ProbabilityTheory.stdGaussian (State N dθ dx)).prod
      (ULA.gibbsMeasure (@IPLA.potential N dθ dx U))).map
        (fun p ↦ ((Real.sqrt N)⁻¹ • p.1,p.2)) =
    ((ProbabilityTheory.stdGaussian (State N dθ dx)).map
      (fun v ↦ (Real.sqrt N)⁻¹ • v)).prod
        (ULA.gibbsMeasure (@IPLA.potential N dθ dx U))
  exact hr.symm

/-- The actual independent-Gaussian particle law is the pushforward of the
same unit-temperature OBABO law, with no assumed chain-law correspondence. -/
theorem kiplmc2Laws_unitTemperature {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) (γ h : ℝ)
    (μ : Measure (State N dθ dx × State N dθ dx)) [IsProbabilityMeasure μ] (n : ℕ) :
    (kiplmc2Laws U γ h μ n).map (rescaleVelocity (Real.sqrt N)) =
      KineticLangevin.obaboLaws (gradient (@IPLA.potential N dθ dx U))
        (Real.sqrt N*γ) (h/Real.sqrt N)
        (Real.sqrt (KineticLangevin.obaboVariance (Real.sqrt N*γ) (h/Real.sqrt N)))
        (obaboNoise N dθ dx) (μ.map (rescaleVelocity (Real.sqrt N))) n := by
  have hg : Continuous (gradient (@IPLA.potential N dθ dx U)) :=
    (IPLA.potential_gradient_lipschitz hdiff hLip).continuous
  apply KineticLangevin.markovLaws_map_conjugacy
  · exact kiplmc2Step_measurable hN hdiff hLip γ h
  · apply Continuous.measurable
    unfold Function.uncurry KineticLangevin.obaboStep KineticLangevin.ornsteinStep
      KineticLangevin.kickStep KineticLangevin.driftStep
    fun_prop
  · unfold rescaleVelocity
    fun_prop
  · intro z ξ
    exact (kiplmc2Step_unitTemperature hN U γ h z ξ.1 ξ.2).symm

end KIPLMC
