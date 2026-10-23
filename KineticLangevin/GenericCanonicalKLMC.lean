import KineticLangevin.GenericCanonicalSource
import KineticLangevin.CoupledSegments
import KineticLangevin.SegmentGlobal
import KineticLangevin.ProductLaw
import KineticLangevin.LpConvergence
import KineticLangevin.StationarityTransfer
import UnadjustedLangevin.InitialCoupling

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.GenericCanonicalCoupling
open BrownianConvolution
abbrev H (ι : Type*) := EuclideanSpace ℝ ι
abbrev Sample (ι : Type*) := (H ι × H ι) × (H ι × ULA.CanonicalBrownian.VectorSample ι)
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ π : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The actual initial-position coupling, extended by independent Gaussian velocity and vector Brownian source. -/
abbrev probability (c : ULA.Coupling μ π) := ULA.initialExtension c (GenericCanonicalSource.canonicalSourceProbability ι)

instance probability_isProbabilityMeasure (c : ULA.Coupling μ π) : IsProbabilityMeasure (probability c) :=
  ULA.initialExtension_isProbabilityMeasure c _

local instance couplingProbability (c : ULA.Coupling μ π) : IsProbabilityMeasure c.joint := c.isProbabilityMeasure

/-- Pull the canonical vector Brownian L² space onto the concrete initial-coupling extension. -/
def brownianLift (c : ULA.Coupling μ π) :
    Lp (H ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ] Lp (H ι) 2 (probability c) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun p : Sample ι => p.2.2)
    ((measurePreserving_snd : MeasurePreserving Prod.snd (GenericCanonicalSource.canonicalSourceProbability ι)
      (ULA.CanonicalBrownian.vectorProbability ι)).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd (probability c) (GenericCanonicalSource.canonicalSourceProbability ι)))).toContinuousLinearMap

/-- The source lift is the actual Brownian-source projection of the product extension. -/
theorem brownianLift_coe (c : ULA.Coupling μ π)
    (Z : Lp (H ι) 2 (ULA.CanonicalBrownian.vectorProbability ι)) :
    brownianLift c Z =ᵐ[probability c] fun p : Sample ι => Z p.2.2 :=
  Lp.coeFn_compMeasurePreserving Z
    ((measurePreserving_snd : MeasurePreserving Prod.snd (GenericCanonicalSource.canonicalSourceProbability ι)
      (ULA.CanonicalBrownian.vectorProbability ι)).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd (probability c) (GenericCanonicalSource.canonicalSourceProbability ι)))

/-- Include the fluctuation-dissipation amplitude in the same continuous linear source lift. -/
def inputLift (c : ULA.Coupling μ π) (γ : ℝ) := Real.sqrt (2*γ) • brownianLift c

/-- The actual scaled Brownian increment used by both exact coupling segments at iteration `n`. -/
def input (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) (t : ℝ) : Lp (H ι) 2 (probability c) :=
  inputLift c γ (vectorBrownianIncrementLp ι ((n : ℝ≥0)*h) t.toNNReal)

/-- The same Brownian interval filtered by the exact exponential velocity response. -/
def filtered (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) (t : ℝ) : Lp (H ι) 2 (probability c) :=
  inputLift c γ (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) t.toNNReal)

/-- Unscaled correlated velocity-position responses for the implemented KLMC update. -/
def innovation (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    Lp (H ι) 2 (probability c) × Lp (H ι) 2 (probability c) :=
  (brownianLift c (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h),
   brownianLift c (vectorSegmentLp ι (psi γ 1) (continuous_psi γ 1) ((n : ℝ≥0)*h) h))

theorem continuous_input (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    Continuous (input c γ h n) :=
  (inputLift c γ).continuous.comp ((continuous_vectorBrownianIncrementLp ι _).comp continuous_real_toNNReal)

theorem continuous_filtered (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    Continuous (filtered c γ h n) :=
  (inputLift c γ).continuous.comp
    ((continuous_vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) _).comp continuous_real_toNNReal)

@[simp] theorem input_zero (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) : input c γ h n 0 = 0 := by
  unfold input vectorBrownianIncrementLp segmentBrownianLp
  simp only [Real.toNNReal_zero,add_zero,sub_self,map_zero]

/-- The constructed filtered input satisfies the exact Brownian integral equation on every step. -/
theorem filtered_integral_equation (c : ULA.Coupling μ π) (γ : ℝ) (hγ : 0 ≤ γ)
    (h : ℝ≥0) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    filtered c γ h n t = input c γ h n t - γ • ∫ s in 0..t, filtered c γ h n s := by
  have hc : Continuous (fun s : ℝ =>
      vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) s.toNNReal) :=
    (continuous_vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) _).comp continuous_real_toNNReal
  unfold filtered input
  rw [vectorSegmentLp_integral_equation ι γ hγ,Real.coe_toNNReal t ht,map_sub,map_smul,
    ← (inputLift c γ).intervalIntegral_comp_comm (f := fun s : ℝ =>
      vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) s.toNNReal)
      (hc.intervalIntegrable _ _)]

/-- Integrating the actual filtered input gives exactly the scaled positional Gaussian innovation. -/
theorem integral_filtered (c : ULA.Coupling μ π) (γ : ℝ) (hγ : 0 ≤ γ)
    (h : ℝ≥0) (n : ℕ) :
    (∫ s in 0..(h : ℝ), filtered c γ h n s) = Real.sqrt (2*γ) • (innovation c γ h n).2 := by
  have hc : Continuous (fun s : ℝ =>
      vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) s.toNNReal) :=
    (continuous_vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) _).comp continuous_real_toNNReal
  unfold filtered innovation
  rw [(inputLift c γ).intervalIntegral_comp_comm (f := fun s : ℝ =>
      vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) s.toNNReal)
      (hc.intervalIntegrable _ _),← vectorSegmentLp_primitive ι γ hγ]
  rfl

/-- The endpoint velocity response is exactly the scaled velocity Gaussian innovation. -/
theorem filtered_endpoint (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    filtered c γ h n h = Real.sqrt (2*γ) • (innovation c γ h n).1 := by
  unfold filtered innovation inputLift
  simp only [Real.toNNReal_coe,ContinuousLinearMap.smul_apply]

/-- The actual exponential chain is precisely the implemented KLMC chain with the same canonical innovations. -/
theorem exponentialInputChain_eq_klmcChain (c : ULA.Coupling μ π)
    (g : Lp (H ι) 2 (probability c) → Lp (H ι) 2 (probability c))
    (γ : ℝ) (hγ : 0 ≤ γ) (h : ℝ≥0)
    (initial : Lp (H ι) 2 (probability c) × Lp (H ι) 2 (probability c)) (n : ℕ) :
    exponentialInputChain g γ h initial (filtered c γ h) n =
      klmcChain g γ h initial (innovation c γ h) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exponentialInputChain_succ,klmcChain_succ,ih,filtered_endpoint,integral_filtered c γ hγ]
    rfl

/-- The L² innovations on the coupling extension are the pointwise canonical Brownian innovations. -/
theorem innovation_coe (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    (fun p : Sample ι => lpPhaseCoe (probability c) (innovation c γ h n) p)
      =ᵐ[probability c] fun p => GenericCanonicalSource.canonicalKLMCInnovation ι γ h n p.2.2 := by
  have hp := ((measurePreserving_snd : MeasurePreserving Prod.snd (GenericCanonicalSource.canonicalSourceProbability ι)
      (ULA.CanonicalBrownian.vectorProbability ι)).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd (probability c) (GenericCanonicalSource.canonicalSourceProbability ι))).quasiMeasurePreserving.ae_eq_comp
    (GenericCanonicalSource.vectorSegmentLp_klmcInnovation_coe ι γ h n)
  filter_upwards [brownianLift_coe c (vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h),
    brownianLift_coe c (vectorSegmentLp ι (psi γ 1) (continuous_psi γ 1) ((n : ℝ≥0)*h) h),hp]
    with p hv hx hp
  change (brownianLift c _ p,brownianLift c _ p) = _
  rw [hv,hx]
  exact hp

/-- The actual Brownian L² innovation is exactly the generic product-law layer's innovation variable. -/
theorem innovation_eq_extensionInnovation (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    innovation c γ h n =
      extensionInnovation (GenericCanonicalSource.canonicalSourceProbability ι) c
        (fun k p => GenericCanonicalSource.canonicalKLMCInnovation ι γ h k p.2)
        (fun k => (GenericCanonicalSource.canonicalSourceInnovation_memLp ι γ h k).1)
        (fun k => (GenericCanonicalSource.canonicalSourceInnovation_memLp ι γ h k).2) n := by
  have hmine := innovation_coe c γ h n
  have hprod := extensionInnovation_coe (GenericCanonicalSource.canonicalSourceProbability ι) c
    (fun k p => GenericCanonicalSource.canonicalKLMCInnovation ι γ h k p.2)
    (fun k => (GenericCanonicalSource.canonicalSourceInnovation_memLp ι γ h k).1)
    (fun k => (GenericCanonicalSource.canonicalSourceInnovation_memLp ι γ h k).2) n
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [hmine,hprod] with p hm hp
    exact congrArg Prod.fst (hm.trans hp.symm)
  · apply Lp.ext
    filter_upwards [hmine,hprod] with p hm hp
    exact congrArg Prod.snd (hm.trans hp.symm)

/-- The shared initial Gaussian velocity on the concrete coupling extension. -/
def initialVelocity (c : ULA.Coupling μ π) : Lp (H ι) 2 (probability c) :=
  extensionVelocity (GenericCanonicalSource.canonicalSourceProbability ι) c Prod.fst (GenericCanonicalSource.canonicalSourceVelocity_memLp ι)

/-- The actual numerical initial state has the prescribed first position marginal. -/
def numericalInitial (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π) :
    Lp (H ι) 2 (probability c) × Lp (H ι) 2 (probability c) :=
  (initialVelocity c,ULA.initialExtension_lpInitial c (GenericCanonicalSource.canonicalSourceProbability ι) hc hπ)

/-- The reference uses the second position marginal and the identical velocity variable. -/
def referenceInitial (c : ULA.Coupling μ π) (hπ : MemLp (id : H ι → H ι) 2 π) :
    Lp (H ι) 2 (probability c) × Lp (H ι) 2 (probability c) :=
  (initialVelocity c,ULA.initialExtension_lpReference c (GenericCanonicalSource.canonicalSourceProbability ι) hπ)

/-- The initial reference phase is the explicit Gaussian velocity and second coupling coordinate. -/
theorem referenceInitial_coe (c : ULA.Coupling μ π) (hπ : MemLp (id : H ι → H ι) 2 π) :
    (fun p : Sample ι => lpPhaseCoe (probability c) (referenceInitial c hπ) p)
      =ᵐ[probability c] fun p => (p.2.1,p.1.2) := by
  filter_upwards [extensionVelocity_coe (GenericCanonicalSource.canonicalSourceProbability ι) c Prod.fst (GenericCanonicalSource.canonicalSourceVelocity_memLp ι),
    (ULA.initialExtension_memLp_reference c (GenericCanonicalSource.canonicalSourceProbability ι) hπ).coeFn_toLp]
    with p hv hx
  exact Prod.ext hv hx

/-- The actual reference initial phase has the canonical product target law. -/
theorem referenceInitial_law (c : ULA.Coupling μ π) (hπ : MemLp (id : H ι → H ι) 2 π) :
    HasLaw (fun p : Sample ι => lpPhaseCoe (probability c) (referenceInitial c hπ) p)
      ((stdGaussian (H ι)).prod π) (probability c) := by
  have hv : HasLaw (fun p : Sample ι => p.2.1) (stdGaussian (H ι)) (probability c) :=
    (GenericCanonicalSource.canonicalSourceVelocity_law ι).comp (measurePreserving_snd.hasLaw)
  have hx : HasLaw (fun p : Sample ι => p.1.2) π (probability c) :=
    ⟨(measurable_fst.snd).aemeasurable,ULA.initialExtension_reference c (GenericCanonicalSource.canonicalSourceProbability ι)⟩
  have hind : IndepFun (fun p : Sample ι => p.2.1) (fun p : Sample ι => p.1.2) (probability c) :=
    (indepFun_prod (μ := c.joint) (ν := GenericCanonicalSource.canonicalSourceProbability ι)
      (X := Prod.snd) (Y := Prod.fst) measurable_snd measurable_fst).symm
  exact (hind.hasLaw_prod hv hx).congr (referenceInitial_coe c hπ)

/-- The canonical numerical chain, with the actual lifted original gradient. -/
def numericalChain (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ : ℝ) (h : ℝ≥0) :
    ℕ → Lp (H ι) 2 (probability c) × Lp (H ι) 2 (probability c) :=
  klmcChain (ULA.lpDrift (probability c) (gradient f) hLip) γ h
    (numericalInitial c hc hπ) (innovation c γ h)

/-- The reference's exact segment chain is constructed using the same canonical Brownian increments. -/
def referenceChain (c : ULA.Coupling μ π) (hπ : MemLp (id : H ι → H ι) 2 π)
    (f : H ι → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    ℕ → Lp (H ι) 2 (probability c) × Lp (H ι) 2 (probability c) :=
  kineticReferenceChain (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz _ _ hLip) h h.coe_nonneg (referenceInitial c hπ)
    (input c γ h) (continuous_input c γ h)

/-- Each actual reference segment starts at its reference chain state. -/
def referenceSegment (c : ULA.Coupling μ π) (hπ : MemLp (id : H ι → H ι) 2 π)
    (f : H ι → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    ℕ → ℝ → Lp (H ι) 2 (probability c) × Lp (H ι) 2 (probability c) :=
  kineticReferenceSegment (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz _ _ hLip) h h.coe_nonneg (referenceInitial c hπ)
    (input c γ h) (continuous_input c γ h)

/-- Each auxiliary exact segment starts at the implemented numerical state, with the shared canonical input. -/
def auxiliarySegment (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    ℕ → ℝ → Lp (H ι) 2 (probability c) × Lp (H ι) 2 (probability c) :=
  kineticAuxiliarySegment (ULA.lpDrift (probability c) (gradient f) hLip) M γ
    (ULA.lpDrift_lipschitz _ _ hLip) h h.coe_nonneg (numericalInitial c hc hπ)
    (input c γ h) (filtered c γ h) (continuous_input c γ h)


/-- Every analytic segment requirement of the first-order coupling theorem is furnished by the actual construction. -/
theorem segments_spec (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    let S := numericalChain c hc hπ f M hLip γ h
    let R := referenceChain c hπ f M γ hLip h
    let A := auxiliarySegment c hc hπ f M γ hLip h
    let Z := referenceSegment c hπ f M γ hLip h
    let B := filtered c γ h
    let W := fun n t => (input c γ h n t, (0 : Lp (H ι) 2 (probability c)))
    let g := ULA.lpDrift (probability c) (gradient f) hLip
    (∀ n, Continuous (A n)) ∧ (∀ n, Continuous (Z n)) ∧ (∀ n, Continuous (B n)) ∧
      (∀ n, A n 0 = S n) ∧ (∀ n, Z n 0 = R n) ∧ (∀ n, Z n h = R (n+1)) ∧
      (∀ n, S (n+1) = exponentialStep g γ h (S n) (B n h,∫ s in 0..(h : ℝ), B n s)) ∧
      (∀ n t, t ∈ Icc 0 (h : ℝ) → A n t - A n 0 =
        -(∫ s in 0..t, kineticNegativeDrift g γ 1 (A n s)) + W n t) ∧
      (∀ n t, t ∈ Icc 0 (h : ℝ) → Z n t - Z n 0 =
        -(∫ s in 0..t, kineticNegativeDrift g γ 1 (Z n s)) + W n t) ∧
      (∀ n t, t ∈ Icc 0 (h : ℝ) → (A n t).1 = psi γ 0 t • (A n 0).1 -
        (∫ s in 0..t, Real.exp (-(γ : ℝ)*(t-s)) • g (A n s).2) + B n t) ∧
      (∀ n t, t ∈ Icc 0 (h : ℝ) → (A n t).2-(A n 0).2 = ∫ s in 0..t, (A n s).1) ∧
      (S 0).1 = (R 0).1 := by
  dsimp only
  let g := ULA.lpDrift (probability c) (gradient f) hLip
  have hg := ULA.lpDrift_lipschitz (probability c) (gradient f) hLip
  have hA := kineticAuxiliarySegment_spec g M γ hg h h.coe_nonneg
    (numericalInitial c hc hπ) (input c γ h) (filtered c γ h) (continuous_input c γ h) (input_zero c γ h)
  have hZ := kineticReferenceSegment_spec g M γ 1 hg h h.coe_nonneg
    (referenceInitial c hπ) (input c γ h) (continuous_input c γ h) (input_zero c γ h)
  have hn (n : ℕ) : exponentialInputChain g γ h (numericalInitial c hc hπ) (filtered c γ h) n =
      numericalChain c hc hπ f M hLip γ h n :=
    exponentialInputChain_eq_klmcChain c g γ γ.coe_nonneg h _ n
  refine ⟨fun n => (hA n).1,fun n => (hZ n).1,continuous_filtered c γ h,?_,?_,?_,?_,?_,?_,?_,?_,rfl⟩
  · intro n
    exact (hA n).2.1.trans (hn n)
  · intro n
    exact (hZ n).2.1
  · intro n
    exact (hZ n).2.2.1
  · intro n
    rw [← hn (n+1),← hn n]
    rfl
  · intro n t ht
    exact (hA n).2.2 t ht
  · intro n t ht
    simpa only [referenceSegment,g,NNReal.coe_one] using (hZ n).2.2.2 t ht
  · intro n t ht
    exact kineticAuxiliarySegment_mild g M γ hg h h.coe_nonneg
      (numericalInitial c hc hπ) (input c γ h) (filtered c γ h) (continuous_input c γ h) (input_zero c γ h)
      (continuous_filtered c γ h)
      (fun k s hs => filtered_integral_equation c γ γ.coe_nonneg h k s hs.1) n t ht
  · intro n t ht
    exact kineticAuxiliarySegment_kinematic g M γ hg h h.coe_nonneg
      (numericalInitial c hc hπ) (input c γ h) (filtered c γ h) (continuous_input c γ h) (input_zero c γ h) n t ht

end KineticLangevin.GenericCanonicalCoupling

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.GenericCanonicalCoupling
open BrownianConvolution
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ π : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The full continuous canonical Brownian input on the actual initial-coupling extension. -/
def globalInput (c : ULA.Coupling μ π) (γ : ℝ) (t : ℝ) : Lp (H ι) 2 (probability c) :=
  inputLift c γ (spatialLift ι (ULA.CanonicalBrownian.valueLp t.toNNReal))

theorem continuous_globalInput (c : ULA.Coupling μ π) (γ : ℝ) : Continuous (globalInput c γ) := by
  have hc : Continuous (ULA.CanonicalBrownian.valueLp) := by
    rw [show ULA.CanonicalBrownian.valueLp = velocityLp 0 from funext velocityLp_zero_friction |>.symm]
    exact continuous_velocityLp 0
  exact (inputLift c γ).continuous.comp ((spatialLift ι).continuous.comp
    (hc.comp continuous_real_toNNReal))

@[simp] theorem globalInput_zero (c : ULA.Coupling μ π) (γ : ℝ) : globalInput c γ 0 = 0 := by
  have hi : ULA.CanonicalBrownian.timeIndicator 0 = 0 := by
    rw [← timeKernelLp_one]
    apply Lp.ext
    filter_upwards [timeKernelLp_coe (fun _ => 1) continuous_const 0,Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)]
      with r hr hz
    rw [hr,hz]
    simp [timeKernel]
  unfold globalInput ULA.CanonicalBrownian.valueLp
  simp only [Real.toNNReal_zero,hi,map_zero]

/-- Every constructed local input is exactly the increment of the same full canonical Brownian input. -/
theorem input_eq_globalInput_increment (c : ULA.Coupling μ π) (γ : ℝ)
    (h : ℝ≥0) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    input c γ h n t = globalInput c γ ((n : ℝ)*(h : ℝ)+t) - globalInput c γ ((n : ℝ)*(h : ℝ)) := by
  let a : ℝ≥0 := (n : ℝ≥0)*h
  have ha : (a : ℝ) = (n : ℝ)*(h : ℝ) := by simp [a]
  have he : ((a : ℝ)+t).toNNReal = a+t.toNNReal := by
    apply NNReal.coe_injective
    simp only [Real.coe_toNNReal _ (by linarith [a.coe_nonneg] : 0 ≤ (a : ℝ)+t),
      NNReal.coe_add,Real.coe_toNNReal t ht]
  unfold input globalInput vectorBrownianIncrementLp segmentBrownianLp
  rw [← ha,he,Real.toNNReal_coe,← map_sub,← map_sub]

/-- The actual full selected kinetic solution started from the canonical reference initial phase. -/
def globalReferenceFlow (c : ULA.Coupling μ π) (hπ : MemLp (id : H ι → H ι) 2 π)
    (f : H ι → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) : ℝ → Lp (H ι) 2 (probability c) × Lp (H ι) 2 (probability c) :=
  kineticSegmentFlow (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz _ _ hLip) T hT (referenceInitial c hπ)
    (globalInput c γ) (continuous_globalInput c γ)

/-- The full reference flow supplies its actual continuous kinetic integral equation. -/
theorem globalReferenceFlow_spec (c : ULA.Coupling μ π) (hπ : MemLp (id : H ι → H ι) 2 π)
    (f : H ι → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) :
    Continuous (globalReferenceFlow c hπ f M γ hLip T hT) ∧
      globalReferenceFlow c hπ f M γ hLip T hT 0 = referenceInitial c hπ ∧
      ∀ t ∈ Icc 0 T,
        globalReferenceFlow c hπ f M γ hLip T hT t - globalReferenceFlow c hπ f M γ hLip T hT 0 =
        -(∫ s in 0..t, kineticNegativeDrift (ULA.lpDrift (probability c) (gradient f) hLip) γ 1
          (globalReferenceFlow c hπ f M γ hLip T hT s)) + (globalInput c γ t,0) := by
  have hs := kineticSegmentFlow_spec (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz _ _ hLip) T hT (referenceInitial c hπ)
    (globalInput c γ) (continuous_globalInput c γ) (globalInput_zero c γ)
  refine ⟨hs.1,hs.2.1,?_⟩
  intro t ht
  simpa only [globalReferenceFlow,hs.2.1,NNReal.coe_one] using hs.2.2 t ht

/-- The constructed canonical reference chain equals the actual global reference solution at every grid point. -/
theorem referenceChain_eq_globalReferenceFlow (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (hn : (n : ℝ)*(h : ℝ) ≤ T) :
    referenceChain c hπ f M γ hLip h n = globalReferenceFlow c hπ f M γ hLip T hT ((n : ℝ)*(h : ℝ)) := by
  have hs := globalReferenceFlow_spec c hπ f M γ hLip T hT
  exact kineticReferenceChain_eq_global (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz _ _ hLip) h h.coe_nonneg (referenceInitial c hπ) (input c γ h)
    (continuous_input c γ h) (input_zero c γ h) _ (globalInput c γ) hs.1 T hs.2.1
    (by simpa only [NNReal.coe_one] using hs.2.2)
    (fun k t ht => input_eq_globalInput_increment c γ h k t ht.1) n hn

/-- Every intermediate canonical reference segment point equals the same actual global kinetic solution. -/
theorem referenceSegment_eq_globalReferenceFlow (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (hn : ((n : ℝ)+1)*(h : ℝ) ≤ T) (t : ℝ) (ht : t ∈ Icc 0 (h : ℝ)) :
    referenceSegment c hπ f M γ hLip h n t =
      globalReferenceFlow c hπ f M γ hLip T hT ((n : ℝ)*(h : ℝ)+t) := by
  have hs := globalReferenceFlow_spec c hπ f M γ hLip T hT
  exact kineticReferenceSegment_eq_global (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz _ _ hLip) h h.coe_nonneg (referenceInitial c hπ) (input c γ h)
    (continuous_input c γ h) (input_zero c γ h) _ (globalInput c γ) hs.1 T hs.2.1
    (by simpa only [NNReal.coe_one] using hs.2.2)
    (fun k t ht => input_eq_globalInput_increment c γ h k t ht.1) n hn t ht

end KineticLangevin.GenericCanonicalCoupling

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.GenericCanonicalCoupling
open BrownianConvolution
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ π : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The explicit phase/Brownian projection of each initial coupling has the independent canonical product law. -/
theorem initialPhase_brownian_jointLaw (c : ULA.Coupling μ π) :
    HasLaw (fun p : Sample ι => ((p.2.1,p.1.2),p.2.2))
      (((stdGaussian (H ι)).prod π).prod (ULA.CanonicalBrownian.vectorProbability ι)) (probability c) := by
  haveI : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  haveI : IsProbabilityMeasure π := by
    have hl : HasLaw Prod.snd π c.joint := ⟨measurable_snd.aemeasurable,c.snd⟩
    exact hl.isProbabilityMeasure_iff.mp inferInstance
  have hproj : HasLaw (fun p : Sample ι => (p.1.2,p.2)) (π.prod (GenericCanonicalSource.canonicalSourceProbability ι)) (probability c) := by
    refine ⟨(measurable_fst.snd.prodMk measurable_snd).aemeasurable,?_⟩
    change (c.joint.prod (GenericCanonicalSource.canonicalSourceProbability ι)).map (Prod.map Prod.snd id) = _
    simpa only [c.snd,Measure.map_id] using
      (Measure.map_prod_map c.joint (GenericCanonicalSource.canonicalSourceProbability ι) measurable_snd measurable_id).symm
  have hassoc : HasLaw (MeasurableEquiv.prodAssoc : ((H ι×H ι)×ULA.CanonicalBrownian.VectorSample ι) ≃ᵐ _).symm
      ((π.prod (stdGaussian (H ι))).prod (ULA.CanonicalBrownian.vectorProbability ι))
      (π.prod (GenericCanonicalSource.canonicalSourceProbability ι)) :=
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc π (stdGaussian (H ι)) (ULA.CanonicalBrownian.vectorProbability ι))).hasLaw
  have hswap : HasLaw (Prod.map Prod.swap id : (H ι×H ι)×ULA.CanonicalBrownian.VectorSample ι → _)
      (((stdGaussian (H ι)).prod π).prod (ULA.CanonicalBrownian.vectorProbability ι))
      ((π.prod (stdGaussian (H ι))).prod (ULA.CanonicalBrownian.vectorProbability ι)) :=
    ((Measure.measurePreserving_swap (μ := π) (ν := stdGaussian (H ι))).prod
      (MeasurePreserving.id (ULA.CanonicalBrownian.vectorProbability ι))).hasLaw
  exact hswap.comp (hassoc.comp hproj)

/-- The global forcing's actual OU increment equals the already constructed filtered velocity response. -/
theorem ouInputIncrement_globalInput (c : ULA.Coupling μ π) (γ : ℝ) (hγ : 0 ≤ γ)
    (h : ℝ≥0) (n : ℕ) :
    ouInputIncrement γ (globalInput c γ) ((n : ℝ)*(h : ℝ)) h = filtered c γ h n h := by
  have hc : Continuous (fun s : ℝ => Real.exp (-γ*((h : ℝ)-s)) •
      vectorBrownianIncrementLp ι ((n : ℝ≥0)*h) s.toNNReal) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-γ*((h : ℝ)-s)))).smul
      ((continuous_vectorBrownianIncrementLp ι _).comp continuous_real_toNNReal)
  unfold filtered
  rw [Real.toNNReal_coe,vectorSegmentLp_velocity_eq_brownian_sub_convolution ι γ hγ,
    map_sub,map_smul,← (inputLift c γ).intervalIntegral_comp_comm (f := fun s : ℝ =>
      Real.exp (-γ*((h : ℝ)-s)) • vectorBrownianIncrementLp ι ((n : ℝ≥0)*h) s.toNNReal)
      (hc.intervalIntegrable _ _)]
  unfold ouInputIncrement
  rw [← input_eq_globalInput_increment c γ h n h h.coe_nonneg]
  change input c γ h n h - γ • (∫ s in 0..(h : ℝ), Real.exp (-γ*((h : ℝ)-s)) •
      (globalInput c γ ((n : ℝ)*(h : ℝ)+s)-globalInput c γ ((n : ℝ)*(h : ℝ)))) = _
  have hend : inputLift c γ (vectorBrownianIncrementLp ι ((n : ℝ≥0)*h) h) = input c γ h n h := by
    simp only [input,Real.toNNReal_coe]
  rw [hend]
  apply congrArg (fun z : Lp (H ι) 2 (probability c) => input c γ h n h - γ • z)
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le h.coe_nonneg] at hs
  dsimp only
  rw [← input_eq_globalInput_increment c γ h n s hs.1,map_smul]
  rfl

/-- The actual OU response on the extension has the original source representative. -/
theorem ouInputIncrement_globalInput_coe (c : ULA.Coupling μ π) (γ : ℝ) (hγ : 0 ≤ γ)
    (h : ℝ≥0) (n : ℕ) :
    ouInputIncrement γ (globalInput c γ) ((n : ℝ)*(h : ℝ)) h =ᵐ[probability c]
      fun p : Sample ι => (Real.sqrt (2*γ) • vectorSegmentLp ι (psi γ 0)
        (continuous_psi γ 0) ((n : ℝ≥0)*h) h) p.2.2 := by
  rw [ouInputIncrement_globalInput c γ hγ]
  have he : filtered c γ h n h = brownianLift c (Real.sqrt (2*γ) •
      vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h) := by
    unfold filtered inputLift
    simp only [Real.toNNReal_coe,smul_apply,map_smul]
  rw [he]
  exact brownianLift_coe c _

/-- The initial reference and the whole actual OU innovation stream have the exact independent thermal product law. -/
theorem initial_ouInput_jointLaw (c : ULA.Coupling μ π) (hπ : MemLp (id : H ι → H ι) 2 π)
    (γ : ℝ) (hγ : 0 ≤ γ) (h : ℝ≥0) :
    HasLaw (fun p : Sample ι => (lpPhaseCoe (probability c) (referenceInitial c hπ) p,
      fun k : ℕ => ouInputIncrement γ (globalInput c γ) ((k : ℝ)*(h : ℝ)) h p))
      (((stdGaussian (H ι)).prod π).prod (Measure.infinitePi (fun _ : ℕ =>
        (stdGaussian (H ι)).map (fun x => Real.sqrt (1-(psi γ 0 h)^2) • x)))) (probability c) := by
  haveI : IsProbabilityMeasure π := by
    have hl : HasLaw (fun p : Sample ι => p.1.2) π (probability c) :=
      ⟨(measurable_fst.snd).aemeasurable,ULA.initialExtension_reference c (GenericCanonicalSource.canonicalSourceProbability ι)⟩
    exact hl.isProbabilityMeasure_iff.mp inferInstance
  let η := (stdGaussian (H ι)).map (fun x => Real.sqrt (1-(psi γ 0 h)^2) • x)
  letI : IsProbabilityMeasure η := (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  let W : ULA.CanonicalBrownian.VectorSample ι → ℕ → H ι := fun ω k =>
    (Real.sqrt (2*γ) • vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((k : ℝ≥0)*h) h) ω
  have hW : Measurable W := measurable_pi_iff.mpr fun _ => (Lp.stronglyMeasurable _).measurable
  have hj := jointLaw_product_source ((stdGaussian (H ι)).prod π)
    (ULA.CanonicalBrownian.vectorProbability ι) η W hW (GenericCanonicalSource.vectorOU_grid_hasLaw ι γ hγ h)
  have hp := hj.comp (initialPhase_brownian_jointLaw c)
  apply hp.congr
  filter_upwards [referenceInitial_coe c hπ,ae_all_iff.mpr (ouInputIncrement_globalInput_coe c γ hγ h)]
    with p hinit hnoise
  exact Prod.ext hinit (funext hnoise)

end KineticLangevin.GenericCanonicalCoupling

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.GenericCanonicalCoupling
open BrownianConvolution
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ π : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The actual KLMC position law from an independent Gaussian-velocity and canonical Brownian source. -/
def klmcLaw (f : H ι → ℝ) (γ : ℝ) (h : ℝ≥0) (μ : Measure (H ι)) (n : ℕ) : Measure (H ι) :=
  productKLMCLaw (GenericCanonicalSource.canonicalSourceProbability ι) f γ h μ Prod.fst
    (fun k p => GenericCanonicalSource.canonicalKLMCInnovation ι γ h k p.2) n

/-- The constructed numerical chain has one actual output law for all initial transport couplings. -/
theorem numericalChain_outputLaw (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    (probability c).map (numericalChain c hc hπ f M hLip γ h n).2 = klmcLaw f γ h μ n := by
  have hn : innovation c γ h = extensionInnovation (GenericCanonicalSource.canonicalSourceProbability ι) c
      (fun k p => GenericCanonicalSource.canonicalKLMCInnovation ι γ h k p.2)
      (fun k => (GenericCanonicalSource.canonicalSourceInnovation_memLp ι γ h k).1)
      (fun k => (GenericCanonicalSource.canonicalSourceInnovation_memLp ι γ h k).2) :=
    funext (innovation_eq_extensionInnovation c γ h)
  unfold numericalChain numericalInitial initialVelocity
  rw [hn]
  exact product_klmcChain_outputLaw (GenericCanonicalSource.canonicalSourceProbability ι) c hc hπ f M hLip γ h
    Prod.fst (GenericCanonicalSource.canonicalSourceVelocity_memLp ι) (fun k p => GenericCanonicalSource.canonicalKLMCInnovation ι γ h k p.2)
    (fun k => (GenericCanonicalSource.canonicalSourceInnovation_memLp ι γ h k).1)
    (fun k => (GenericCanonicalSource.canonicalSourceInnovation_memLp ι γ h k).2) n

/-- State the sole remaining probabilistic reference-law property on the actual full constructed flow. -/
def GlobalReferenceStationary (c : ULA.Coupling μ π) (hπ : MemLp (id : H ι → H ι) 2 π)
    (f : H ι → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f)) : Prop :=
  ∀ T (hT : 0 ≤ T) t, t ∈ Icc 0 T →
    HasLaw (fun p => lpPhaseCoe (probability c) (globalReferenceFlow c hπ f M γ hLip T hT t) p)
      ((stdGaussian (H ι)).prod π) (probability c)

/-- A stationary actual global phase law supplies the stationary grid position law. -/
theorem referenceChain_position_law (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0)
    (hglobal : GlobalReferenceStationary c hπ f M γ hLip) (n : ℕ) :
    (probability c).map (referenceChain c hπ f M γ hLip h n).2 = π := by
  haveI : IsProbabilityMeasure π := by
    have hl : HasLaw (fun p : Sample ι => p.1.2) π (probability c) :=
      ⟨(measurable_fst.snd).aemeasurable,ULA.initialExtension_reference c (GenericCanonicalSource.canonicalSourceProbability ι)⟩
    exact hl.isProbabilityMeasure_iff.mp inferInstance
  let T : ℝ := (n : ℝ)*(h : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  rw [referenceChain_eq_globalReferenceFlow c hπ f M γ hLip h T hT n le_rfl]
  have hl := hglobal T hT T ⟨hT,le_rfl⟩
  have hp : HasLaw Prod.snd π ((stdGaussian (H ι)).prod π) := measurePreserving_snd.hasLaw
  exact (hp.comp hl).map_eq

/-- The stationary full phase law also supplies Gaussian velocities at every intermediate reference time. -/
theorem referenceSegment_velocity_law (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0)
    (hglobal : GlobalReferenceStationary c hπ f M γ hLip)
    (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 (h : ℝ)) :
    HasLaw ((referenceSegment c hπ f M γ hLip h n t).1) (stdGaussian (H ι)) (probability c) := by
  have hπprob : IsProbabilityMeasure π := by
    have hxl : HasLaw (fun p : Sample ι => p.1.2) π (probability c) :=
      ⟨(measurable_fst.snd).aemeasurable,ULA.initialExtension_reference c (GenericCanonicalSource.canonicalSourceProbability ι)⟩
    exact hxl.isProbabilityMeasure_iff.mp inferInstance
  let T : ℝ := ((n : ℝ)+1)*(h : ℝ)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have htime : (n : ℝ)*(h : ℝ)+t ∈ Icc 0 T := by
    constructor
    · exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) h.coe_nonneg) ht.1
    · dsimp [T]; nlinarith [ht.2]
  rw [referenceSegment_eq_globalReferenceFlow c hπ f M γ hLip h T hT n le_rfl t ht]
  have hp : HasLaw Prod.fst (stdGaussian (H ι)) ((stdGaussian (H ι)).prod π) :=
    measurePreserving_fst.hasLaw
  exact hp.comp (hglobal T hT _ htime)

/-- The initial L² position discrepancy is the actual cost of the supplied transport plan. -/
theorem initial_position_cost (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    ‖(numericalChain c hc hπ f M hLip γ h 0).2-(referenceChain c hπ f M γ hLip h 0).2‖ =
      (ULA.couplingCost c.joint).toReal := by
  exact ULA.initialExtension_lp_cost c (GenericCanonicalSource.canonicalSourceProbability ι) hc hπ

/-- The first-order KLMC bound for one actual initial coupling, conditional only on stationarity of the actual full reference flow. -/
theorem klmc_bound_of_globalStationarity (c : ULA.Coupling μ π)
    (hc : ULA.couplingCost c.joint ≠ ⊤) (hπ : MemLp (id : H ι → H ι) 2 π)
    (f : H ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 < m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m+(M : ℝ) ≤ (γ : ℝ)^2)
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (hstep : 4*(γ : ℝ)*(M : ℝ)*(h : ℝ) ≤ m)
    (hglobal : GlobalReferenceStationary c hπ f M γ hLip) (n : ℕ) :
    ULA.wasserstein2Real (klmcLaw f γ h μ n) π ≤
      Real.sqrt 2 * (1-3*m*(h : ℝ)/(4*(γ : ℝ)))^n * (ULA.couplingCost c.joint).toReal +
        (M : ℝ)*(h : ℝ)*Real.sqrt (2*(Fintype.card ι : ℝ))/m := by
  rcases segments_spec c hc hπ f M γ hLip h with
    ⟨hA,hZ,hB,hA0,hZ0,hZh,hupdate,heA,heZ,hmild,hkin,hvelocity⟩
  have hb := lp_klmc_reference_wasserstein_bound (probability c) f m M γ hdiff hsc hLip hmM hm
    hγ hfriction h hh hstep (numericalChain c hc hπ f M hLip γ h)
    (referenceChain c hπ f M γ hLip h) (auxiliarySegment c hc hπ f M γ hLip h)
    (referenceSegment c hπ f M γ hLip h) (fun k t => (input c γ h k t,0)) (filtered c γ h)
    hA hZ hB hA0 hZ0 hZh hupdate heA heZ hmild hkin
    (referenceSegment_velocity_law c hπ f M γ hLip h hglobal)
    π (referenceChain_position_law c hπ f M γ hLip h hglobal) hvelocity n
  rw [numericalChain_outputLaw c hc hπ f M hLip γ h n,initial_position_cost c hc hπ f M γ hLip h] at hb
  simpa only [] using hb

/-- The output has finite transport distance, proved from actual square-integrable coupled states. -/
theorem klmcLaw_wasserstein2_ne_top (hπ : MemLp (id : H ι → H ι) 2 π)
    (f : H ι → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0)
    (hfinite : ULA.wasserstein2 μ π ≠ ⊤)
    (hglobal : ∀ c : ULA.Coupling μ π, GlobalReferenceStationary c hπ f M γ hLip) (n : ℕ) :
    ULA.wasserstein2 (klmcLaw f γ h μ n) π ≠ ⊤ := by
  obtain ⟨c,hc⟩ := ULA.exists_finiteCost_coupling μ π hfinite
  have hb := ULA.wasserstein2_le_Lp_cost (probability c)
    (numericalChain c (ne_of_lt hc) hπ f M hLip γ h n).2
    (referenceChain c hπ f M γ hLip h n).2
  rw [numericalChain_outputLaw c (ne_of_lt hc) hπ f M hLip γ h n,
    referenceChain_position_law c hπ f M γ hLip h (hglobal c) n] at hb
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb

/-- Taking the genuine transport infimum gives the paper's KLMC bound with the true initial Wasserstein distance. -/
theorem klmc_wasserstein_bound_of_globalStationarity
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 < m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m+(M : ℝ) ≤ (γ : ℝ)^2)
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (hstep : 4*(γ : ℝ)*(M : ℝ)*(h : ℝ) ≤ m)
    (hfinite : ULA.wasserstein2 μ π ≠ ⊤)
    (hglobal : ∀ c : ULA.Coupling μ π, GlobalReferenceStationary c hπ f M γ hLip) (n : ℕ) :
    ULA.wasserstein2Real (klmcLaw f γ h μ n) π ≤
      Real.sqrt 2 * (1-3*m*(h : ℝ)/(4*(γ : ℝ)))^n * ULA.wasserstein2Real μ π +
        (M : ℝ)*(h : ℝ)*Real.sqrt (2*(Fintype.card ι : ℝ))/m := by
  obtain ⟨hc,hs⟩ := kinetic_scalar_conditions m M γ h hm hmM hγ hfriction hh.le hstep
  have hcoeff := firstOrder_coefficient_bound (m/(γ : ℝ)) M h (div_nonneg hm.le hγ.le)
    M.coe_nonneg h.coe_nonneg hc hs
  have hq : 0 ≤ 1-3*m*(h : ℝ)/(4*(γ : ℝ)) := by
    have he := Real.exp_pos (-(m/(γ : ℝ))*(h : ℝ))
    have hp : 0 ≤ (3/4 : ℝ)*(M : ℝ)*(h : ℝ)^2 := by positivity
    have hid : 1-3*m*(h : ℝ)/(4*(γ : ℝ)) = 1-(3/4 : ℝ)*(m/(γ : ℝ))*(h : ℝ) := by ring
    rw [hid]
    linarith
  let a : ℝ≥0 := ⟨Real.sqrt 2 * (1-3*m*(h : ℝ)/(4*(γ : ℝ)))^n,by positivity⟩
  let b : ℝ≥0 := ⟨(M : ℝ)*(h : ℝ)*Real.sqrt (2*(Fintype.card ι : ℝ))/m,by positivity⟩
  apply ULA.wasserstein2_affine_bound_real_of_finite_couplings μ π (klmcLaw f γ h μ n) π a b hfinite
    (klmcLaw_wasserstein2_ne_top hπ f M γ hLip h hfinite hglobal n)
  intro c hc
  exact klmc_bound_of_globalStationarity c hc hπ f m M γ hdiff hsc hLip hmM hm hγ hfriction h hh hstep (hglobal c) n

end KineticLangevin.GenericCanonicalCoupling

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.GenericCanonicalCoupling
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The actual canonical global reference remains Gibbs distributed on every initial coupling extension. -/
theorem globalReferenceFlow_stationary
    (f : H ι → ℝ) (m : ℝ) (hm : 0 < m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f))
    (c : ULA.Coupling μ (ULA.gibbsMeasure f))
    (hπ : MemLp (id : H ι → H ι) 2 (ULA.gibbsMeasure f)) :
    GlobalReferenceStationary c hπ f M γ hLip := by
  intro T hT t ht
  let Y := globalReferenceFlow c hπ f M γ hLip T hT
  have hs := globalReferenceFlow_spec c hπ f M γ hLip T hT
  have hjoint : ∀ h : ℝ≥0, HasLaw
      (fun p => (lpPhaseCoe (probability c) (referenceInitial c hπ) p,
        fun k : ℕ => ouInputIncrement γ (globalInput c γ) ((k : ℝ)*h) h p))
      ((kineticGibbsTarget f).prod (Measure.infinitePi (fun _ : ℕ => ouThermalLaw (E := H ι) γ h)))
      (probability c) := by
    intro h
    simpa only [kineticGibbsTarget,ouThermalLaw] using initial_ouInput_jointLaw c hπ γ γ.coe_nonneg h
  have heq : ∀ s ∈ Icc 0 t, Y s-referenceInitial c hπ =
      -(∫ r in 0..s,kineticNegativeDrift (ULA.lpDrift (probability c) (gradient f) hLip) γ 1 (Y r)) +
        (globalInput c γ s,0) := by
    intro s hs'
    simpa only [hs.2.1] using hs.2.2 s ⟨hs'.1,hs'.2.trans ht.2⟩
  have hl := kinetic_integral_stationary_of_jointNoise (probability c) f m hm M γ hf hsc hLip
    (referenceInitial c hπ) (globalInput c γ) (continuous_globalInput c γ) (globalInput_zero c γ)
    hjoint Y hs.1 (⟨t,ht.1⟩ : ℝ≥0) heq
  exact ⟨(measurable_lpPhaseCoe (probability c) (Y t)).aemeasurable,hl⟩

/-- Dalalyan--Riou-Durand's first-order KLMC Wasserstein estimate for the actual canonical sampler.
All continuous reference laws, local-error identities and initial-coupling infima are proved internally. -/
theorem klmc_wasserstein_bound
    (f : H ι → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ)) (hm : 0 < m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m+(M : ℝ) ≤ (γ : ℝ)^2)
    (h : ℝ≥0) (hh : 0 < (h : ℝ)) (hstep : 4*(γ : ℝ)*(M : ℝ)*(h : ℝ) ≤ m)
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f) ≠ ⊤) (n : ℕ) :
    ULA.wasserstein2Real (klmcLaw f γ h μ n) (ULA.gibbsMeasure f) ≤
      Real.sqrt 2 * (1-3*m*(h : ℝ)/(4*(γ : ℝ)))^n * ULA.wasserstein2Real μ (ULA.gibbsMeasure f) +
        (M : ℝ)*(h : ℝ)*Real.sqrt (2*(Fintype.card ι : ℝ))/m := by
  have hπ : MemLp (id : H ι → H ι) 2 (ULA.gibbsMeasure f) := ULA.memLp_id_gibbsMeasure f m hm hf hsc
  exact klmc_wasserstein_bound_of_globalStationarity hπ f m M γ hf hsc hLip hmM hm hγ hfriction
    h hh hstep hfinite (fun c => globalReferenceFlow_stationary f m hm M γ hf hsc hLip c hπ) n

end KineticLangevin.GenericCanonicalCoupling