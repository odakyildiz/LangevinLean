import KineticLangevin.CoupledSegments
import KineticLangevin.VectorSegmentEquations
import KineticLangevin.ProductLaw

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.CanonicalCoupling
open BrownianConvolution
abbrev H (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Sample (d : ℕ) := (H d × H d) × (H d × ULA.CanonicalBrownian.VectorSample (Fin d))
variable {d : ℕ} {μ π : Measure (H d)} [IsProbabilityMeasure μ]

/-- The actual initial-position coupling, extended by independent Gaussian velocity and vector Brownian source. -/
abbrev probability (c : ULA.Coupling μ π) := ULA.initialExtension c (canonicalSourceProbability d)

instance probability_isProbabilityMeasure (c : ULA.Coupling μ π) : IsProbabilityMeasure (probability c) :=
  ULA.initialExtension_isProbabilityMeasure c _

local instance couplingProbability (c : ULA.Coupling μ π) : IsProbabilityMeasure c.joint := c.isProbabilityMeasure

/-- Pull the canonical vector Brownian L² space onto the concrete initial-coupling extension. -/
def brownianLift (c : ULA.Coupling μ π) :
    Lp (H d) 2 (ULA.CanonicalBrownian.vectorProbability (Fin d)) →L[ℝ] Lp (H d) 2 (probability c) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun p : Sample d => p.2.2)
    ((measurePreserving_snd : MeasurePreserving Prod.snd (canonicalSourceProbability d)
      (ULA.CanonicalBrownian.vectorProbability (Fin d))).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd (probability c) (canonicalSourceProbability d)))).toContinuousLinearMap

/-- The source lift is the actual Brownian-source projection of the product extension. -/
theorem brownianLift_coe (c : ULA.Coupling μ π)
    (Z : Lp (H d) 2 (ULA.CanonicalBrownian.vectorProbability (Fin d))) :
    brownianLift c Z =ᵐ[probability c] fun p : Sample d => Z p.2.2 :=
  Lp.coeFn_compMeasurePreserving Z
    ((measurePreserving_snd : MeasurePreserving Prod.snd (canonicalSourceProbability d)
      (ULA.CanonicalBrownian.vectorProbability (Fin d))).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd (probability c) (canonicalSourceProbability d)))

/-- Include the fluctuation-dissipation amplitude in the same continuous linear source lift. -/
def inputLift (c : ULA.Coupling μ π) (γ : ℝ) := Real.sqrt (2*γ) • brownianLift c

/-- The actual scaled Brownian increment used by both exact coupling segments at iteration `n`. -/
def input (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) (t : ℝ) : Lp (H d) 2 (probability c) :=
  inputLift c γ (vectorBrownianIncrementLp (Fin d) ((n : ℝ≥0)*h) t.toNNReal)

/-- The same Brownian interval filtered by the exact exponential velocity response. -/
def filtered (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) (t : ℝ) : Lp (H d) 2 (probability c) :=
  inputLift c γ (vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) t.toNNReal)

/-- Unscaled correlated velocity-position responses for the implemented KLMC update. -/
def innovation (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    Lp (H d) 2 (probability c) × Lp (H d) 2 (probability c) :=
  (brownianLift c (vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h),
   brownianLift c (vectorSegmentLp (Fin d) (psi γ 1) (continuous_psi γ 1) ((n : ℝ≥0)*h) h))

theorem continuous_input (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    Continuous (input c γ h n) :=
  (inputLift c γ).continuous.comp ((continuous_vectorBrownianIncrementLp (Fin d) _).comp continuous_real_toNNReal)

theorem continuous_filtered (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    Continuous (filtered c γ h n) :=
  (inputLift c γ).continuous.comp
    ((continuous_vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) _).comp continuous_real_toNNReal)

@[simp] theorem input_zero (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) : input c γ h n 0 = 0 := by
  unfold input vectorBrownianIncrementLp segmentBrownianLp
  simp only [Real.toNNReal_zero,add_zero,sub_self,map_zero]

/-- The constructed filtered input satisfies the exact Brownian integral equation on every step. -/
theorem filtered_integral_equation (c : ULA.Coupling μ π) (γ : ℝ) (hγ : 0 ≤ γ)
    (h : ℝ≥0) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    filtered c γ h n t = input c γ h n t - γ • ∫ s in 0..t, filtered c γ h n s := by
  have hc : Continuous (fun s : ℝ =>
      vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) s.toNNReal) :=
    (continuous_vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) _).comp continuous_real_toNNReal
  unfold filtered input
  rw [vectorSegmentLp_integral_equation (Fin d) γ hγ,Real.coe_toNNReal t ht,map_sub,map_smul,
    ← (inputLift c γ).intervalIntegral_comp_comm (f := fun s : ℝ =>
      vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) s.toNNReal)
      (hc.intervalIntegrable _ _)]

/-- Integrating the actual filtered input gives exactly the scaled positional Gaussian innovation. -/
theorem integral_filtered (c : ULA.Coupling μ π) (γ : ℝ) (hγ : 0 ≤ γ)
    (h : ℝ≥0) (n : ℕ) :
    (∫ s in 0..(h : ℝ), filtered c γ h n s) = Real.sqrt (2*γ) • (innovation c γ h n).2 := by
  have hc : Continuous (fun s : ℝ =>
      vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) s.toNNReal) :=
    (continuous_vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) _).comp continuous_real_toNNReal
  unfold filtered innovation
  rw [(inputLift c γ).intervalIntegral_comp_comm (f := fun s : ℝ =>
      vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) s.toNNReal)
      (hc.intervalIntegrable _ _),← vectorSegmentLp_primitive (Fin d) γ hγ]
  rfl

/-- The endpoint velocity response is exactly the scaled velocity Gaussian innovation. -/
theorem filtered_endpoint (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    filtered c γ h n h = Real.sqrt (2*γ) • (innovation c γ h n).1 := by
  unfold filtered innovation inputLift
  simp only [Real.toNNReal_coe,ContinuousLinearMap.smul_apply]

/-- The actual exponential chain is precisely the implemented KLMC chain with the same canonical innovations. -/
theorem exponentialInputChain_eq_klmcChain (c : ULA.Coupling μ π)
    (g : Lp (H d) 2 (probability c) → Lp (H d) 2 (probability c))
    (γ : ℝ) (hγ : 0 ≤ γ) (h : ℝ≥0)
    (initial : Lp (H d) 2 (probability c) × Lp (H d) 2 (probability c)) (n : ℕ) :
    exponentialInputChain g γ h initial (filtered c γ h) n =
      klmcChain g γ h initial (innovation c γ h) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exponentialInputChain_succ,klmcChain_succ,ih,filtered_endpoint,integral_filtered c γ hγ]
    rfl

/-- The L² innovations on the coupling extension are the pointwise canonical Brownian innovations. -/
theorem innovation_coe (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    (fun p : Sample d => lpPhaseCoe (probability c) (innovation c γ h n) p)
      =ᵐ[probability c] fun p => canonicalKLMCInnovation d γ h n p.2.2 := by
  have hp := ((measurePreserving_snd : MeasurePreserving Prod.snd (canonicalSourceProbability d)
      (ULA.CanonicalBrownian.vectorProbability (Fin d))).comp
      (measurePreserving_snd : MeasurePreserving Prod.snd (probability c) (canonicalSourceProbability d))).quasiMeasurePreserving.ae_eq_comp
    (vectorSegmentLp_klmcInnovation_coe d γ h n)
  filter_upwards [brownianLift_coe c (vectorSegmentLp (Fin d) (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) h),
    brownianLift_coe c (vectorSegmentLp (Fin d) (psi γ 1) (continuous_psi γ 1) ((n : ℝ≥0)*h) h),hp]
    with p hv hx hp
  change (brownianLift c _ p,brownianLift c _ p) = _
  rw [hv,hx]
  exact hp

/-- The actual Brownian L² innovation is exactly the generic product-law layer's innovation variable. -/
theorem innovation_eq_extensionInnovation (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    innovation c γ h n =
      extensionInnovation (canonicalSourceProbability d) c
        (fun k p => canonicalKLMCInnovation d γ h k p.2)
        (fun k => (canonicalSourceInnovation_memLp d γ h k).1)
        (fun k => (canonicalSourceInnovation_memLp d γ h k).2) n := by
  have hmine := innovation_coe c γ h n
  have hprod := extensionInnovation_coe (canonicalSourceProbability d) c
    (fun k p => canonicalKLMCInnovation d γ h k p.2)
    (fun k => (canonicalSourceInnovation_memLp d γ h k).1)
    (fun k => (canonicalSourceInnovation_memLp d γ h k).2) n
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [hmine,hprod] with p hm hp
    exact congrArg Prod.fst (hm.trans hp.symm)
  · apply Lp.ext
    filter_upwards [hmine,hprod] with p hm hp
    exact congrArg Prod.snd (hm.trans hp.symm)

/-- The shared initial Gaussian velocity on the concrete coupling extension. -/
def initialVelocity (c : ULA.Coupling μ π) : Lp (H d) 2 (probability c) :=
  extensionVelocity (canonicalSourceProbability d) c Prod.fst (canonicalSourceVelocity_memLp d)

/-- The actual numerical initial state has the prescribed first position marginal. -/
def numericalInitial (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H d → H d) 2 π) :
    Lp (H d) 2 (probability c) × Lp (H d) 2 (probability c) :=
  (initialVelocity c,ULA.initialExtension_lpInitial c (canonicalSourceProbability d) hc hπ)

/-- The reference uses the second position marginal and the identical velocity variable. -/
def referenceInitial (c : ULA.Coupling μ π) (hπ : MemLp (id : H d → H d) 2 π) :
    Lp (H d) 2 (probability c) × Lp (H d) 2 (probability c) :=
  (initialVelocity c,ULA.initialExtension_lpReference c (canonicalSourceProbability d) hπ)

/-- The initial reference phase is the explicit Gaussian velocity and second coupling coordinate. -/
theorem referenceInitial_coe (c : ULA.Coupling μ π) (hπ : MemLp (id : H d → H d) 2 π) :
    (fun p : Sample d => lpPhaseCoe (probability c) (referenceInitial c hπ) p)
      =ᵐ[probability c] fun p => (p.2.1,p.1.2) := by
  filter_upwards [extensionVelocity_coe (canonicalSourceProbability d) c Prod.fst (canonicalSourceVelocity_memLp d),
    (ULA.initialExtension_memLp_reference c (canonicalSourceProbability d) hπ).coeFn_toLp]
    with p hv hx
  exact Prod.ext hv hx

/-- The actual reference initial phase has the canonical product target law. -/
theorem referenceInitial_law (c : ULA.Coupling μ π) (hπ : MemLp (id : H d → H d) 2 π) :
    HasLaw (fun p : Sample d => lpPhaseCoe (probability c) (referenceInitial c hπ) p)
      ((stdGaussian (H d)).prod π) (probability c) := by
  have hv : HasLaw (fun p : Sample d => p.2.1) (stdGaussian (H d)) (probability c) :=
    (canonicalSourceVelocity_law d).comp (measurePreserving_snd.hasLaw)
  have hx : HasLaw (fun p : Sample d => p.1.2) π (probability c) :=
    ⟨(measurable_fst.snd).aemeasurable,ULA.initialExtension_reference c (canonicalSourceProbability d)⟩
  have hind : IndepFun (fun p : Sample d => p.2.1) (fun p : Sample d => p.1.2) (probability c) :=
    (indepFun_prod (μ := c.joint) (ν := canonicalSourceProbability d)
      (X := Prod.snd) (Y := Prod.fst) measurable_snd measurable_fst).symm
  exact (hind.hasLaw_prod hv hx).congr (referenceInitial_coe c hπ)

/-- The canonical numerical chain, with the actual lifted original gradient. -/
def numericalChain (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (γ : ℝ) (h : ℝ≥0) :
    ℕ → Lp (H d) 2 (probability c) × Lp (H d) 2 (probability c) :=
  klmcChain (ULA.lpDrift (probability c) (gradient f) hLip) γ h
    (numericalInitial c hc hπ) (innovation c γ h)

/-- The reference's exact segment chain is constructed using the same canonical Brownian increments. -/
def referenceChain (c : ULA.Coupling μ π) (hπ : MemLp (id : H d → H d) 2 π)
    (f : H d → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    ℕ → Lp (H d) 2 (probability c) × Lp (H d) 2 (probability c) :=
  kineticReferenceChain (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz _ _ hLip) h h.coe_nonneg (referenceInitial c hπ)
    (input c γ h) (continuous_input c γ h)

/-- Each actual reference segment starts at its reference chain state. -/
def referenceSegment (c : ULA.Coupling μ π) (hπ : MemLp (id : H d → H d) 2 π)
    (f : H d → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    ℕ → ℝ → Lp (H d) 2 (probability c) × Lp (H d) 2 (probability c) :=
  kineticReferenceSegment (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz _ _ hLip) h h.coe_nonneg (referenceInitial c hπ)
    (input c γ h) (continuous_input c γ h)

/-- Each auxiliary exact segment starts at the implemented numerical state, with the shared canonical input. -/
def auxiliarySegment (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    ℕ → ℝ → Lp (H d) 2 (probability c) × Lp (H d) 2 (probability c) :=
  kineticAuxiliarySegment (ULA.lpDrift (probability c) (gradient f) hLip) M γ
    (ULA.lpDrift_lipschitz _ _ hLip) h h.coe_nonneg (numericalInitial c hc hπ)
    (input c γ h) (filtered c γ h) (continuous_input c γ h)


/-- Every analytic segment requirement of the first-order coupling theorem is furnished by the actual construction. -/
theorem segments_spec (c : ULA.Coupling μ π) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) :
    let S := numericalChain c hc hπ f M hLip γ h
    let R := referenceChain c hπ f M γ hLip h
    let A := auxiliarySegment c hc hπ f M γ hLip h
    let Z := referenceSegment c hπ f M γ hLip h
    let B := filtered c γ h
    let W := fun n t => (input c γ h n t, (0 : Lp (H d) 2 (probability c)))
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

end KineticLangevin.CanonicalCoupling
