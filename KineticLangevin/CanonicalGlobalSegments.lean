import KineticLangevin.CanonicalCoupledSegments
import KineticLangevin.SegmentGlobal

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin.CanonicalCoupling
open BrownianConvolution
variable {d : ℕ} {μ π : Measure (H d)} [IsProbabilityMeasure μ]

/-- The full continuous canonical Brownian input on the actual initial-coupling extension. -/
def globalInput (c : ULA.Coupling μ π) (γ : ℝ) (t : ℝ) : Lp (H d) 2 (probability c) :=
  inputLift c γ (spatialLift (Fin d) (ULA.CanonicalBrownian.valueLp t.toNNReal))

theorem continuous_globalInput (c : ULA.Coupling μ π) (γ : ℝ) : Continuous (globalInput c γ) := by
  have hc : Continuous (ULA.CanonicalBrownian.valueLp) := by
    rw [show ULA.CanonicalBrownian.valueLp = velocityLp 0 from funext velocityLp_zero_friction |>.symm]
    exact continuous_velocityLp 0
  exact (inputLift c γ).continuous.comp ((spatialLift (Fin d)).continuous.comp
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
def globalReferenceFlow (c : ULA.Coupling μ π) (hπ : MemLp (id : H d → H d) 2 π)
    (f : H d → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) : ℝ → Lp (H d) 2 (probability c) × Lp (H d) 2 (probability c) :=
  kineticSegmentFlow (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
    (ULA.lpDrift_lipschitz _ _ hLip) T hT (referenceInitial c hπ)
    (globalInput c γ) (continuous_globalInput c γ)

/-- The full reference flow supplies its actual continuous kinetic integral equation. -/
theorem globalReferenceFlow_spec (c : ULA.Coupling μ π) (hπ : MemLp (id : H d → H d) 2 π)
    (f : H d → ℝ) (M γ : ℝ≥0) (hLip : LipschitzWith M (gradient f))
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
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (M γ : ℝ≥0)
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
    (hπ : MemLp (id : H d → H d) 2 π) (f : H d → ℝ) (M γ : ℝ≥0)
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

end KineticLangevin.CanonicalCoupling
