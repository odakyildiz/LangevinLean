import KineticLangevin.CanonicalFreeOU
import KineticLangevin.CorrectedStep

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace KineticLangevin.GenericCanonicalCoupling
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {μ π : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The actual canonical reference segment is continuous and joins its two consecutive reference states. -/
theorem referenceSegment_spec (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι→ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) (n : ℕ) :
    Continuous (referenceSegment c hπ f M γ hLip h n) ∧
      referenceSegment c hπ f M γ hLip h n 0=referenceChain c hπ f M γ hLip h n ∧
      referenceSegment c hπ f M γ hLip h n h=referenceChain c hπ f M γ hLip h (n+1) ∧
      ∀ t∈Icc 0 (h : ℝ),referenceSegment c hπ f M γ hLip h n t-referenceSegment c hπ f M γ hLip h n 0=
        -(∫ s in 0..t,kineticNegativeDrift (ULA.lpDrift (probability c) (gradient f) hLip) γ 1
          (referenceSegment c hπ f M γ hLip h n s))+(input c γ h n t,0) := by
  simpa only [referenceSegment,referenceChain,NNReal.coe_one] using
    kineticReferenceSegment_spec (ULA.lpDrift (probability c) (gradient f) hLip) M γ 1
      (ULA.lpDrift_lipschitz _ _ hLip) h h.coe_nonneg (referenceInitial c hπ)
      (input c γ h) (continuous_input c γ h) (input_zero c γ h) n

/-- Every actual reference segment has the true free-OU force-mild equation. -/
theorem referenceSegment_mild (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι→ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) (n : ℕ) (t : ℝ) (ht : t∈Icc 0 (h : ℝ)) :
    (referenceSegment c hπ f M γ hLip h n t).1=
      freeOUResponse (probability c) (inputLift c γ)
        (referenceSegment c hπ f M γ hLip h n 0).1 γ ((n : ℝ≥0)*h) 0 t-
      dampedIntegral γ (fun s ↦ ULA.lpDrift (probability c) (gradient f) hLip
        (referenceSegment c hπ f M γ hLip h n s).2) t := by
  have hs := referenceSegment_spec c hπ f M γ hLip h n
  have hm := kinetic_integral_mild (ULA.lpDrift (probability c) (gradient f) hLip) γ 1 t ht.1
    (referenceSegment c hπ f M γ hLip h n) (input c γ h n) (filtered c γ h n) hs.1
    (ULA.lpDrift_lipschitz _ _ hLip).continuous (continuous_filtered c γ h n)
    (fun s hs' ↦ hs.2.2.2 s ⟨hs'.1,hs'.2.trans ht.2⟩)
    (fun s hs' ↦ filtered_integral_equation c γ γ.coe_nonneg h n s hs'.1)
  simp only [one_smul] at hm
  dsimp only [freeOUResponse,dampedIntegral,filtered] at *
  rw [hm]
  abel

/-- The actual reference position is the ordinary primitive of its actual velocity. -/
theorem referenceSegment_kinematic (c : ULA.Coupling μ π)
    (hπ : MemLp (id : H ι → H ι) 2 π) (f : H ι→ℝ) (M γ : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (h : ℝ≥0) (n : ℕ) (t : ℝ) (ht : t∈Icc 0 (h : ℝ)) :
    (referenceSegment c hπ f M γ hLip h n t).2-(referenceSegment c hπ f M γ hLip h n 0).2=
      ∫ s in 0..t,(referenceSegment c hπ f M γ hLip h n s).1 := by
  have hs := referenceSegment_spec c hπ f M γ hLip h n
  exact kinetic_integral_kinematic (ULA.lpDrift (probability c) (gradient f) hLip) γ 1 h
    (referenceSegment c hπ f M γ hLip h n) (input c γ h n) hs.1
    (ULA.lpDrift_lipschitz _ _ hLip).continuous hs.2.2.2 t ht

/-- The entire actual canonical segment has the kinetic Gibbs phase law, including its endpoints. -/
theorem referenceSegment_stationary
    (f : H ι→ℝ) (m : ℝ) (hm : 0<m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (c : ULA.Coupling μ (ULA.gibbsMeasure f))
    (hπ : MemLp (id : H ι→H ι) 2 (ULA.gibbsMeasure f))
    (h : ℝ≥0) (n : ℕ) (t : ℝ) (ht : t∈Icc 0 (h : ℝ)) :
    HasLaw (lpPhaseCoe (probability c) (referenceSegment c hπ f M γ hLip h n t))
      (kineticGibbsTarget f) (probability c) := by
  let T : ℝ := ((n : ℝ)+1)*(h : ℝ)
  have hn : 0≤(n : ℝ) := Nat.cast_nonneg n
  have hT : 0≤T := mul_nonneg (by linarith) h.coe_nonneg
  have htime : (n : ℝ)*(h : ℝ)+t∈Icc 0 T := by
    dsimp [T]
    constructor
    · exact add_nonneg (mul_nonneg hn h.coe_nonneg) ht.1
    · nlinarith [ht.2]
  rw [referenceSegment_eq_globalReferenceFlow c hπ f M γ hLip h T hT n le_rfl t ht]
  exact globalReferenceFlow_stationary f m hm M γ hf hsc hLip c hπ T hT _ htime

end KineticLangevin.GenericCanonicalCoupling
