import KineticLangevin.CanonicalPastFuture
import KineticLangevin.FreeOUCorrection

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace KineticLangevin.GenericCanonicalCoupling
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {μ : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The actual free OU response built from a reference-grid velocity and its fresh Brownian interval is standard Gaussian. -/
theorem referenceChain_freeOUResponse_hasLaw
    (f : H ι → ℝ) (m : ℝ) (hm : 0<m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (c : ULA.Coupling μ (ULA.gibbsMeasure f))
    (hπ : MemLp (id : H ι → H ι) 2 (ULA.gibbsMeasure f))
    (h : ℝ≥0) (n : ℕ) (r : ℝ) (hr : 0≤r) :
    HasLaw (freeOUResponse (probability c) (inputLift c γ)
      (referenceChain c hπ f M γ hLip h n).1 γ ((n : ℝ≥0)*h) 0 r)
      (stdGaussian (H ι)) (probability c) := by
  let N := fun s : ℝ ↦ inputLift c γ
    (BrownianConvolution.vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) ((n : ℝ≥0)*h) s.toNNReal)
  have hj := referenceChain_velocity_future_jointLaw f m hm M γ hf hsc hLip c hπ h n r.toNNReal
  rw [Real.coe_toNNReal r hr] at hj
  exact freeOUVelocity_hasLaw (probability c) γ γ.coe_nonneg
    (referenceChain c hπ f M γ hLip h n).1 N r hr hj

/-- The same marginal statement holds at every point of the actual global reference solution. -/
theorem globalReferenceFlow_freeOUResponse_hasLaw
    (f : H ι → ℝ) (m : ℝ) (hm : 0<m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (c : ULA.Coupling μ (ULA.gibbsMeasure f))
    (hπ : MemLp (id : H ι → H ι) 2 (ULA.gibbsMeasure f))
    (T : ℝ) (hT : 0≤T) (a : ℝ≥0) (ha : (a : ℝ)≤T) (r : ℝ) (hr : 0≤r) :
    HasLaw (freeOUResponse (probability c) (inputLift c γ)
      (globalReferenceFlow c hπ f M γ hLip T hT a).1 γ a 0 r)
      (stdGaussian (H ι)) (probability c) := by
  let N := fun s : ℝ ↦ inputLift c γ
    (BrownianConvolution.vectorSegmentLp ι (psi γ 0) (continuous_psi γ 0) a s.toNNReal)
  have hj := globalReferenceFlow_velocity_future_jointLaw f m hm M γ hf hsc hLip c hπ T hT a r.toNNReal ha
  rw [Real.coe_toNNReal r hr] at hj
  exact freeOUVelocity_hasLaw (probability c) γ γ.coe_nonneg
    (globalReferenceFlow c hπ f M γ hLip T hT a).1 N r hr hj

end KineticLangevin.GenericCanonicalCoupling
