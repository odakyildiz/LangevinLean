import KineticLangevin.CanonicalKLMC2Law
import KineticLangevin.CanonicalSecondOrderSegments
import KineticLangevin.SecondOrderOneStep

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace KineticLangevin.SecondOrderSource
open GenericCanonicalCoupling
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The direct canonical four-kernel innovation is exactly the analytic lifted four-kernel innovation. -/
theorem extensionInnovation_eq_lifted (c : ULA.Coupling μ π) (γ : ℝ) (h : ℝ≥0) (n : ℕ) :
    extensionInnovation c γ h n =
      liftedKLMC2Noise (GenericCanonicalCoupling.probability c) (brownianLift c) γ ((n : ℝ≥0)*h) h := by
  funext j
  simp only [extensionInnovation,innovationLp,liftedKLMC2Noise,Real.toNNReal_coe]

/-- Every actual canonical KLMC2 step obeys the repaired source recurrence against the same stationary Brownian reference. -/
theorem numericalChain_error_recurrence
    (f : H ι → ℝ) (Hess : H ι → H ι →L[ℝ] H ι) (m : ℝ) (M γ M2 : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hHLip : LipschitzWith M2 Hess)
    (hderiv : ∀ x,HasFDerivAt (gradient f) (Hess x) x)
    (hm : 0<m) (hmM : m≤(M : ℝ)) (hγ : 0<(γ : ℝ)) (hfriction : m+(M : ℝ)≤(γ : ℝ)^2)
    (h : ℝ≥0) (hh : 0<(h : ℝ)) (hstep : 5*(γ : ℝ)*(M : ℝ)*(h : ℝ)≤m)
    (α : ℝ) (hα : 5*(Fintype.card ι : ℝ)≤α)
    (c : ULA.Coupling μ (ULA.gibbsMeasure f)) (hc : ULA.couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (id : H ι → H ι) 2 (ULA.gibbsMeasure f)) (n : ℕ) :
    transformNorm γ 0 (numericalChain c hc hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h (n+1)-
      referenceChain c hπ f M γ hLip h (n+1)) ≤
      (1-m*(h : ℝ)/(2*(γ : ℝ))+(M2 : ℝ)*Real.sqrt α*(h : ℝ)^2/(γ : ℝ))*
        transformNorm γ 0 (numericalChain c hc hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h n-
          referenceChain c hπ f M γ hLip h n)+
      Real.sqrt 2*(h : ℝ)^2*((M : ℝ)-m)*Real.exp (-(α-(Fintype.card ι : ℝ))/8)+
      (h : ℝ)^3/4*((M2 : ℝ)*Real.sqrt ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))+
        (M : ℝ)*Real.sqrt ((M : ℝ)*(Fintype.card ι : ℝ))) := by
  let P := GenericCanonicalCoupling.probability c
  let R := referenceSegment c hπ f M γ hLip h n
  let V := fun t => (R t).1
  let X := fun t => (R t).2
  let w := numericalChain c hc hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h n
  have hs := referenceSegment_spec c hπ f M γ hLip h n
  have hlaw (r : ℝ) (hr : r∈Icc 0 (h : ℝ)) :
      P.map (lpPhaseCoe P (V r,X r))=kineticGibbsTarget f :=
    (referenceSegment_stationary f m hm M γ hf hsc hLip c hπ h n r hr).map_eq
  have hmild (r : ℝ) (hr : r∈Icc 0 (h : ℝ)) :
      V r=freeOUResponse P (Real.sqrt (2*(γ : ℝ)) • brownianLift c) (V 0) γ ((n : ℝ≥0)*h) 0 r-
        dampedIntegral γ (fun s => ULA.lpDrift P (gradient f) hLip (X s)) r :=
    referenceSegment_mild c hπ f M γ hLip h n r hr
  have hkin (r : ℝ) (hr : r∈Icc 0 (h : ℝ)) : X r-X 0=∫ s in 0..r,V s :=
    referenceSegment_kinematic c hπ f M γ hLip h n r hr
  have hGaussian (r : ℝ) (hr : r∈Icc 0 (h : ℝ)) :
      HasLaw (freeOUResponse P (Real.sqrt (2*(γ : ℝ)) • brownianLift c) (V 0) γ ((n : ℝ≥0)*h) 0 r)
        (stdGaussian (H ι)) P := by
    have he : V 0=(referenceChain c hπ f M γ hLip h n).1 := congrArg Prod.fst hs.2.1
    rw [he]
    exact referenceChain_freeOUResponse_hasLaw f m hm M γ hf hsc hLip c hπ h n r hr.1
  have hb := klmc2Step_oneStep_bound P f Hess m γ h α M M2 hm hmM hγ hfriction h.coe_nonneg hstep hα
    hf hsc hLip hHLip hderiv (brownianLift c) ((n : ℝ≥0)*h) V X hs.1.fst hs.1.snd hlaw hmild hkin w hGaussian
  change transformNorm γ 0 (klmc2Step (ULA.lpDrift P (gradient f) hLip)
    (lpHessian P (gradient f) Hess M M2 hLip hHLip hderiv) γ h w
    (liftedKLMC2Noise P (brownianLift c) γ ((n : ℝ≥0)*h) h)-R h) ≤
      _*transformNorm γ 0 (R 0-w)+_+_ at hb
  have hR0 : R 0=referenceChain c hπ f M γ hLip h n := hs.2.1
  have hRh : R h=referenceChain c hπ f M γ hLip h (n+1) := hs.2.2.1
  rw [← extensionInnovation_eq_lifted c γ h n,hR0,hRh] at hb
  have hsym : referenceChain c hπ f M γ hLip h n-w=-(w-referenceChain c hπ f M γ hLip h n) := by abel
  rw [hsym,transformNorm_neg] at hb
  change transformNorm γ 0 (numericalChain c hc hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h (n+1)-
    referenceChain c hπ f M γ hLip h (n+1))≤_ at hb
  exact hb

end KineticLangevin.SecondOrderSource
