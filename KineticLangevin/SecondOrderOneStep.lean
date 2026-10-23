import KineticLangevin.SecondOrderComparison
import KineticLangevin.SecondOrderLpLocal
import KineticLangevin.CorrectedStep

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace KineticLangevin
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The source step restriction gives exactly the local friction restriction in Proposition 2. -/
theorem secondOrder_step_friction_bound (m M γ h : ℝ) (hm : 0<m) (hmM : m≤M)
    (hstep : 5*γ*M*h≤m) : γ*h≤1/5 := by
  have hM : 0<M := hm.trans_le hmM
  have hh : (5*γ*h)*M≤1*M := by nlinarith only [hstep,hmM]
  have hb := (mul_le_mul_iff_left₀ hM).mp hh
  linarith only [hb]

/-- The actual four-kernel implemented KLMC2 step has the source local quarter-bound against an actual stationary mild solution. -/
theorem klmc2Step_stationary_local_bound
    (f : EuclideanSpace ℝ ι → ℝ)
    (H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (m γ T : ℝ) (M M2 : ℝ≥0) (hm : 0<m) (hγ : 0≤γ) (hT : 0≤T)
    (hsmall : γ*T≤1/5)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hH : LipschitzWith M2 H)
    (hderiv : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (R : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P) (a : ℝ≥0)
    (V X : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hV : Continuous V) (hX : Continuous X)
    (hlaw : ∀ t∈Icc 0 T,P.map (lpPhaseCoe P (V t,X t))=kineticGibbsTarget f)
    (hmild : ∀ t∈Icc 0 T,V t=freeOUResponse P (Real.sqrt (2*γ) • R) (V 0) γ a 0 t-
      dampedIntegral γ (fun s ↦ ULA.lpDrift P (gradient f) hLip (X s)) t)
    (hkin : ∀ t∈Icc 0 T,X t-X 0=∫ r in 0..t,V r) :
    let G := ULA.lpDrift P (gradient f) hLip
    let A := lpHessian P (gradient f) H M M2 hLip hH hderiv
    transformNorm γ 0 (klmc2Step G A γ T (V 0,X 0) (liftedKLMC2Noise P R γ a T)-(V T,X T))≤
      T^3/4*((M2 : ℝ)*Real.sqrt ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))+
        (M : ℝ)*Real.sqrt ((M : ℝ)*(Fintype.card ι : ℝ))) := by
  intro G A
  let U := freeOUResponse P (Real.sqrt (2*γ) • R) (V 0) γ a 0
  have hb := lp_secondOrder_stationary_local_bound P f H m γ T M M2 hm hγ hT hf hsc hLip hH hderiv
    V X U hV hX (continuous_freeOUResponse P _ _ _ _ _) hlaw hmild hkin
  have he := klmc2Step_eq_corrected_freeOU P R G A γ hγ a T hT (V 0,X 0)
  rw [he]
  exact (hb.2.2 hsmall).trans_eq (by ring)

/-- One actual numerical step combines the repaired synchronous comparison with the true stationary local defect. -/
theorem klmc2Step_oneStep_bound
    (f : EuclideanSpace ℝ ι → ℝ)
    (H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (m γ t α : ℝ) (M M2 : ℝ≥0) (hm : 0<m) (hmM : m≤(M : ℝ)) (hγ : 0<γ)
    (hfriction : m+(M : ℝ)≤γ^2) (ht : 0≤t) (hstep : 5*γ*(M : ℝ)*t≤m)
    (hα : 5*(Fintype.card ι : ℝ)≤α)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hH : LipschitzWith M2 H) (hderiv : ∀ x,HasFDerivAt (gradient f) (H x) x)
    (R : Lp (EuclideanSpace ℝ ι) 2 (ULA.CanonicalBrownian.vectorProbability ι) →L[ℝ]
      Lp (EuclideanSpace ℝ ι) 2 P) (a : ℝ≥0)
    (V X : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hV : Continuous V) (hX : Continuous X)
    (hlaw : ∀ s∈Icc 0 t,P.map (lpPhaseCoe P (V s,X s))=kineticGibbsTarget f)
    (hmild : ∀ s∈Icc 0 t,V s=freeOUResponse P (Real.sqrt (2*γ) • R) (V 0) γ a 0 s-
      dampedIntegral γ (fun r ↦ ULA.lpDrift P (gradient f) hLip (X r)) s)
    (hkin : ∀ s∈Icc 0 t,X s-X 0=∫ r in 0..s,V r)
    (w : Lp (EuclideanSpace ℝ ι) 2 P×Lp (EuclideanSpace ℝ ι) 2 P)
    (hGaussian : ∀ r∈Icc 0 t,HasLaw (freeOUResponse P (Real.sqrt (2*γ) • R) (V 0) γ a 0 r)
      (stdGaussian (EuclideanSpace ℝ ι)) P) :
    let G := ULA.lpDrift P (gradient f) hLip
    let A := lpHessian P (gradient f) H M M2 hLip hH hderiv
    transformNorm γ 0 (klmc2Step G A γ t w (liftedKLMC2Noise P R γ a t)-(V t,X t))≤
      (1-m*t/(2*γ)+(M2 : ℝ)*Real.sqrt α*t^2/γ)*transformNorm γ 0 ((V 0,X 0)-w)+
        Real.sqrt 2*t^2*((M : ℝ)-m)*Real.exp (-(α-(Fintype.card ι : ℝ))/8)+
      t^3/4*((M2 : ℝ)*Real.sqrt ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))+
        (M : ℝ)*Real.sqrt ((M : ℝ)*(Fintype.card ι : ℝ))) := by
  intro G A
  let z := (V 0,X 0)
  let Ξ := liftedKLMC2Noise P R γ a t
  have hcmp := klmc2SourceStep_comparison_bound P f H m γ t α M M2 hm hmM hγ hfriction ht hstep hα
    hf hsc hLip hH hderiv (Real.sqrt (2*γ) • R) a z w hGaussian
  dsimp only at hcmp
  rw [klmc2SourceStep_eq_klmc2Step P G A R γ a t z,
    klmc2SourceStep_eq_klmc2Step P G A R γ a t w] at hcmp
  have hlocal := klmc2Step_stationary_local_bound P f H m γ t M M2 hm hγ.le ht
    (secondOrder_step_friction_bound m M γ t hm hmM hstep) hf hsc hLip hH hderiv R a V X hV hX hlaw hmild hkin
  have hsym : transformNorm γ 0 (klmc2Step G A γ t w Ξ-klmc2Step G A γ t z Ξ)=
      transformNorm γ 0 (klmc2Step G A γ t z Ξ-klmc2Step G A γ t w Ξ) := by
    have he : klmc2Step G A γ t w Ξ-klmc2Step G A γ t z Ξ=
        -(klmc2Step G A γ t z Ξ-klmc2Step G A γ t w Ξ) := by abel
    rw [he,transformNorm_neg]
  exact (transformNorm_sub_triangle γ 0 (klmc2Step G A γ t w Ξ) (klmc2Step G A γ t z Ξ) (V t,X t)).trans
    (add_le_add (hsym.le.trans hcmp) hlocal)

end KineticLangevin
