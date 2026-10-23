import KineticLangevin.CanonicalKLMC2Recurrence
import KineticLangevin.SecondOrderRecurrence

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace KineticLangevin.SecondOrderSource
open GenericCanonicalCoupling
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : Measure (H ι)} [IsProbabilityMeasure μ]

/-- The source time-step regime makes the accumulated second-order contraction factor nonnegative. -/
theorem secondOrder_contraction_factor_nonneg (m M γ h : ℝ)
    (hm : 0<m) (hmM : m≤M) (hγ : 0<γ) (hfriction : m+M≤γ^2) (hh : 0≤h)
    (hstep : 5*γ*M*h≤m) : 0≤1-m*h/(4*γ) := by
  have hsmall := secondOrder_step_friction_bound m M γ h hm hmM hstep
  have hmγ : m≤γ^2 := by linarith only [hfriction,hm.trans_le hmM]
  have h1 := mul_le_mul_of_nonneg_right hmγ hh
  have h2 := mul_le_mul_of_nonneg_left hsmall hγ.le
  have h3 : m*h≤γ/5 := by nlinarith only [h1,h2]
  have h4 : m*h/(4*γ)≤1/20 := (div_le_iff₀ (by positivity : (0 : ℝ)<4*γ)).mpr (by linarith only [h3])
  linarith only [h4]

/-- The actual canonical second-order sampler has the exact per-coupling position error bound. -/
theorem klmc2_coupling_position_bound
    (f : H ι → ℝ) (Hess : H ι → H ι →L[ℝ] H ι) (m : ℝ) (M γ M2 : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hHLip : LipschitzWith M2 Hess)
    (hderiv : ∀ x,HasFDerivAt (gradient f) (Hess x) x)
    (hm : 0<m) (hmM : m≤(M : ℝ)) (hγ : 0<(γ : ℝ))
    (hfriction : m+(M : ℝ)≤(γ : ℝ)^2)
    (h : ℝ≥0) (hh : 0<(h : ℝ)) (hstep : 5*(γ : ℝ)*(M : ℝ)*(h : ℝ)≤m)
    (α : ℝ) (hα : 5*(Fintype.card ι : ℝ)≤α) (hcut : (M2 : ℝ)*Real.sqrt α*(h : ℝ)≤m/4)
    (c : ULA.Coupling μ (ULA.gibbsMeasure f)) (hc : ULA.couplingCost c.joint≠⊤)
    (hπ : MemLp (id : H ι → H ι) 2 (ULA.gibbsMeasure f)) (n : ℕ) :
    ‖(SecondOrderSource.numericalChain c hc hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h n).2-
      (GenericCanonicalCoupling.referenceChain c hπ f M γ hLip h n).2‖≤
      Real.sqrt 2*(1-m*(h : ℝ)/(4*(γ : ℝ)))^n*(ULA.couplingCost c.joint).toReal+
      Real.sqrt 2*(h : ℝ)^2*((M2 : ℝ)*Real.sqrt ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))+
        (M : ℝ)*Real.sqrt ((M : ℝ)*(Fintype.card ι : ℝ)))/m+
      8*((M : ℝ)-m)*(h : ℝ)/m*Real.exp (-(α-(Fintype.card ι : ℝ))/8) := by
  let S := SecondOrderSource.numericalChain c hc hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h
  let R := GenericCanonicalCoupling.referenceChain c hπ f M γ hLip h
  let e := fun k ↦ transformNorm γ 0 (S k-R k)
  let d := fun k ↦ ‖(S k).2-(R k).2‖
  let C : ℝ := (M2 : ℝ)*Real.sqrt ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))+
        (M : ℝ)*Real.sqrt ((M : ℝ)*(Fintype.card ι : ℝ))
  have hrec (k : ℕ) : e (k+1)≤(1-m*(h : ℝ)/(2*(γ : ℝ))+(M2 : ℝ)*Real.sqrt α*(h : ℝ)^2/(γ : ℝ))*e k+
      Real.sqrt 2*(h : ℝ)^2*((M : ℝ)-m)*Real.exp (-(α-(Fintype.card ι : ℝ))/8)+(h : ℝ)^3*C/4 := by
    simpa only [C,div_mul_eq_mul_div] using SecondOrderSource.numericalChain_error_recurrence f Hess m M γ M2 hf hsc hLip hHLip hderiv hm hmM hγ hfriction
      h hh hstep α hα c hc hπ k
  have hproject (k : ℕ) : d k≤Real.sqrt 2/(γ : ℝ)*e k := position_le_transformNorm γ hγ (S k-R k)
  have hi : e 0≤(γ : ℝ)*d 0 := by
    have hv : (S 0).1=(R 0).1 := rfl
    change transformNorm γ 0 ((S 0).1-(R 0).1,(S 0).2-(R 0).2)≤_
    rw [hv,sub_self,transformNorm_zero_velocity γ γ.coe_nonneg]
  have hcost : d 0=(ULA.couplingCost c.joint).toReal :=
    SecondOrderSource.initial_position_cost c hc hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h
  have hb := secondOrder_projected_bound e d m γ h M2 α (Fintype.card ι) ((M : ℝ)-m) C
    hm hγ hh (sub_nonneg.mpr hmM) (by dsimp only [C];positivity)
    (secondOrder_contraction_factor_nonneg m M γ h hm hmM hγ hfriction hh.le hstep) hcut
    (fun k ↦ transformNorm_nonneg _ _ _) hrec hproject hi n
  rw [hcost] at hb
  exact hb

end KineticLangevin.SecondOrderSource
