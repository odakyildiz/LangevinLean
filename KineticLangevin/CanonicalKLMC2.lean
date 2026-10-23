import KineticLangevin.CanonicalKLMC2Bound
import KineticLangevin.SecondOrderRecurrence

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KineticLangevin.SecondOrderSource
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The actual correlated-Gaussian KLMC2 sampler bound, with the exact Gaussian fourth moment in every dimension.
The full reference construction, Gibbs stationarity, repaired stochastic Hessian comparison, and true coupling infimum are internal. -/
theorem klmc2_wasserstein_bound_exact {μ : Measure (H ι)} [IsProbabilityMeasure μ]
    (f : H ι→ℝ) (Hess : H ι→H ι→L[ℝ] H ι) (m : ℝ) (M γ M2 : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hHLip : LipschitzWith M2 Hess)
    (hderiv : ∀ x,HasFDerivAt (gradient f) (Hess x) x)
    (hm : 0<m) (hmM : m≤(M:ℝ)) (hγ : 0<(γ:ℝ)) (hM2 : 0<(M2:ℝ))
    (hfriction : m+(M:ℝ)≤(γ:ℝ)^2) (h : ℝ≥0) (hh : 0<(h:ℝ))
    (hstep : 5*(γ:ℝ)*(M:ℝ)*(h:ℝ)≤m)
    (hdim : 4*Real.sqrt (5*(Fintype.card ι:ℝ))*(M2:ℝ)*(h:ℝ)≤m)
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f)≠⊤) (n : ℕ) :
    ULA.wasserstein2Real (law ι (gradient f) Hess γ h μ n) (ULA.gibbsMeasure f)≤
      Real.sqrt 2*(1-m*(h:ℝ)/(4*(γ:ℝ)))^n*ULA.wasserstein2Real μ (ULA.gibbsMeasure f)+
      Real.sqrt 2*(h:ℝ)^2*((M2:ℝ)*Real.sqrt ((Fintype.card ι:ℝ)^2+2*(Fintype.card ι:ℝ))+
        (M:ℝ)*Real.sqrt ((M:ℝ)*(Fintype.card ι:ℝ)))/m+
      8*((M:ℝ)-m)*(h:ℝ)/m*Real.exp (-(secondOrderCutoff m M2 h-(Fintype.card ι:ℝ))/8) := by
  letI := ULA.isProbabilityMeasure_gibbsMeasure f m hm hf hsc
  have hπ := ULA.memLp_id_gibbsMeasure f m hm hf hsc
  let α := secondOrderCutoff m M2 h
  have hcut := secondOrderCutoff_spec m M2 h (Fintype.card ι) hm hM2 hh (by positivity) hdim
  have hstep4 : 4*(γ:ℝ)*(M:ℝ)*(h:ℝ)≤m := by nlinarith [mul_nonneg (mul_nonneg γ.coe_nonneg M.coe_nonneg) h.coe_nonneg]
  have hfrac := klmc_rate_fraction_le_one m M γ h hm hmM hγ hfriction h.coe_nonneg hstep4
  have hid : 3*m*(h:ℝ)/(4*(γ:ℝ))=3*(m*(h:ℝ)/(4*(γ:ℝ))) := by ring
  rw [hid] at hfrac
  have hq : 0≤1-m*(h:ℝ)/(4*(γ:ℝ)) := by linarith
  let a : ℝ≥0 := ⟨Real.sqrt 2*(1-m*(h:ℝ)/(4*(γ:ℝ)))^n,by positivity⟩
  let b : ℝ≥0 := ⟨Real.sqrt 2*(h:ℝ)^2*((M2:ℝ)*Real.sqrt ((Fintype.card ι:ℝ)^2+2*(Fintype.card ι:ℝ))+
      (M:ℝ)*Real.sqrt ((M:ℝ)*(Fintype.card ι:ℝ)))/m+
      8*((M:ℝ)-m)*(h:ℝ)/m*Real.exp (-(α-(Fintype.card ι:ℝ))/8),
      add_nonneg (by positivity) (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hmM)) h.coe_nonneg) hm.le) (Real.exp_nonneg _))⟩
  rw [add_assoc]
  change ULA.wasserstein2Real _ _≤(a:ℝ)*ULA.wasserstein2Real μ (ULA.gibbsMeasure f)+(b:ℝ)
  apply ULA.wasserstein2_affine_bound_real_of_finite_couplings μ (ULA.gibbsMeasure f)
    (law ι (gradient f) Hess γ h μ n) (ULA.gibbsMeasure f) a b hfinite
    (law_wasserstein2_ne_top hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h hfinite n)
  intro c hc
  have hb := klmc2_coupling_position_bound f Hess m M γ M2 hf hsc hLip hHLip hderiv
    hm hmM hγ hfriction h hh hstep α hcut.2.2.2 hcut.2.2.1.le c hc hπ n
  have hglobal := GenericCanonicalCoupling.globalReferenceFlow_stationary f m hm M γ hf hsc hLip c hπ
  have hR := GenericCanonicalCoupling.referenceChain_position_law c hπ f M γ hLip h hglobal n
  have hS := numericalChain_outputLaw c hc hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h n
  have hw := ULA.wasserstein2_le_Lp_cost_real (GenericCanonicalCoupling.probability c)
    (numericalChain c hc hπ (gradient f) Hess M M2 hLip hHLip hderiv γ h n).2
    (GenericCanonicalCoupling.referenceChain c hπ f M γ hLip h n).2
  rw [hS,hR] at hw
  change ULA.wasserstein2Real (law ι (gradient f) Hess γ h μ n) (ULA.gibbsMeasure f)≤
    Real.sqrt 2*(1-m*(h:ℝ)/(4*(γ:ℝ)))^n*(ULA.couplingCost c.joint).toReal+
      (Real.sqrt 2*(h:ℝ)^2*((M2:ℝ)*Real.sqrt ((Fintype.card ι:ℝ)^2+2*(Fintype.card ι:ℝ))+
        (M:ℝ)*Real.sqrt ((M:ℝ)*(Fintype.card ι:ℝ)))/m+
      8*((M:ℝ)-m)*(h:ℝ)/m*Real.exp (-(α-(Fintype.card ι:ℝ))/8))
  simpa only [add_assoc] using hw.trans hb

/-- The actual sampler also satisfies the source footnote’s stronger inverse-step-square tail. -/
theorem klmc2_wasserstein_bound_sharp_tail {μ : Measure (H ι)} [IsProbabilityMeasure μ]
    (f : H ι→ℝ) (Hess : H ι→H ι→L[ℝ] H ι) (m : ℝ) (M γ M2 : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hHLip : LipschitzWith M2 Hess)
    (hderiv : ∀ x,HasFDerivAt (gradient f) (Hess x) x)
    (hm : 0<m) (hmM : m≤(M:ℝ)) (hγ : 0<(γ:ℝ)) (hM2 : 0<(M2:ℝ))
    (hfriction : m+(M:ℝ)≤(γ:ℝ)^2) (h : ℝ≥0) (hh : 0<(h:ℝ))
    (hstep : 5*(γ:ℝ)*(M:ℝ)*(h:ℝ)≤m)
    (hdim : 4*Real.sqrt (5*(Fintype.card ι:ℝ))*(M2:ℝ)*(h:ℝ)≤m)
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f)≠⊤) (n : ℕ) :
    ULA.wasserstein2Real (law ι (gradient f) Hess γ h μ n) (ULA.gibbsMeasure f)≤
      Real.sqrt 2*(1-m*(h:ℝ)/(4*(γ:ℝ)))^n*ULA.wasserstein2Real μ (ULA.gibbsMeasure f)+
      Real.sqrt 2*(h:ℝ)^2*((M2:ℝ)*Real.sqrt ((Fintype.card ι:ℝ)^2+2*(Fintype.card ι:ℝ))+
        (M:ℝ)*Real.sqrt ((M:ℝ)*(Fintype.card ι:ℝ)))/m+
      8*((M:ℝ)-m)*(h:ℝ)/m*Real.exp (-m^2/(160*(M2:ℝ)^2*(h:ℝ)^2)) := by
  have hb := klmc2_wasserstein_bound_exact ι f Hess m M γ M2 hf hsc hLip hHLip hderiv hm hmM hγ hM2
    hfriction h hh hstep hdim hfinite n
  have he := (secondOrderCutoff_tail m M2 h (Fintype.card ι) hm hM2 hh (by positivity) hdim).2
  have hB : 0≤(M:ℝ)-m := sub_nonneg.mpr hmM
  have ht := mul_le_mul_of_nonneg_left he (by positivity : 0≤8*((M:ℝ)-m)*(h:ℝ)/m)
  linarith

/-- The printed second-order theorem, with its valid dimension restriction p≥2 stated explicitly. -/
theorem klmc2_wasserstein_bound {μ : Measure (H ι)} [IsProbabilityMeasure μ]
    (hp : 2≤Fintype.card ι)
    (f : H ι→ℝ) (Hess : H ι→H ι→L[ℝ] H ι) (m : ℝ) (M γ M2 : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hHLip : LipschitzWith M2 Hess)
    (hderiv : ∀ x,HasFDerivAt (gradient f) (Hess x) x)
    (hm : 0<m) (hmM : m≤(M:ℝ)) (hγ : 0<(γ:ℝ)) (hM2 : 0<(M2:ℝ))
    (hfriction : m+(M:ℝ)≤(γ:ℝ)^2) (h : ℝ≥0) (hh : 0<(h:ℝ))
    (hstep : 5*(γ:ℝ)*(M:ℝ)*(h:ℝ)≤m)
    (hdim : 4*Real.sqrt (5*(Fintype.card ι:ℝ))*(M2:ℝ)*(h:ℝ)≤m)
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f)≠⊤) (n : ℕ) :
    ULA.wasserstein2Real (law ι (gradient f) Hess γ h μ n) (ULA.gibbsMeasure f)≤
      Real.sqrt 2*(1-m*(h:ℝ)/(4*(γ:ℝ)))^n*ULA.wasserstein2Real μ (ULA.gibbsMeasure f)+
      2*(h:ℝ)^2*(M2:ℝ)*(Fintype.card ι:ℝ)/m+
      (h:ℝ)^2*(M:ℝ)*Real.sqrt (2*(M:ℝ)*(Fintype.card ι:ℝ))/m+
      (8*(M:ℝ)/m)*(h:ℝ)*Real.exp (-(Fintype.card ι:ℝ)/2) := by
  have hb := klmc2_wasserstein_bound_exact ι f Hess m M γ M2 hf hsc hLip hHLip hderiv hm hmM hγ hM2
    hfriction h hh hstep hdim hfinite n
  have hd := secondOrder_source_dimension_bound (Fintype.card ι) M M2 (by exact_mod_cast hp) M.coe_nonneg M2.coe_nonneg
  have hD := mul_le_mul_of_nonneg_left hd (by positivity : 0≤(h:ℝ)^2/m)
  have ht := (secondOrderCutoff_tail m M2 h (Fintype.card ι) hm hM2 hh (by positivity) hdim).1
  have hB : 0≤(M:ℝ)-m := sub_nonneg.mpr hmM
  have htail : 8*((M:ℝ)-m)*(h:ℝ)/m*Real.exp (-(secondOrderCutoff m M2 h-(Fintype.card ι:ℝ))/8)≤
      (8*(M:ℝ)/m)*(h:ℝ)*Real.exp (-(Fintype.card ι:ℝ)/2) := by
    have h1 := mul_le_mul_of_nonneg_left ht (by positivity : 0≤8*((M:ℝ)-m)*(h:ℝ)/m)
    have hbase : 8*((M:ℝ)-m)*(h:ℝ)/m≤8*(M:ℝ)/m*(h:ℝ) := by
      have hnum : 8*((M:ℝ)-m)*(h:ℝ)≤8*(M:ℝ)*(h:ℝ) := by nlinarith [mul_nonneg hm.le h.coe_nonneg]
      convert div_le_div_of_nonneg_right hnum hm.le using 1 <;> ring
    have h2 := mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg (-(Fintype.card ι:ℝ)/2))
    exact h1.trans h2
  have hDbound : Real.sqrt 2*(h:ℝ)^2*((M2:ℝ)*Real.sqrt ((Fintype.card ι:ℝ)^2+2*(Fintype.card ι:ℝ))+
      (M:ℝ)*Real.sqrt ((M:ℝ)*(Fintype.card ι:ℝ)))/m ≤
      2*(h:ℝ)^2*(M2:ℝ)*(Fintype.card ι:ℝ)/m+(h:ℝ)^2*(M:ℝ)*Real.sqrt (2*(M:ℝ)*(Fintype.card ι:ℝ))/m := by
    convert hD using 1 <;> ring
  exact hb.trans (by linarith)

end KineticLangevin.SecondOrderSource
