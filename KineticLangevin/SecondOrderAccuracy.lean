import KineticLangevin.CanonicalKLMC2
import KineticLangevin.SecondOrderBudget

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace KineticLangevin.SecondOrderSource
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The actual second-order Gaussian sampler reaches epsilon under explicit quadratic-bias and integer-time budgets. -/
theorem klmc2_accuracy {μ : Measure (H ι)} [IsProbabilityMeasure μ]
    (f : H ι→ℝ) (Hess : H ι→H ι→L[ℝ] H ι) (m : ℝ) (M γ M2 : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hHLip : LipschitzWith M2 Hess)
    (hderiv : ∀ x,HasFDerivAt (gradient f) (Hess x) x)
    (hm : 0<m) (hmM : m≤(M:ℝ)) (hγ : 0<(γ:ℝ)) (hM2 : 0<(M2:ℝ))
    (hfriction : m+(M:ℝ)≤(γ:ℝ)^2) (h : ℝ≥0) (hh : 0<(h:ℝ)) (hh1 : (h:ℝ)≤1)
    (hstep : 5*(γ:ℝ)*(M:ℝ)*(h:ℝ)≤m)
    (hdim : 4*Real.sqrt (5*(Fintype.card ι:ℝ))*(M2:ℝ)*(h:ℝ)≤m)
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f)≠⊤) (ε : ℝ) (hε : 0<ε)
    (hbias : secondOrderBiasCoefficient m M M2 (Fintype.card ι)*(h:ℝ)^2≤(47/50:ℝ)*ε)
    (n : ℕ) (hn : ULA.wasserstein2Real μ (ULA.gibbsMeasure f)=0 ∨
      firstOrderIterationCount (m*(h:ℝ)/(4*(γ:ℝ))) (ULA.wasserstein2Real μ (ULA.gibbsMeasure f)) ε≤n) :
    ULA.wasserstein2Real (law ι (gradient f) Hess γ h μ n) (ULA.gibbsMeasure f)≤ε := by
  have hb := klmc2_wasserstein_bound_exact ι f Hess m M γ M2 hf hsc hLip hHLip hderiv hm hmM hγ hM2
    hfriction h hh hstep hdim hfinite n
  have hq := secondOrder_contraction_factor_nonneg m M γ h hm hmM hγ hfriction hh.le hstep
  have hquad := secondOrder_bias_quadratic m M M2 h (Fintype.card ι) hm hmM hM2 hh hh1 (by positivity) hdim
  apply firstOrder_accuracy_budget (m*(h:ℝ)/(4*(γ:ℝ))) (ULA.wasserstein2Real μ (ULA.gibbsMeasure f)) ε
    (secondOrderBiasCoefficient m M M2 (Fintype.card ι)*(h:ℝ)^2) _ (by positivity) (by linarith)
    ENNReal.toReal_nonneg hε hbias n hn
  linarith

/-- The actual sampler with the explicit positive minimum step and rounded natural iteration count reaches epsilon. -/
theorem klmc2_accuracy_explicit {μ : Measure (H ι)} [IsProbabilityMeasure μ]
    (hp : 0<Fintype.card ι)
    (f : H ι→ℝ) (Hess : H ι→H ι→L[ℝ] H ι) (m : ℝ) (M γ M2 : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hHLip : LipschitzWith M2 Hess)
    (hderiv : ∀ x,HasFDerivAt (gradient f) (Hess x) x)
    (hm : 0<m) (hmM : m≤(M:ℝ)) (hγ : 0<(γ:ℝ)) (hM2 : 0<(M2:ℝ))
    (hfriction : m+(M:ℝ)≤(γ:ℝ)^2)
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f)≠⊤) (ε : ℝ) (hε : 0<ε) :
    let hs := secondOrderAccuracyStep_spec m M γ M2 (Fintype.card ι) ε hm (hm.trans_le hmM)
      hγ hM2 (by exact_mod_cast hp) hε
    let h : ℝ≥0 := ⟨secondOrderAccuracyStep m M γ M2 (Fintype.card ι) ε,hs.1.le⟩
    let n := firstOrderIterationCount (m*(h:ℝ)/(4*(γ:ℝ))) (ULA.wasserstein2Real μ (ULA.gibbsMeasure f)) ε
    ULA.wasserstein2Real (law ι (gradient f) Hess γ h μ n) (ULA.gibbsMeasure f)≤ε := by
  let hs := secondOrderAccuracyStep_spec m M γ M2 (Fintype.card ι) ε hm (hm.trans_le hmM)
    hγ hM2 (by exact_mod_cast hp) hε
  let h : ℝ≥0 := ⟨secondOrderAccuracyStep m M γ M2 (Fintype.card ι) ε,hs.1.le⟩
  change ULA.wasserstein2Real (law ι (gradient f) Hess γ h μ
    (firstOrderIterationCount (m*(h:ℝ)/(4*(γ:ℝ))) (ULA.wasserstein2Real μ (ULA.gibbsMeasure f)) ε)) _≤ε
  exact klmc2_accuracy ι f Hess m M γ M2 hf hsc hLip hHLip hderiv hm hmM hγ hM2 hfriction
    h hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hfinite ε hε hs.2.2.2.2 _ (Or.inr le_rfl)

end KineticLangevin.SecondOrderSource
