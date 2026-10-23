import KineticLangevin.CanonicalKLMC
import KineticLangevin.Complexity

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace KineticLangevin

/-- The genuine KLMC geometric rate lies in the interval required by the logarithmic count. -/
theorem klmc_rate_fraction_le_one (m M γ h : ℝ) (hm : 0<m) (hmM : m≤M)
    (hγ : 0<γ) (hfriction : m+M≤γ^2) (hh : 0≤h) (hstep : 4*γ*M*h≤m) :
    3*m*h/(4*γ)≤1 := by
  obtain ⟨hc,hs⟩ := kinetic_scalar_conditions m M γ h hm hmM hγ hfriction hh hstep
  have hb := firstOrder_coefficient_bound (m/γ) M h (by positivity) (hm.le.trans hmM) hh hc hs
  have he := Real.exp_pos (-(m/γ)*h)
  have hM : 0≤M := hm.le.trans hmM
  have hp : 0≤(3/4:ℝ)*M*h^2 := by positivity
  have hid : 3*m*h/(4*γ)=(3/4:ℝ)*(m/γ)*h := by ring
  rw [hid]
  linarith

/-- An actual sampler accuracy guarantee, with a rounded natural iteration count and no convergence premise. -/
theorem klmc_accuracy_of_error_budgets {d : ℕ} {μ : Measure (CanonicalCoupling.H d)}
    [IsProbabilityMeasure μ] (f : CanonicalCoupling.H d → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hmM : m≤(M:ℝ)) (hm : 0<m) (hγ : 0<(γ:ℝ)) (hfriction : m+(M:ℝ)≤(γ:ℝ)^2)
    (h : ℝ≥0) (hh : 0<(h:ℝ)) (hstep : 4*(γ:ℝ)*(M:ℝ)*(h:ℝ)≤m)
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f)≠⊤) (ε : ℝ) (hε : 0<ε)
    (hbias : (M:ℝ)*(h:ℝ)*Real.sqrt (2*(d:ℝ))/m≤(47/50:ℝ)*ε) (n : ℕ)
    (hn : ULA.wasserstein2Real μ (ULA.gibbsMeasure f)=0 ∨
      firstOrderIterationCount (3*m*(h:ℝ)/(4*(γ:ℝ)))
        (ULA.wasserstein2Real μ (ULA.gibbsMeasure f)) ε≤n) :
    ULA.wasserstein2Real (CanonicalCoupling.klmcLaw f γ h μ n) (ULA.gibbsMeasure f)≤ε := by
  apply firstOrder_accuracy_budget (3*m*(h:ℝ)/(4*(γ:ℝ)))
    (ULA.wasserstein2Real μ (ULA.gibbsMeasure f)) ε _ _ (by positivity)
    (klmc_rate_fraction_le_one m M γ h hm hmM hγ hfriction h.coe_nonneg hstep)
    (ENNReal.toReal_nonneg) hε hbias n hn
  exact CanonicalCoupling.klmc_wasserstein_bound f m M γ hf hsc hLip hmM hm hγ hfriction h hh hstep hfinite n

/-- The paper's explicit minimum of stability and 0.94-epsilon bias step sizes. -/
def klmcAccuracyStep (m M γ p ε : ℝ) : ℝ :=
  min (m/(4*γ*M)) ((47/50:ℝ)*ε*m/(M*Real.sqrt (2*p)))

/-- The chosen step is positive, stable, and satisfies the exact printed bias allocation. -/
theorem klmcAccuracyStep_spec (m M γ p ε : ℝ) (hm : 0<m) (hM : 0<M)
    (hγ : 0<γ) (hp : 0<p) (hε : 0<ε) :
    0<klmcAccuracyStep m M γ p ε ∧
    4*γ*M*klmcAccuracyStep m M γ p ε≤m ∧
    M*klmcAccuracyStep m M γ p ε*Real.sqrt (2*p)/m≤(47/50:ℝ)*ε := by
  have hs : 0<Real.sqrt (2*p) := Real.sqrt_pos.2 (by positivity)
  refine ⟨lt_min (by positivity) (by positivity),?_,?_⟩
  · have hb := min_le_left (m/(4*γ*M)) ((47/50:ℝ)*ε*m/(M*Real.sqrt (2*p)))
    have hx := (le_div_iff₀ (by positivity : 0<4*γ*M)).mp hb
    change 4*γ*M*min _ _≤m
    nlinarith
  · have hb := min_le_right (m/(4*γ*M)) ((47/50:ℝ)*ε*m/(M*Real.sqrt (2*p)))
    have hb' := (le_div_iff₀ (mul_pos hM hs)).mp hb
    apply (div_le_iff₀ hm).mpr
    dsimp only [klmcAccuracyStep]
    nlinarith

/-- The exact first-order sampler with the explicit paper step and an integer logarithmic count has error at most epsilon. -/
theorem klmc_accuracy_explicit {d : ℕ} (hd : 0<d) {μ : Measure (CanonicalCoupling.H d)}
    [IsProbabilityMeasure μ] (f : CanonicalCoupling.H d → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hmM : m≤(M:ℝ)) (hm : 0<m) (hγ : 0<(γ:ℝ)) (hfriction : m+(M:ℝ)≤(γ:ℝ)^2)
    (hfinite : ULA.wasserstein2 μ (ULA.gibbsMeasure f)≠⊤) (ε : ℝ) (hε : 0<ε) :
    let hs := klmcAccuracyStep_spec m M γ d ε hm (hm.trans_le hmM) hγ (by exact_mod_cast hd) hε
    let h : ℝ≥0 := ⟨klmcAccuracyStep m M γ d ε,hs.1.le⟩
    let n := firstOrderIterationCount (3*m*(h:ℝ)/(4*(γ:ℝ))) (ULA.wasserstein2Real μ (ULA.gibbsMeasure f)) ε
    ULA.wasserstein2Real (CanonicalCoupling.klmcLaw f γ h μ n) (ULA.gibbsMeasure f)≤ε := by
  let hs := klmcAccuracyStep_spec m M γ d ε hm (hm.trans_le hmM) hγ (by exact_mod_cast hd) hε
  let h : ℝ≥0 := ⟨klmcAccuracyStep m M γ d ε,hs.1.le⟩
  change ULA.wasserstein2Real (CanonicalCoupling.klmcLaw f γ h μ
    (firstOrderIterationCount (3*m*(h:ℝ)/(4*(γ:ℝ))) (ULA.wasserstein2Real μ (ULA.gibbsMeasure f)) ε)) _≤ε
  exact klmc_accuracy_of_error_budgets f m M γ hf hsc hLip hmM hm hγ hfriction h
    hs.1 hs.2.1 hfinite ε hε hs.2.2 _ (Or.inr le_rfl)

end KineticLangevin
