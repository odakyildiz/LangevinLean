import KIPLMC.CanonicalExponential
import KIPLMC.OBABOPaperRate
import KineticLangevin.Accuracy

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace KIPLMC

/-- Allocate one third of the total error to each persistent floor. -/
theorem three_term_geometric_accuracy (α D ε b s error : ℝ) (n : ℕ)
    (hα : 0<α) (hα1 : α≤1) (hD : 0≤D) (hε : 0<ε)
    (hb : b≤ε/3) (hs : s≤ε/3)
    (hn : D=0 ∨ KineticLangevin.firstOrderIterationCount α D ε≤n)
    (he : error≤Real.sqrt 2*(1-α)^n*D+b+s) : error≤ε := by
  apply KineticLangevin.firstOrder_accuracy_budget α D ε (b+s) error hα hα1 hD hε
    (by linarith) n hn
  simpa only [add_assoc] using he

/-- The actual KIPLMC1 algorithm attains epsilon error with explicit statistical, step, and integer-time budgets. -/
theorem kiplmc1_accuracy {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx→ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m≤(L:ℝ)) (hm : 0<m)
    (hγ : 0<(γ:ℝ)) (hfriction : m+(L:ℝ)≤(γ:ℝ)^2)
    (h : ℝ≥0) (hh : 0<(h:ℝ)) (hstep : 4*(γ:ℝ)*(L:ℝ)*(h:ℝ)≤m)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν] (hν : MemLp (id : State N dθ dx→State N dθ dx) 2 ν)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar)
    (ε : ℝ) (hε : 0<ε)
    (hbias : (L:ℝ)*(h:ℝ)*(Real.sqrt 2*Real.sqrt (((dθ:ℝ)+(N:ℝ)*(dx:ℝ))/(N:ℝ)))/m≤ε/3)
    (hstat : Real.sqrt ((dθ:ℝ)/((N:ℝ)*m))≤ε/3) (n : ℕ)
    (hn : ULA.wasserstein2Real ν (IPLA.gibbsTarget U)=0 ∨
      KineticLangevin.firstOrderIterationCount (3*m*(h:ℝ)/(4*(γ:ℝ)))
        (ULA.wasserstein2Real ν (IPLA.gibbsTarget U)) ε≤n) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z-θStar‖^2
      ∂(kiplmc1GaussianLaws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd)≤ε := by
  apply three_term_geometric_accuracy (3*m*(h:ℝ)/(4*(γ:ℝ)))
    (ULA.wasserstein2Real ν (IPLA.gibbsTarget U)) ε _ _ _ n (by positivity)
    (KineticLangevin.klmc_rate_fraction_le_one m L γ h hm hmL hγ hfriction h.coe_nonneg hstep)
    ENNReal.toReal_nonneg hε hbias hstat hn
  exact kiplmc1_parameter_bound hN U m L γ hdiff hsc hLip hmL hm hγ hfriction h hh hstep ν hν θStar hmax n

/-- The same rounded logarithmic threshold controls a genuine exponential transient. -/
theorem exponential_transient_budget (α D ε : ℝ) (hα : 0<α) (hD : 0≤D) (hε : 0<ε) (n : ℕ)
    (hn : D=0 ∨ KineticLangevin.firstOrderIterationCount α D ε≤n) :
    D*Real.exp (-α*(n:ℝ))≤ε/24 := by
  rcases eq_or_lt_of_le hD with hz|hp
  · simp only [← hz,zero_mul]
    positivity
  · have hn' : KineticLangevin.firstOrderIterationCount α D ε≤n := hn.resolve_left hp.ne'
    have hc := KineticLangevin.firstOrderIterationCount_spec α D ε hα n hn'
    have he := Real.exp_le_exp.mpr (show -α*(n:ℝ)≤-Real.log (24*D/ε) by linarith)
    rw [Real.exp_neg,Real.exp_log (by positivity : 0<24*D/ε)] at he
    have hb := mul_le_mul_of_nonneg_left he hD
    have hid : D*(24*D/ε)⁻¹=ε/24 := by field_simp
    rwa [hid] at hb

/-- A fully explicit particle count for the square-root equilibrium floor. -/
def accuracyParticleCount (C d ε : ℝ) : ℕ :=
  max 1 (Nat.ceil (9*C^2*d/ε^2))

/-- The integer choice is positive and makes the equilibrium contribution at most epsilon/3. -/
theorem accuracyParticleCount_spec (C d ε : ℝ) (hC : 0≤C) (hd : 0≤d) (hε : 0<ε) :
    0<accuracyParticleCount C d ε ∧
    C*Real.sqrt (d/(accuracyParticleCount C d ε:ℝ))≤ε/3 := by
  let N := accuracyParticleCount C d ε
  have hN : 1≤N := le_max_left _ _
  have hn : 0<(N:ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hN)
  have hceil : Nat.ceil (9*C^2*d/ε^2)≤N := le_max_right _ _
  have hc : 9*C^2*d/ε^2≤(N:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hx := (div_le_iff₀ (sq_pos_of_pos hε)).mp hc
  have hs := Real.sq_sqrt (div_nonneg hd hn.le)
  have hm : 9*C^2*(d/(N:ℝ))≤ε^2 := by
    calc
      _ = (9*C^2*d)/(N:ℝ) := by ring
      _ ≤ ε^2 := (div_le_iff₀ hn).mpr (by nlinarith)
  refine ⟨Nat.succ_le_iff.mp hN,?_⟩
  change C*Real.sqrt (d/(N:ℝ))≤ε/3
  nlinarith [sq_nonneg (C*Real.sqrt (d/(N:ℝ))+ε/3)]

/-- Balance a positive stability cap and a linear discretization floor. -/
def accuracyStep (stability biasCoefficient ε : ℝ) : ℝ :=
  min stability (ε/(3*biasCoefficient))

/-- The explicit minimum is positive, respects stability, and controls the discretization floor. -/
theorem accuracyStep_spec (A B ε : ℝ) (hA : 0<A) (hB : 0<B) (hε : 0<ε) :
    0<accuracyStep A B ε ∧ accuracyStep A B ε≤A ∧ accuracyStep A B ε*B≤ε/3 := by
  have hmin := min_le_right A (ε/(3*B))
  have he := (le_div_iff₀ (by positivity : 0<3*B)).mp hmin
  exact ⟨lt_min hA (by positivity),min_le_left _ _,by dsimp only [accuracyStep];nlinarith⟩

/-- The source's particle-dimension expression after the statistical choice N=dtheta/epsilon². -/
theorem complexity_dimension_identity (dθ dx ε : ℝ) (hθ : 0≤dθ) (hx : 0≤dx) (hε : 0<ε) :
    Real.sqrt ((dθ/ε^2)*(dθ+(dθ/ε^2)*dx))=
      (dθ/ε)*Real.sqrt (1+dx/ε^2) := by
  have hleft := Real.sq_sqrt (by positivity : 0≤(dθ/ε^2)*(dθ+(dθ/ε^2)*dx))
  have hright := Real.sq_sqrt (by positivity : 0≤1+dx/ε^2)
  have he : (dθ/ε^2)*(dθ+(dθ/ε^2)*dx)=(dθ/ε)^2*(1+dx/ε^2) := by field_simp
  have hn : 0≤(dθ/ε)*Real.sqrt (1+dx/ε^2) := by positivity
  have heq : Real.sqrt ((dθ/ε^2)*(dθ+(dθ/ε^2)*dx))^2 = ((dθ/ε)*Real.sqrt (1+dx/ε^2))^2 := by
    rw [mul_pow,hright]
    exact hleft.trans he
  nlinarith [Real.sqrt_nonneg ((dθ/ε^2)*(dθ+(dθ/ε^2)*dx))]

/-- The printed coarse KIPLMC2 rate gives an actual epsilon guarantee with all constants and the integer count visible. -/
theorem kiplmc2_accuracy {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx→ℝ) (m γ h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0<m) (hmL : m≤(L:ℝ))
    (hγ : 0<γ) (hh : 0<h) (hfriction : 4*(L:ℝ)≤γ^2) (hstep : 33*γ^3*h≤m)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx→State N dθ dx) 2 ν)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar)
    (ε : ℝ) (hε : 0<ε)
    (hbias : kiplmc2PaperConstant m L γ*h*Real.sqrt ((N:ℝ)*((dθ:ℝ)+(N:ℝ)*(dx:ℝ)))≤ε/3)
    (hstat : kiplmc2PaperConstant m L γ*Real.sqrt ((dθ:ℝ)/(N:ℝ))≤ε/3) (n : ℕ)
    (hn : let D := kiplmc2PaperConstant m L γ*(Real.sqrt N*ULA.wasserstein2Real ν (IPLA.gibbsTarget U)+
          h*(N:ℝ)*Real.sqrt ((dθ:ℝ)+(N:ℝ)*(dx:ℝ)))
      D=0 ∨ KineticLangevin.firstOrderIterationCount (m*h/(6*γ)) D ε≤n) :
    Real.sqrt (∫ z,‖IPLA.parameterCLM z-θStar‖^2
      ∂(kiplmc2Laws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd)≤ε := by
  have hC := (kiplmc2PaperConstant_bounds m L γ hm L.coe_nonneg hγ).1
  let A := Real.sqrt N*ULA.wasserstein2Real ν (IPLA.gibbsTarget U)+
    h*(N:ℝ)*Real.sqrt ((dθ:ℝ)+(N:ℝ)*(dx:ℝ))
  have hA : 0≤A := by dsimp [A];exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg) (by positivity)
  have ht := exponential_transient_budget (m*h/(6*γ)) (kiplmc2PaperConstant m L γ*A) ε
    (by positivity) (mul_nonneg hC hA) hε n hn
  have hb := kiplmc2_parameter_paper_bound hN U m γ h L hdiff hsc hLip hm hmL hγ hh hfriction hstep ν hν θStar hmax n
  have he : -m*h*(n:ℝ)/(6*γ)=-(m*h/(6*γ))*(n:ℝ) := by ring
  rw [he] at hb
  nlinarith

end KIPLMC
