import KIPLMC.OBABOBound

/-! # The supplied KIPLMC2 particle-rate statement with an explicit constant -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KIPLMC

/-- The exact OBABO square-root geometric rate has the paper's exponential envelope. -/
theorem kiplmc2_rate_exp_bound (m γ h : ℝ) (n : ℕ) :
    (KineticLangevin.obaboContractionRate m γ h : ℝ)^n ≤
      Real.exp (-m*h*(n : ℝ)/(6*γ)) := by
  have hr : (KineticLangevin.obaboContractionRate m γ h : ℝ) ≤ Real.exp (-m*h/(6*γ)) := by
    change Real.sqrt (1-m*h/(3*γ))≤_
    by_cases hq : 0≤1-m*h/(3*γ)
    · apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
      rw [Real.sq_sqrt hq,pow_two,← Real.exp_add]
      have he := Real.add_one_le_exp (-m*h/(3*γ))
      have he' : 1-m*h/(3*γ)≤Real.exp (-m*h/(3*γ)) := by convert he using 1 <;> ring
      convert he' using 1 <;> congr 1 <;> ring
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hq)]
      positivity
  have hp := pow_le_pow_left₀ (KineticLangevin.obaboContractionRate m γ h).coe_nonneg hr n
  convert hp using 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- An explicit uniform upper bound for the physical-time bias coefficient. -/
def kiplmc2PaperBiasCoefficient (m L γ : ℝ) : ℝ :=
  (6*Real.sqrt 2*γ/m)*(4*Real.sqrt L+L*m/(66*γ^3))

/-- This constant depends only on curvature, smoothness and friction. -/
def kiplmc2PaperConstant (m L γ : ℝ) : ℝ :=
  Real.sqrt 2+kiplmc2PaperBiasCoefficient m L γ+1/Real.sqrt m

theorem kiplmc2PaperConstant_bounds (m L γ : ℝ) (hm : 0<m) (hL : 0≤L) (hγ : 0<γ) :
    0≤kiplmc2PaperConstant m L γ ∧ Real.sqrt 2≤kiplmc2PaperConstant m L γ ∧
      kiplmc2PaperBiasCoefficient m L γ≤kiplmc2PaperConstant m L γ ∧
      1/Real.sqrt m≤kiplmc2PaperConstant m L γ := by
  have hB : 0≤kiplmc2PaperBiasCoefficient m L γ := by unfold kiplmc2PaperBiasCoefficient;positivity
  have hI : 0≤1/Real.sqrt m := by positivity
  unfold kiplmc2PaperConstant
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith [Real.sqrt_nonneg 2]

/-- The explicit intensive bound implies the manuscript's coarser particle
rate, including the stated transient term, uniformly in N and dimensions. -/
theorem kiplmc2_paper_envelope (m L γ h N d dθ D error : ℝ) (n : ℕ)
    (hm : 0<m) (hL : 0≤L) (hγ : 0<γ) (hh : 0≤h) (hN : 1≤N)
    (hd : 0≤d) (hθ : 0≤dθ) (hD : 0≤D) (hstep : 33*γ^3*h≤m)
    (hbound : error≤Real.sqrt 2*(KineticLangevin.obaboContractionRate m γ h : ℝ)^n*D+
      Real.sqrt 2*((6*γ/m)*h*(Real.sqrt d/Real.sqrt N)*(4*Real.sqrt L+L*h/2))+
      Real.sqrt (dθ/(N*m))) :
    error≤kiplmc2PaperConstant m L γ*
      ((Real.sqrt N*D+h*N*Real.sqrt d)*Real.exp (-m*h*(n : ℝ)/(6*γ))+
        h*Real.sqrt (N*d)+Real.sqrt (dθ/N)) := by
  let C := kiplmc2PaperConstant m L γ
  have hCb := kiplmc2PaperConstant_bounds m L γ hm hL hγ
  have hC : 0≤C := hCb.1
  have hC2 : Real.sqrt 2≤C := hCb.2.1
  have hn : 0<N := by linarith
  have hs : 0<Real.sqrt N := Real.sqrt_pos.mpr hn
  have hs1 : 1≤Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN
  have ht : 0<Real.exp (-m*h*(n : ℝ)/(6*γ)) := Real.exp_pos _
  have hmax : h≤m/(33*γ^3) := (le_div_iff₀ (by positivity : (0 : ℝ)<33*γ^3)).mpr (by nlinarith)
  have heq : L*m/(66*γ^3)=L*(m/(33*γ^3))/2 := by field_simp <;> ring
  have hinside : 4*Real.sqrt L+L*h/2 ≤4*Real.sqrt L+L*m/(66*γ^3) := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left hmax hL]
  have hcoef : Real.sqrt 2*(6*γ/m)*(4*Real.sqrt L+L*h/2)≤C := by
    apply le_trans _ hCb.2.2.1
    unfold kiplmc2PaperBiasCoefficient
    convert mul_le_mul_of_nonneg_left hinside (by positivity : (0 : ℝ)≤6*Real.sqrt 2*γ/m) using 1 <;> ring
  have hratio : Real.sqrt d/Real.sqrt N≤Real.sqrt (N*d) := by
    apply (div_le_iff₀ hs).mpr
    rw [Real.sqrt_mul hn.le]
    have hsquare := Real.sq_sqrt hn.le
    calc
      _ ≤ N*Real.sqrt d := by nlinarith [mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg d)]
      _ = (Real.sqrt N)^2*Real.sqrt d := congrArg (fun x : ℝ ↦ x*Real.sqrt d) hsquare.symm
      _ = _ := by ring
  have htrans : Real.sqrt 2*(KineticLangevin.obaboContractionRate m γ h : ℝ)^n*D ≤
      C*((Real.sqrt N*D+h*N*Real.sqrt d)*Real.exp (-m*h*(n : ℝ)/(6*γ))) := by
    have hr := kiplmc2_rate_exp_bound m γ h n
    have hi : D≤Real.sqrt N*D+h*N*Real.sqrt d := by nlinarith [mul_le_mul_of_nonneg_right hs1 hD,mul_nonneg (mul_nonneg hh hn.le) (Real.sqrt_nonneg d)]
    calc
      _ ≤ Real.sqrt 2*Real.exp (-m*h*(n : ℝ)/(6*γ))*D := by gcongr
      _ = Real.sqrt 2*(D*Real.exp (-m*h*(n : ℝ)/(6*γ))) := by ring
      _ ≤ C*((Real.sqrt N*D+h*N*Real.sqrt d)*Real.exp (-m*h*(n : ℝ)/(6*γ))) := by gcongr
  have hbias : Real.sqrt 2*((6*γ/m)*h*(Real.sqrt d/Real.sqrt N)*(4*Real.sqrt L+L*h/2)) ≤
      C*(h*Real.sqrt (N*d)) := by
    calc
      _ = (Real.sqrt 2*(6*γ/m)*(4*Real.sqrt L+L*h/2))*h*(Real.sqrt d/Real.sqrt N) := by ring
      _ ≤ C*h*Real.sqrt (N*d) := by gcongr
      _ = _ := by ring
  have hceq : Real.sqrt (dθ/(N*m))=(1/Real.sqrt m)*Real.sqrt (dθ/N) := by
    have he : dθ/(N*m)=(dθ/N)/m := by ring
    rw [he,Real.sqrt_div (div_nonneg hθ hn.le)]
    ring
  have hconcentration : Real.sqrt (dθ/(N*m))≤C*Real.sqrt (dθ/N) := by
    rw [hceq]
    exact mul_le_mul_of_nonneg_right hCb.2.2.2 (Real.sqrt_nonneg _)
  have hb := hbound.trans (add_le_add (add_le_add htrans hbias) hconcentration)
  convert hb using 1 <;> ring

/-- The supplied manuscript's KIPLMC2 theorem for the actual algorithm,
with an explicit constant depending only on m, L and gamma. -/
theorem kiplmc2_parameter_paper_bound {N dθ dx : ℕ} (hN : 0<N)
    (U : IPLA.Joint dθ dx → ℝ) (m γ h : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hm : 0<m) (hmL : m≤(L : ℝ))
    (hγ : 0<γ) (hh : 0<h) (hfriction : 4*(L : ℝ)≤γ^2) (hstep : 33*γ^3*h≤m)
    (ν : Measure (State N dθ dx)) [IsProbabilityMeasure ν]
    (hν : MemLp (id : State N dθ dx → State N dθ dx) 2 ν)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) (n : ℕ) :
    Real.sqrt (∫ z,‖IPLA.parameterCLM z-θStar‖^2
      ∂(kiplmc2Laws U γ h ((velocityTarget N dθ dx).prod ν) n).map Prod.snd) ≤
      kiplmc2PaperConstant m L γ*
        ((Real.sqrt N*ULA.wasserstein2Real ν (IPLA.gibbsTarget U)+
          h*(N : ℝ)*Real.sqrt ((dθ : ℝ)+(N : ℝ)*(dx : ℝ)))*
            Real.exp (-m*h*(n : ℝ)/(6*γ))+
          h*Real.sqrt ((N : ℝ)*((dθ : ℝ)+(N : ℝ)*(dx : ℝ)))+
          Real.sqrt ((dθ : ℝ)/(N : ℝ))) := by
  have hb := kiplmc2_parameter_bound hN U m γ h L hdiff hsc hLip hm hmL
    hγ hh hfriction hstep ν hν θStar hmax n
  have hn : (1 : ℝ)≤N := by exact_mod_cast (Nat.succ_le_iff.mpr hN)
  exact kiplmc2_paper_envelope m L γ h N ((dθ : ℝ)+(N : ℝ)*(dx : ℝ)) dθ
    (ULA.wasserstein2Real ν (IPLA.gibbsTarget U)) _ n hm L.coe_nonneg hγ hh.le hn
    (by positivity) (by positivity) ENNReal.toReal_nonneg hstep hb

end KIPLMC
