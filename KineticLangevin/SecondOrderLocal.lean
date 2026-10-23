import KineticLangevin.MildError
import KineticLangevin.RandomOperatorLp

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped NNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Friction-weighted integration of an actual Banach-valued forcing path. -/
def dampedIntegral (γ : ℝ) (F : ℝ → E) (t : ℝ) : E :=
  ∫ s in 0..t, Real.exp (-γ*(t-s)) • F s

theorem continuous_time_primitive (F : ℝ → E) (hF : Continuous F) :
    Continuous (fun t : ℝ ↦ ∫ s in 0..t,F s) := by
  exact continuous_iff_continuousAt.mpr (fun t ↦ (hF.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt)

theorem continuous_dampedIntegral (γ : ℝ) (F : ℝ → E) (hF : Continuous F) :
    Continuous (dampedIntegral γ F) := by
  have he (t : ℝ) : dampedIntegral γ F t =
      Real.exp (-γ*t) • ∫ s in 0..t,Real.exp (γ*s) • F s := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp [dampedIntegral]
    rw [smul_smul,← Real.exp_add]
    congr 2
    ring
  have hc : Continuous (fun s : ℝ ↦ Real.exp (γ*s) • F s) := by fun_prop
  rw [show dampedIntegral γ F=(fun t ↦ Real.exp (-γ*t) • ∫ s in 0..t,Real.exp (γ*s) • F s) from funext he]
  exact (by fun_prop : Continuous (fun t : ℝ ↦ Real.exp (-γ*t))).smul
    (continuous_time_primitive _ hc)

/-- The quadratic frozen-force correction uses the entire actual free-OU path. -/
def correctedVelocity (γ : ℝ) (U : ℝ → E) (F0 : E) (H0 : E →L[ℝ] E) (t : ℝ) : E :=
  U t - psi γ 1 t • F0 - H0 (dampedIntegral γ (fun s ↦ ∫ r in 0..s,U r) t)

/-- Taylor and force-memory terms in the genuine second-order velocity error. -/
def secondOrderTaylorDefect (γ : ℝ) (G X : ℝ → E) (H0 : E →L[ℝ] E) (t : ℝ) : E :=
  dampedIntegral γ (fun s ↦ G s-G 0-H0 (X s-X 0)) t

def secondOrderMemoryDefect (γ : ℝ) (G : ℝ → E) (H0 : E →L[ℝ] E) (t : ℝ) : E :=
  H0 (dampedIntegral γ (fun s ↦ ∫ r in 0..s,dampedIntegral γ G r) t)

/-- The second-order velocity error is derived from the exact mild and kinematic equations. -/
theorem correctedVelocity_error_identity (γ T : ℝ) (hT : 0≤T)
    (V X U G : ℝ → E) (hV : Continuous V) (hX : Continuous X)
    (hU : Continuous U) (hG : Continuous G) (H0 : E →L[ℝ] E)
    (hmild : ∀ t ∈ Icc 0 T,V t=U t-dampedIntegral γ G t)
    (hkin : ∀ t ∈ Icc 0 T,X t-X 0=∫ r in 0..t,V r) :
    correctedVelocity γ U (G 0) H0 T-V T=
      secondOrderTaylorDefect γ G X H0 T-secondOrderMemoryDefect γ G H0 T := by
  have hcD := continuous_dampedIntegral γ G hG
  have hcI := continuous_time_primitive V hV
  have hcU := continuous_time_primitive U hU
  have hcDI := continuous_time_primitive (dampedIntegral γ G) hcD
  have hUX (s : ℝ) (hs : s∈Icc 0 T) :
      (∫ r in 0..s,U r)=(X s-X 0)+(∫ r in 0..s,dampedIntegral γ G r) := by
    rw [hkin s hs,← intervalIntegral.integral_add (hV.intervalIntegrable _ _) (hcD.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hs.1] at hr
    change U r=V r+dampedIntegral γ G r
    rw [hmild r ⟨hr.1,hr.2.trans hs.2⟩]
    abel
  have hsum : dampedIntegral γ (fun s ↦ ∫ r in 0..s,U r) T=
      dampedIntegral γ (fun s ↦ X s-X 0) T+
        dampedIntegral γ (fun s ↦ ∫ r in 0..s,dampedIntegral γ G r) T := by
    change (∫ s in 0..T,Real.exp (-γ*(T-s)) • (∫ r in 0..s,U r))=
      (∫ s in 0..T,Real.exp (-γ*(T-s)) • (X s-X 0))+
      (∫ s in 0..T,Real.exp (-γ*(T-s)) • (∫ r in 0..s,dampedIntegral γ G r))
    rw [← intervalIntegral.integral_add
      (((by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(T-s)) • (X s-X 0)))).intervalIntegrable _ _)
      (((by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(T-s)) • ∫ r in 0..s,dampedIntegral γ G r))).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hT] at hs
    change Real.exp (-γ*(T-s)) • (∫ r in 0..s,U r)=_
    rw [hUX s hs,smul_add]
  have hcomm : dampedIntegral γ (fun s ↦ H0 (X s-X 0)) T=
      H0 (dampedIntegral γ (fun s ↦ X s-X 0) T) := by
    unfold dampedIntegral
    rw [← H0.intervalIntegral_comp_comm
      (((by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(T-s)) • (X s-X 0)))).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro s _
    simp
  have hcorr : H0 (dampedIntegral γ (fun s ↦ ∫ r in 0..s,U r) T)=
      dampedIntegral γ (fun s ↦ H0 (X s-X 0)) T+secondOrderMemoryDefect γ G H0 T := by
    rw [hsum,map_add,← hcomm]
    rfl
  have hiG : IntervalIntegrable (fun s : ℝ ↦ Real.exp (-γ*(T-s)) • G s) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(T-s)) • G s)).intervalIntegrable _ _
  have hi0 : IntervalIntegrable (fun s : ℝ ↦ Real.exp (-γ*(T-s)) • G 0) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(T-s)) • G 0)).intervalIntegrable _ _
  have hiH : IntervalIntegrable (fun s : ℝ ↦ Real.exp (-γ*(T-s)) • H0 (X s-X 0)) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ ↦ Real.exp (-γ*(T-s)) • H0 (X s-X 0))).intervalIntegrable _ _
  have hTaylor : secondOrderTaylorDefect γ G X H0 T=
      dampedIntegral γ G T-psi γ 1 T • G 0-
        dampedIntegral γ (fun s ↦ H0 (X s-X 0)) T := by
    unfold secondOrderTaylorDefect dampedIntegral
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub (hiG.sub hi0) hiH,
      intervalIntegral.integral_sub hiG hi0,intervalIntegral.integral_smul_const,
      integral_reverse_exponential]
  rw [correctedVelocity,hmild T ⟨hT,le_rfl⟩,hcorr,hTaylor]
  abel

/-- Exponential damping never enlarges a polynomial envelope on forward time. -/
theorem dampedIntegral_norm_le_pow (γ t C : ℝ) (hγ : 0≤γ) (ht : 0≤t)
    (F : ℝ → E) (n : ℕ) (hbound : ∀ s ∈ Icc 0 t,‖F s‖≤C*s^n) :
    ‖dampedIntegral γ F t‖≤C*t^(n+1)/(n+1) := by
  have hb (s : ℝ) (hs : s∈Ioc 0 t) :
      ‖Real.exp (-γ*(t-s)) • F s‖≤C*s^n := by
    have he : Real.exp (-γ*(t-s))≤1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hγ (sub_nonneg.mpr hs.2)])
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact (mul_le_of_le_one_left (norm_nonneg _) he).trans (hbound s ⟨hs.1.le,hs.2⟩)
  calc
    _ ≤ ∫ s in 0..t,C*s^n := intervalIntegral.norm_integral_le_of_norm_le ht
      (Filter.Eventually.of_forall hb)
      ((by fun_prop : Continuous (fun s : ℝ ↦ C*s^n)).intervalIntegrable _ _)
    _ = _ := by rw [intervalIntegral.integral_const_mul,integral_pow];simp;ring

/-- The undamped primitive obeys the same exact polynomial integration rule. -/
theorem primitive_norm_le_pow (t C : ℝ) (ht : 0≤t) (F : ℝ → E) (n : ℕ)
    (hbound : ∀ s ∈ Icc 0 t,‖F s‖≤C*s^n) :
    ‖∫ s in 0..t,F s‖≤C*t^(n+1)/(n+1) := by
  simpa only [dampedIntegral,neg_zero,zero_mul,Real.exp_zero,one_smul] using
    dampedIntegral_norm_le_pow 0 t C le_rfl ht F n hbound

/-- Three actual nested integrals give the sharp cubic memory term. -/
theorem secondOrderMemoryDefect_bound (γ T G0 : ℝ) (hγ : 0≤γ) (G : ℝ → E)
    (H0 : E →L[ℝ] E) (hG : ∀ s∈Icc 0 T,‖G s‖≤G0)
    {t : ℝ} (ht : t∈Icc 0 T) :
    ‖secondOrderMemoryDefect γ G H0 t‖≤‖H0‖*G0*t^3/6 := by
  have hD (r : ℝ) (hr : r∈Icc 0 T) : ‖dampedIntegral γ G r‖≤G0*r := by
    simpa using dampedIntegral_norm_le_pow γ r G0 hγ hr.1 G 0
      (fun s hs ↦ by simpa using hG s ⟨hs.1,hs.2.trans hr.2⟩)
  have hI (s : ℝ) (hs : s∈Icc 0 T) :
      ‖∫ r in 0..s,dampedIntegral γ G r‖≤G0/2*s^2 := by
    have hb := primitive_norm_le_pow s G0 hs.1 (dampedIntegral γ G) 1
      (fun r hr ↦ by simpa using hD r ⟨hr.1,hr.2.trans hs.2⟩)
    norm_num at hb
    nlinarith only [hb]
  have hb := dampedIntegral_norm_le_pow γ t (G0/2) hγ ht.1
    (fun s ↦ ∫ r in 0..s,dampedIntegral γ G r) 2
    (fun s hs ↦ hI s ⟨hs.1,hs.2.trans ht.2⟩)
  norm_num at hb
  exact (H0.le_opNorm _).trans (by nlinarith only [mul_le_mul_of_nonneg_left hb (norm_nonneg H0)])

/-- The actual Taylor-plus-memory decomposition gives the source cubic velocity bound. -/
theorem correctedVelocity_error_bound (γ T R G0 : ℝ) (hγ : 0≤γ) (hT : 0≤T)
    (V X U G : ℝ → E) (hV : Continuous V) (hX : Continuous X)
    (hU : Continuous U) (hG : Continuous G) (H0 : E →L[ℝ] E)
    (hmild : ∀ t∈Icc 0 T,V t=U t-dampedIntegral γ G t)
    (hkin : ∀ t∈Icc 0 T,X t-X 0=∫ r in 0..t,V r)
    (hTaylor : ∀ t∈Icc 0 T,‖G t-G 0-H0 (X t-X 0)‖≤R*t^2)
    (hscore : ∀ t∈Icc 0 T,‖G t‖≤G0) :
    ‖correctedVelocity γ U (G 0) H0 T-V T‖≤(2*R+‖H0‖*G0)*T^3/6 := by
  rw [correctedVelocity_error_identity γ T hT V X U G hV hX hU hG H0 hmild hkin]
  have hA := dampedIntegral_norm_le_pow γ T R hγ hT
    (fun s ↦ G s-G 0-H0 (X s-X 0)) 2 hTaylor
  norm_num only [Nat.reduceAdd,Nat.cast_ofNat] at hA
  have hB := secondOrderMemoryDefect_bound γ T G0 hγ G H0 hscore ⟨hT,le_rfl⟩
  exact (norm_sub_le _ _).trans (by dsimp [secondOrderTaylorDefect] at *;nlinarith only [hA,hB])

/-- Position is the time integral of the corrected velocity, not a separate discretization. -/
def correctedPosition (γ : ℝ) (U : ℝ → E) (x0 F0 : E) (H0 : E →L[ℝ] E) (t : ℝ) : E :=
  x0+∫ s in 0..t,correctedVelocity γ U F0 H0 s

theorem continuous_correctedVelocity (γ : ℝ) (U : ℝ → E) (hU : Continuous U)
    (F0 : E) (H0 : E →L[ℝ] E) : Continuous (correctedVelocity γ U F0 H0) := by
  have hc := continuous_time_primitive U hU
  have hd := continuous_dampedIntegral γ (fun s ↦ ∫ r in 0..s,U r) hc
  exact (hU.sub ((continuous_psi γ 1).smul continuous_const)).sub (H0.continuous.comp hd)

/-- Integrating the cubic velocity estimate yields the quartic position estimate. -/
theorem correctedPosition_error_bound (γ T R G0 : ℝ) (hγ : 0≤γ) (hT : 0≤T)
    (V X U G : ℝ → E) (hV : Continuous V) (hX : Continuous X)
    (hU : Continuous U) (hG : Continuous G) (H0 : E →L[ℝ] E)
    (hmild : ∀ t∈Icc 0 T,V t=U t-dampedIntegral γ G t)
    (hkin : ∀ t∈Icc 0 T,X t-X 0=∫ r in 0..t,V r)
    (hTaylor : ∀ t∈Icc 0 T,‖G t-G 0-H0 (X t-X 0)‖≤R*t^2)
    (hscore : ∀ t∈Icc 0 T,‖G t‖≤G0) :
    ‖correctedPosition γ U (X 0) (G 0) H0 T-X T‖≤(2*R+‖H0‖*G0)*T^4/24 := by
  have he : correctedPosition γ U (X 0) (G 0) H0 T-X T=
      ∫ s in 0..T,correctedVelocity γ U (G 0) H0 s-V s := by
    rw [intervalIntegral.integral_sub
      ((continuous_correctedVelocity γ U hU (G 0) H0).intervalIntegrable _ _) (hV.intervalIntegrable _ _)]
    have hk := hkin T ⟨hT,le_rfl⟩
    dsimp [correctedPosition]
    rw [← hk]
    abel
  rw [he]
  have hb := primitive_norm_le_pow T ((2*R+‖H0‖*G0)/6) hT
    (fun s ↦ correctedVelocity γ U (G 0) H0 s-V s) 3 (fun s hs ↦ by
      have hi := correctedVelocity_error_bound γ s R G0 hγ hs.1 V X U G hV hX hU hG H0
        (fun r hr ↦ hmild r ⟨hr.1,hr.2.trans hs.2⟩)
        (fun r hr ↦ hkin r ⟨hr.1,hr.2.trans hs.2⟩)
        (fun r hr ↦ hTaylor r ⟨hr.1,hr.2.trans hs.2⟩)
        (fun r hr ↦ hscore r ⟨hr.1,hr.2.trans hs.2⟩)
      nlinarith only [hi])
  norm_num at hb
  nlinarith only [hb]

/-- The genuine cubic/quartic component estimates imply the paper's quarter-constant in transformed coordinates. -/
theorem secondOrder_component_transform_bound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (γ T C : ℝ) (hγ : 0≤γ) (hT : 0≤T) (hC : 0≤C) (hsmall : γ*T≤1/5)
    (v x : F) (hv : ‖v‖≤C*T^3/6) (hx : ‖x‖≤C*T^4/24) :
    transformNorm γ 0 (v,x)≤C*T^3/4 := by
  let B : ℝ := C*T^3
  have hB : 0≤B := by dsimp [B];positivity
  have hv' : ‖v‖≤B/6 := hv
  have hx' : ‖x‖≤B*T/24 := by dsimp [B];nlinarith only [hx]
  have hsum : ‖v+γ • x‖≤(7/40 : ℝ)*B := by
    have hs := norm_add_le v (γ • x)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hγ] at hs
    have h1 := mul_le_mul_of_nonneg_left hx' hγ
    have h2 := mul_le_mul_of_nonneg_left hsmall hB
    nlinarith only [hs,hv',h1,h2]
  apply transformNorm_le_of_energy_le γ 0 (C*T^3/4) (v,x) (by positivity)
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤(7/40 : ℝ)*B)).mpr hsum
  have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤B/6)).mpr hv'
  simp only [transformEnergy,transform,sub_zero,zero_smul,add_zero,norm_neg]
  change _≤(C*T^3/4)^2
  change _≤(B/4)^2
  nlinarith only [hs,hv2,sq_nonneg B]

/-- The actual second-order local phase error satisfies the source quarter-constant. -/
theorem correctedPhase_error_bound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (γ T R G0 : ℝ) (hγ : 0≤γ) (hT : 0≤T) (hR : 0≤R) (hG0 : 0≤G0)
    (hsmall : γ*T≤1/5) (V X U G : ℝ → F) (hV : Continuous V) (hX : Continuous X)
    (hU : Continuous U) (hG : Continuous G) (H0 : F →L[ℝ] F)
    (hmild : ∀ t∈Icc 0 T,V t=U t-dampedIntegral γ G t)
    (hkin : ∀ t∈Icc 0 T,X t-X 0=∫ r in 0..t,V r)
    (hTaylor : ∀ t∈Icc 0 T,‖G t-G 0-H0 (X t-X 0)‖≤R*t^2)
    (hscore : ∀ t∈Icc 0 T,‖G t‖≤G0) :
    transformNorm γ 0 (correctedVelocity γ U (G 0) H0 T-V T,
      correctedPosition γ U (X 0) (G 0) H0 T-X T)≤(2*R+‖H0‖*G0)*T^3/4 :=
  secondOrder_component_transform_bound γ T _ hγ hT (by positivity) hsmall _ _
    (correctedVelocity_error_bound γ T R G0 hγ hT V X U G hV hX hU hG H0 hmild hkin hTaylor hscore)
    (correctedPosition_error_bound γ T R G0 hγ hT V X U G hV hX hU hG H0 hmild hkin hTaylor hscore)

end KineticLangevin
