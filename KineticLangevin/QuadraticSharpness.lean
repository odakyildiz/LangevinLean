import KineticLangevin.Friction

noncomputable section
namespace KineticLangevin

/-- Position difference for one overdamped quadratic mode, with initial position one and common initial velocity zero. -/
def quadraticPositionResponse (a b t : ℝ) : ℝ :=
  (b*Real.exp (-a*t)-a*Real.exp (-b*t))/(b-a)

def quadraticVelocityResponse (a b t : ℝ) : ℝ :=
  a*b*(Real.exp (-b*t)-Real.exp (-a*t))/(b-a)

@[simp] theorem quadraticPositionResponse_zero (a b : ℝ) (hab : a≠b) :
    quadraticPositionResponse a b 0=1 := by
  simp only [quadraticPositionResponse,mul_zero,Real.exp_zero,mul_one]
  exact div_self (sub_ne_zero.mpr hab.symm)

@[simp] theorem quadraticVelocityResponse_zero (a b : ℝ) : quadraticVelocityResponse a b 0=0 := by
  simp [quadraticVelocityResponse]

/-- These are genuine solutions of the deterministic quadratic kinetic equations. -/
theorem quadraticResponse_derivatives (a b t : ℝ) :
    HasDerivAt (quadraticPositionResponse a b) (quadraticVelocityResponse a b t) t ∧
    HasDerivAt (quadraticVelocityResponse a b)
      (-(a+b)*quadraticVelocityResponse a b t-(a*b)*quadraticPositionResponse a b t) t := by
  have ha := (((hasDerivAt_id t).const_mul (-a)).exp)
  have hb := (((hasDerivAt_id t).const_mul (-b)).exp)
  constructor
  · convert ((ha.const_mul b).sub (hb.const_mul a)).div_const (b-a) using 1
    · funext s
      dsimp [quadraticPositionResponse]
    · dsimp [quadraticVelocityResponse]
      ring
  · convert ((hb.sub ha).const_mul (a*b)).div_const (b-a) using 1
    · funext s
      dsimp [quadraticVelocityResponse]
    · dsimp [quadraticPositionResponse,quadraticVelocityResponse]
      ring

/-- The slow mode cannot be cancelled when the two copies start with equal velocity. -/
theorem quadraticPositionResponse_slow_lower (a b t : ℝ) (ha : 0≤a) (hab : a<b) (ht : 0≤t) :
    Real.exp (-a*t)≤quadraticPositionResponse a b t := by
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  have he : Real.exp (-b*t)≤Real.exp (-a*t) := Real.exp_le_exp.mpr (by nlinarith)
  have hm := mul_nonneg ha (sub_nonneg.mpr he)
  nlinarith

/-- No finite prefactor can support any exponent strictly faster than the genuine slow quadratic rate. -/
theorem quadraticPositionResponse_no_faster_rate (a b β C : ℝ) (ha : 0≤a) (hab : a<b) (hβ : a<β) :
    ∃ t : ℝ,0≤t ∧ C*Real.exp (-β*t)<quadraticPositionResponse a b t := by
  let t := Real.log (|C|+1)/(β-a)
  have ht : 0≤t := div_nonneg (Real.log_nonneg (by linarith [abs_nonneg C])) (by linarith)
  have he : Real.exp ((β-a)*t)=|C|+1 := by
    dsimp [t]
    rw [mul_div_cancel₀ _ (sub_ne_zero.mpr hβ.ne'),Real.exp_log (by positivity)]
  have hex : Real.exp (-a*t)=(|C|+1)*Real.exp (-β*t) := by
    rw [← he,← Real.exp_add]
    congr 1
    ring
  refine ⟨t,ht,lt_of_lt_of_le ?_ (quadraticPositionResponse_slow_lower a b t ha hab ht)⟩
  rw [hex]
  exact mul_lt_mul_of_pos_right (by linarith [le_abs_self C]) (Real.exp_pos _)

/-- The critical repeated-root position response carries its unavoidable polynomial prefactor. -/
def criticalQuadraticPosition (a t : ℝ) : ℝ := (1+a*t)*Real.exp (-a*t)

def criticalQuadraticVelocity (a t : ℝ) : ℝ := -(a^2)*t*Real.exp (-a*t)

/-- At repeated roots, the exact quadratic response still solves the kinetic ODE. -/
theorem criticalQuadratic_derivatives (a t : ℝ) :
    HasDerivAt (criticalQuadraticPosition a) (criticalQuadraticVelocity a t) t ∧
    HasDerivAt (criticalQuadraticVelocity a)
      (-(2*a)*criticalQuadraticVelocity a t-a^2*criticalQuadraticPosition a t) t := by
  have he := (((hasDerivAt_id t).const_mul (-a)).exp)
  constructor
  · convert (((hasDerivAt_id t).const_mul a).const_add 1).mul he using 1
    · funext s
      dsimp [criticalQuadraticPosition]
    · dsimp [criticalQuadraticVelocity]
      ring
  · convert (((hasDerivAt_id t).const_mul (-(a^2))).mul he) using 1
    · funext s
      dsimp [criticalQuadraticVelocity]
    · dsimp [criticalQuadraticPosition,criticalQuadraticVelocity]
      ring

/-- At critical damping, the boundary exponent itself admits no finite constant prefactor. -/
theorem criticalQuadratic_prefactor_obstruction (a C : ℝ) (ha : 0<a) :
    ∃ t : ℝ,0≤t ∧ C*Real.exp (-a*t)<criticalQuadraticPosition a t := by
  let t := (|C|+1)/a
  have ht : 0≤t := by dsimp [t]; positivity
  have he : a*t=|C|+1 := by dsimp [t];exact mul_div_cancel₀ _ ha.ne'
  refine ⟨t,ht,?_⟩
  unfold criticalQuadraticPosition
  rw [he]
  exact mul_lt_mul_of_pos_right (by linarith [le_abs_self C]) (Real.exp_pos _)

/-- The two real quadratic roots give exactly the rate and friction in the source overdamped regime. -/
theorem quadratic_slow_fast_roots (γ m : ℝ) (hγ : 0<γ) (hm : 0<m) (hdisc : 4*m<γ^2) :
    let a := (γ-Real.sqrt (γ^2-4*m))/2
    let b := (γ+Real.sqrt (γ^2-4*m))/2
    0<a ∧ a<b ∧ a+b=γ ∧ a*b=m := by
  dsimp only
  have hs : 0<Real.sqrt (γ^2-4*m) := Real.sqrt_pos.mpr (by linarith)
  have hsq := Real.sq_sqrt (by linarith : 0≤γ^2-4*m)
  refine ⟨by nlinarith,by linarith,by ring,?_⟩
  nlinarith

end KineticLangevin
