import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # A corrected condition-number refinement for the KLMC2 step prescription

These scalar results concern the source's explicitly tail-free refinement.
They are certificates for that step/count prescription, not lower bounds on
the complexity of the stochastic algorithm. The printed expression can only
be used uniformly after retaining the usual condition number as well.
-/
noncomputable section
set_option maxHeartbeats 1000000
namespace KineticLangevin

/-- The ordinary gradient condition number. -/
def kineticConditionNumber (m M : ℝ) : ℝ := M/m

/-- The source's actual Hessian condition number, including its dimension factor. -/
def sourceHessianConditionNumber (m M M2 p : ℝ) : ℝ :=
  (M2 ^ (2/3 : ℝ) + M*p ^ (-1/3 : ℝ))/m

/-- The dimensionless form, with κ=M/m and η=M₂/m^(3/2). -/
def normalizedHessianConditionNumber (κ η p : ℝ) : ℝ :=
  η ^ (2/3 : ℝ) + κ*p ^ (-1/3 : ℝ)

/-- Normalize the actual source definition; no relation between the two condition
numbers is added as a premise. -/
theorem sourceHessianConditionNumber_normalize (m M M2 p : ℝ) (hm : 0<m) (hM2 : 0≤M2) :
    sourceHessianConditionNumber m M M2 p =
      normalizedHessianConditionNumber (M/m) (M2/(m*Real.sqrt m)) p := by
  have hden : (m*Real.sqrt m) ^ (2/3 : ℝ)=m := by
    rw [Real.sqrt_eq_rpow]
    have he : m*m ^ (1/2 : ℝ)=m ^ (3/2 : ℝ) := by
      rw [show (3/2 : ℝ)=1+1/2 by norm_num,Real.rpow_add hm,Real.rpow_one]
    rw [he,←Real.rpow_mul hm.le]
    norm_num
  rw [sourceHessianConditionNumber,normalizedHessianConditionNumber,
    Real.div_rpow hM2 (mul_nonneg hm.le (Real.sqrt_nonneg _)) _,hden]
  ring

/-- The genuine source quantity controls the squared Hessian ratio and the
cubed gradient ratio. These are consequences of its definition. -/
theorem normalizedHessianConditionNumber_cubes (κ η p : ℝ)
    (hκ : 0<κ) (hη : 0≤η) (hp : 0<p) :
    0<normalizedHessianConditionNumber κ η p ∧
      η^2≤(normalizedHessianConditionNumber κ η p)^3 ∧
      κ^3≤p*(normalizedHessianConditionNumber κ η p)^3 := by
  let ρ := normalizedHessianConditionNumber κ η p
  have hpw : 0<p ^ (-1/3 : ℝ) := Real.rpow_pos_of_pos hp _
  have hρ : 0<ρ := add_pos_of_nonneg_of_pos (Real.rpow_nonneg hη _) (mul_pos hκ hpw)
  have h1 : η ^ (2/3 : ℝ)≤ρ := le_add_of_nonneg_right (mul_nonneg hκ.le hpw.le)
  have h2 : κ*p ^ (-1/3 : ℝ)≤ρ := le_add_of_nonneg_left (Real.rpow_nonneg hη _)
  have he1 : (η ^ (2/3 : ℝ))^3=η^2 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hη]
    norm_num
  have he2 : (p ^ (-1/3 : ℝ))^3=1/p := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp.le]
    norm_num [Real.rpow_neg_one,one_div]
  have ha : η^2≤ρ^3 := by
    rw [←he1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hη _) h1 3
  have hb : κ^3≤p*ρ^3 := by
    have hh := pow_le_pow_left₀ (mul_nonneg hκ.le hpw.le) h2 3
    rw [mul_pow,he2] at hh
    have hc := mul_le_mul_of_nonneg_left hh hp.le
    field_simp at hc
    nlinarith
  exact ⟨hρ,ha,hb⟩

/-- The exact dimensionless reciprocal-step/count coefficient, including the
source constants, after γ=√(m+M) and normalized accuracy ε/√m. The Gaussian tail
is excluded here exactly as it is in the source's informal refinement. -/
def secondOrderNormalizedWork (κ η p ε : ℝ) : ℝ :=
  4*Real.sqrt (1+κ)*max (5*κ*Real.sqrt (1+κ))
    (max (4*Real.sqrt (5*p)*η)
      (Real.sqrt ((4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p)/ε)))

/-- The two dimensionless comparison terms from the source's proposed scaling. -/
def secondOrderRefinement (ρ p ε : ℝ) : ℝ :=
  Real.sqrt p*ρ^2+Real.sqrt (p/ε)*ρ ^ (5/4 : ℝ)

/-- A scalar bound with all hypotheses justified later by the actual condition
number definition. Retaining R≥κ is essential. -/
theorem secondOrderNormalizedWork_le (κ η p ε R : ℝ)
    (hκ : 1≤κ) (hη : 0≤η) (hp : 1≤p) (hε : 0<ε)
    (hκR : κ≤R) (hηR : η^2≤R^3) :
    secondOrderNormalizedWork κ η p ε≤64*secondOrderRefinement R p ε := by
  have hκ0 : 0≤κ := by linarith
  have hR : 0<R := by linarith
  have hp0 : 0≤p := by linarith
  have hsR := Real.sq_sqrt hR.le
  have hsp := Real.sq_sqrt hp0
  have hsk := Real.sq_sqrt hκ0
  have hsg := Real.sq_sqrt (by linarith : 0≤1+κ)
  have hRhalf : η≤R*Real.sqrt R := by
    have hsq : (R*Real.sqrt R)^2=R^3 := by
      calc
        _ = R^2*(Real.sqrt R)^2 := by ring
        _ = _ := by rw [hsR];ring
    apply (sq_le_sq₀ hη (by positivity : 0≤R*Real.sqrt R)).mp
    rw [hsq]
    exact hηR
  have hsp1 : 1≤Real.sqrt p := by nlinarith [Real.sqrt_nonneg p]
  have hspp : Real.sqrt p≤p := by nlinarith [Real.sqrt_nonneg p]
  have hskR : Real.sqrt κ≤Real.sqrt R := Real.sqrt_le_sqrt hκR
  have hkR : κ*Real.sqrt κ≤R*Real.sqrt R :=
    mul_le_mul hκR hskR (Real.sqrt_nonneg κ) hR.le
  have hforce : 4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p≤8*p*(R*Real.sqrt R) := by
    have hs2 : Real.sqrt 2≤2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
    have ha := mul_le_mul_of_nonneg_right hRhalf hp0
    have hb := mul_le_mul hkR hspp (Real.sqrt_nonneg p) (by positivity : 0≤R*Real.sqrt R)
    have hc := mul_le_mul_of_nonneg_right hs2 (by positivity : 0≤κ*Real.sqrt κ*Real.sqrt p)
    nlinarith
  let A := Real.sqrt p*R^2
  let B := Real.sqrt (p/ε)*R ^ (5/4 : ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  have hB : 0≤B := by dsimp [B];positivity
  have hA2 : A^2=p*R^4 := by dsimp only [A];rw [mul_pow,hsp];ring
  have hB2 : B^2=(p/ε)*(R^2*Real.sqrt R) := by
    have he : (R ^ (5/4 : ℝ))^2=R^2*Real.sqrt R := by
      rw [←Real.rpow_natCast,←Real.rpow_mul hR.le]
      norm_num
      rw [show (5/2 : ℝ)=2+1/2 by norm_num,Real.rpow_add hR,Real.rpow_ofNat,←Real.sqrt_eq_rpow]
    dsimp [B]
    rw [mul_pow,Real.sq_sqrt (by positivity : 0≤p/ε),he]
  have hstable : 4*Real.sqrt (1+κ)*(5*κ*Real.sqrt (1+κ))≤64*(A+B) := by
    have ha : κ*(1+κ)≤2*R^2 := by
      have he := mul_le_mul hκR (by linarith : 1+κ≤2*R) (by linarith : 0≤1+κ) hR.le
      convert he using 1;ring
    have hb : R^2≤A := by dsimp [A];nlinarith [mul_nonneg (sub_nonneg.mpr hsp1) (sq_nonneg R)]
    calc
      _ = 20*κ*(1+κ) := by
        calc
          _ = 20*κ*(Real.sqrt (1+κ))^2 := by ring
          _ = _ := by rw [hsg]
      _ ≤ 40*R^2 := by linarith
      _ ≤ 64*(A+B) := by linarith
  have hHess : 4*Real.sqrt (1+κ)*(4*Real.sqrt (5*p)*η)≤64*(A+B) := by
    have hs5 := Real.sq_sqrt (by positivity : 0≤5*p)
    have hprod : (1+κ)*η^2≤2*R^4 := by
      have hh := mul_le_mul (by linarith : 1+κ≤2*R) hηR (sq_nonneg η) (by positivity : 0≤2*R)
      convert hh using 1;ring
    have hsq : (4*Real.sqrt (1+κ)*(4*Real.sqrt (5*p)*η))^2≤(64*A)^2 := by
      have he : (4*Real.sqrt (1+κ)*(4*Real.sqrt (5*p)*η))^2=1280*p*((1+κ)*η^2) := by
        calc
          _ = 256*(Real.sqrt (1+κ))^2*(Real.sqrt (5*p))^2*η^2 := by ring
          _ = _ := by rw [hsg,hs5];ring
      rw [he,mul_pow,hA2]
      nlinarith only [mul_le_mul_of_nonneg_left hprod hp0,mul_nonneg hp0 (pow_nonneg hR.le 4)]
    have he : 4*Real.sqrt (1+κ)*(4*Real.sqrt (5*p)*η)≤64*A := by
      exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    linarith
  have hbias : 4*Real.sqrt (1+κ)*Real.sqrt ((4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p)/ε)≤64*(A+B) := by
    have hpos : 0≤(4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p)/ε := by positivity
    have hs := Real.sq_sqrt hpos
    have hdiv := (div_le_div_iff_of_pos_right hε).mpr hforce
    have hprod : (1+κ)*((4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p)/ε)≤
        16*(p/ε)*(R^2*Real.sqrt R) := by
      have hh := mul_le_mul_of_nonneg_left hdiv (by linarith : 0≤1+κ)
      have hh' := mul_le_mul_of_nonneg_right (by linarith : 1+κ≤2*R)
        (by positivity : 0≤8*p*(R*Real.sqrt R)/ε)
      calc
        _ ≤ (1+κ)*(8*p*(R*Real.sqrt R)/ε) := hh
        _ ≤ (2*R)*(8*p*(R*Real.sqrt R)/ε) := hh'
        _ = _ := by ring
    have hsq : (4*Real.sqrt (1+κ)*Real.sqrt ((4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p)/ε))^2≤(16*B)^2 := by
      calc
        _ = 16*(1+κ)*((4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p)/ε) := by
          calc
            _ = 16*(Real.sqrt (1+κ))^2*(Real.sqrt ((4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p)/ε))^2 := by ring
            _ = _ := by rw [hsg,hs]
        _ ≤ 256*((p/ε)*(R^2*Real.sqrt R)) := by linarith
        _ = _ := by rw [mul_pow,hB2];ring
    have he : 4*Real.sqrt (1+κ)*Real.sqrt ((4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p)/ε)≤16*B := by
      exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    linarith
  rw [secondOrderNormalizedWork,mul_max_of_nonneg _ _ (by positivity),mul_max_of_nonneg _ _ (by positivity)]
  exact max_le hstable (max_le hHess hbias)

/-- Corrected refinement using max(κ,κ₂), valid without the unprinted comparison
κ≤κ₂. It is linked to the source's actual fractional-power definition. -/
theorem secondOrderNormalizedWork_source_bound (κ η p ε : ℝ)
    (hκ : 1≤κ) (hη : 0≤η) (hp : 1≤p) (hε : 0<ε) :
    secondOrderNormalizedWork κ η p ε≤
      64*secondOrderRefinement (max κ (normalizedHessianConditionNumber κ η p)) p ε := by
  have hc := normalizedHessianConditionNumber_cubes κ η p (by linarith) hη (by linarith)
  exact secondOrderNormalizedWork_le κ η p ε _ hκ hη hp hε (le_max_left _ _)
    (hc.2.1.trans (pow_le_pow_left₀ hc.1.le (le_max_right _ _) 3))

/-- The printed form is justified if its Hessian condition number also bounds
κ. That extra comparison is stated explicitly here. -/
theorem secondOrderNormalizedWork_source_regime (κ η p ε : ℝ)
    (hκ : 1≤κ) (hη : 0≤η) (hp : 1≤p) (hε : 0<ε)
    (hregime : κ≤normalizedHessianConditionNumber κ η p) :
    secondOrderNormalizedWork κ η p ε≤
      64*secondOrderRefinement (normalizedHessianConditionNumber κ η p) p ε := by
  simpa only [max_eq_right hregime] using secondOrderNormalizedWork_source_bound κ η p ε hκ hη hp hε

/-- The physical source parameters satisfy the corrected max-condition-number
refinement, rather than silently identifying κ with κ₂. -/
theorem secondOrderNormalizedWork_physical_bound (m M M2 p ε : ℝ)
    (hm : 0<m) (hmM : m≤M) (hM2 : 0≤M2) (hp : 1≤p) (hε : 0<ε) :
    secondOrderNormalizedWork (M/m) (M2/(m*Real.sqrt m)) p ε≤
      64*secondOrderRefinement (max (kineticConditionNumber m M)
        (sourceHessianConditionNumber m M M2 p)) p ε := by
  rw [sourceHessianConditionNumber_normalize m M M2 p hm hM2]
  exact secondOrderNormalizedWork_source_bound _ _ p ε
    ((le_div_iff₀ hm).mpr (by simpa using hmM)) (by positivity) hp hε


/-- An exact positive-parameter family makes the source condition number equal
to two although κ=t² is arbitrarily large: η=1 and p=t⁶. -/
theorem normalizedHessianConditionNumber_family (t : ℝ) (ht : 0<t) :
    normalizedHessianConditionNumber (t^2) 1 (t^6)=2 := by
  have he : (t^6) ^ (-1/3 : ℝ)=(t^2)⁻¹ := by
    calc
      _ = (t ^ (6 : ℝ)) ^ (-1/3 : ℝ) := by rw [Real.rpow_ofNat]
      _ = t ^ (-2 : ℝ) := by rw [←Real.rpow_mul ht.le];norm_num
      _ = _ := by rw [show (-2 : ℝ)=-(2 : ℝ) by norm_num,Real.rpow_neg ht.le,Real.rpow_ofNat]
  simp only [normalizedHessianConditionNumber,Real.one_rpow,he,mul_inv_cancel₀ (pow_ne_zero 2 ht.ne')]
  norm_num

/-- The stability part of the actual normalized prescription alone costs at
least 20κ². This is an algebraic budget bound, not an algorithmic lower bound. -/
theorem secondOrderNormalizedWork_stability_lower (κ η p ε : ℝ) (hκ : 0≤κ) :
    20*κ^2≤secondOrderNormalizedWork κ η p ε := by
  have hs := Real.sq_sqrt (by linarith : 0≤1+κ)
  have he := mul_le_mul_of_nonneg_left (le_max_left
    (5*κ*Real.sqrt (1+κ))
    (max (4*Real.sqrt (5*p)*η)
      (Real.sqrt ((4*η*p+2*Real.sqrt 2*κ*Real.sqrt κ*Real.sqrt p)/ε))))
    (by positivity : 0≤4*Real.sqrt (1+κ))
  have hid : 4*Real.sqrt (1+κ)*(5*κ*Real.sqrt (1+κ))=20*κ*(1+κ) := by
    calc
      _ = 20*κ*(Real.sqrt (1+κ))^2 := by ring
      _ = _ := by rw [hs]
  rw [hid] at he
  exact (by nlinarith : 20*κ^2≤20*κ*(1+κ)).trans he

/-- On the exact source family κ=t², η=1, p=t⁶, ε=1 the proposed expression
is at most 8t³, whereas the true prescription costs at least 20t⁴. -/
theorem secondOrderRefinement_family_upper (t : ℝ) (ht : 0<t) :
    secondOrderRefinement (normalizedHessianConditionNumber (t^2) 1 (t^6)) (t^6) 1≤8*t^3 := by
  have hs : Real.sqrt (t^6)=t^3 := by
    rw [show t^6=(t^3)^2 by ring,Real.sqrt_sq (pow_nonneg ht.le 3)]
  have hr : (2 : ℝ) ^ (5/4 : ℝ)≤4 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : (5/4:ℝ)≤2)
    norm_num at hh ⊢
    exact hh
  rw [normalizedHessianConditionNumber_family t ht,secondOrderRefinement,div_one,hs]
  nlinarith [mul_le_mul_of_nonneg_left hr (pow_nonneg ht.le 3)]

/-- No dimension-uniform multiplicative constant can repair the printed
condition-number expression without an additional comparison or factor.
Here the dimensions are genuine natural numbers n⁶. This only disproves the
algebraic step/count simplification, not a stochastic algorithm lower bound. -/
theorem secondOrderRefinement_no_uniform_constant (C : ℝ) (hC : 0<C) :
    ∃ n : ℕ, 1≤n ∧
      C*secondOrderRefinement
        (normalizedHessianConditionNumber ((n:ℝ)^2) 1 ((n:ℝ)^6)) ((n:ℝ)^6) 1 <
      secondOrderNormalizedWork ((n:ℝ)^2) 1 ((n:ℝ)^6) 1 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (C+1)
  have ht : 0<(n:ℝ) := by linarith
  have hn1 : 1≤n := by exact_mod_cast (by linarith : (1:ℝ)≤(n:ℝ))
  refine ⟨n,hn1,?_⟩
  have hu := secondOrderRefinement_family_upper (n:ℝ) ht
  have hl := secondOrderNormalizedWork_stability_lower ((n:ℝ)^2) 1 ((n:ℝ)^6) 1 (sq_nonneg _)
  have hc := mul_le_mul_of_nonneg_left hu hC.le
  have hh := mul_lt_mul_of_pos_right (by linarith : 8*C<20*(n:ℝ)) (pow_pos ht 3)
  have he : 20*((n:ℝ)^2)^2=20*(n:ℝ)*(n:ℝ)^3 := by ring
  rw [he] at hl
  exact (hc.trans_lt (by nlinarith only [hh])).trans_le hl


/-- The additional regime needed by the printed simplification has an exact
physical-parameter interpretation; it is not an automatic curvature fact. -/
theorem sourceHessianConditionNumber_ge_iff (m M M2 p : ℝ) (hm : 0<m) :
    kineticConditionNumber m M≤sourceHessianConditionNumber m M M2 p ↔
      M*(1-p ^ (-1/3 : ℝ))≤M2 ^ (2/3 : ℝ) := by
  unfold kineticConditionNumber sourceHessianConditionNumber
  rw [div_le_div_iff_of_pos_right hm]
  constructor <;> intro h <;> nlinarith only [h]

/-- Under that explicit physical regime the source's proposed shape is a valid
upper bound for its tail-free prescription. -/
theorem secondOrderNormalizedWork_physical_regime (m M M2 p ε : ℝ)
    (hm : 0<m) (hmM : m≤M) (hM2 : 0≤M2) (hp : 1≤p) (hε : 0<ε)
    (hregime : M*(1-p ^ (-1/3 : ℝ))≤M2 ^ (2/3 : ℝ)) :
    secondOrderNormalizedWork (M/m) (M2/(m*Real.sqrt m)) p ε≤
      64*secondOrderRefinement (sourceHessianConditionNumber m M M2 p) p ε := by
  have hr := (sourceHessianConditionNumber_ge_iff m M M2 p hm).2 hregime
  simpa only [max_eq_right hr] using secondOrderNormalizedWork_physical_bound m M M2 p ε hm hmM hM2 hp hε

/-- The counterexample uses precisely the source's physical condition-number
definition, with m=M₂=1, M=n² and actual natural dimension n⁶. -/
theorem secondOrderSourceRefinement_no_uniform_constant (C : ℝ) (hC : 0<C) :
    ∃ n : ℕ, 1≤n ∧
      C*secondOrderRefinement
        (sourceHessianConditionNumber 1 ((n:ℝ)^2) 1 ((n:ℝ)^6)) ((n:ℝ)^6) 1 <
      secondOrderNormalizedWork ((n:ℝ)^2) 1 ((n:ℝ)^6) 1 := by
  obtain ⟨n,hn,hbad⟩ := secondOrderRefinement_no_uniform_constant C hC
  refine ⟨n,hn,?_⟩
  rw [sourceHessianConditionNumber_normalize 1 ((n:ℝ)^2) 1 ((n:ℝ)^6) (by norm_num) (by norm_num)]
  simpa only [Real.sqrt_one,one_mul,div_one] using hbad

end KineticLangevin
