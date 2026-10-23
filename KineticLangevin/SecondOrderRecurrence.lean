import KineticLangevin.Accuracy

noncomputable section
namespace KineticLangevin

/-- The actual second-order cutoff used to absorb the random-Hessian comparison into contraction. -/
def secondOrderCutoff (m M2 h : ℝ) : ℝ := (m/(4*M2*h))^2

/-- The source cutoff has the exact square root, absorption coefficient, and dimension lower bound. -/
theorem secondOrderCutoff_spec (m M2 h p : ℝ) (hm : 0<m) (hM2 : 0<M2)
    (hh : 0<h) (hp : 0≤p) (hdim : 4*Real.sqrt (5*p)*M2*h≤m) :
    0<secondOrderCutoff m M2 h ∧
    Real.sqrt (secondOrderCutoff m M2 h)=m/(4*M2*h) ∧
    M2*Real.sqrt (secondOrderCutoff m M2 h)*h=m/4 ∧
    5*p≤secondOrderCutoff m M2 h := by
  have hr : 0<m/(4*M2*h) := by positivity
  have hs : Real.sqrt (secondOrderCutoff m M2 h)=m/(4*M2*h) := Real.sqrt_sq hr.le
  refine ⟨sq_pos_of_pos hr,hs,?_,?_⟩
  · rw [hs]
    field_simp
  · have hb : Real.sqrt (5*p)≤m/(4*M2*h) :=
      (le_div_iff₀ (by positivity : 0<4*M2*h)).mpr (by nlinarith)
    have hx := (sq_le_sq₀ (Real.sqrt_nonneg _) hr.le).mpr hb
    simpa only [Real.sq_sqrt (by positivity : 0≤5*p),secondOrderCutoff] using hx

/-- The source dimension restriction gives both the printed and stronger inverse-step-square Gaussian tails. -/
theorem secondOrderCutoff_tail (m M2 h p : ℝ) (hm : 0<m) (hM2 : 0<M2)
    (hh : 0<h) (hp : 0≤p) (hdim : 4*Real.sqrt (5*p)*M2*h≤m) :
    Real.exp (-(secondOrderCutoff m M2 h-p)/8)≤Real.exp (-p/2) ∧
    Real.exp (-(secondOrderCutoff m M2 h-p)/8)≤Real.exp (-m^2/(160*M2^2*h^2)) := by
  have hs := (secondOrderCutoff_spec m M2 h p hm hM2 hh hp hdim).2.2.2
  refine ⟨Real.exp_le_exp.mpr (by linarith),Real.exp_le_exp.mpr ?_⟩
  have he : -m^2/(160*M2^2*h^2) = -(secondOrderCutoff m M2 h)/10 := by
    unfold secondOrderCutoff
    field_simp
    <;> ring
  rw [he]
  linarith

/-- Affine accumulation of the repaired actual KLMC2 local and comparison errors. -/
theorem secondOrder_coupling_recurrence_bound (e : ℕ→ℝ) (m γ h M2 α p B C : ℝ)
    (hm : 0<m) (hγ : 0<γ) (hh : 0<h) (hB : 0≤B) (hC : 0≤C)
    (hq : 0≤1-m*h/(4*γ)) (hcut : M2*Real.sqrt α*h≤m/4)
    (hnonneg : ∀ n,0≤e n)
    (hlocal : ∀ n,e (n+1)≤(1-m*h/(2*γ)+M2*Real.sqrt α*h^2/γ)*e n+
      Real.sqrt 2*h^2*B*Real.exp (-(α-p)/8)+h^3*C/4) (n : ℕ) :
    e n≤(1-m*h/(4*γ))^n*e 0+
      (4*γ/(m*h))*(Real.sqrt 2*h^2*B*Real.exp (-(α-p)/8)+h^3*C/4) := by
  let q := 1-m*h/(4*γ)
  let b := Real.sqrt 2*h^2*B*Real.exp (-(α-p)/8)+h^3*C/4
  have hcoef : 1-m*h/(2*γ)+M2*Real.sqrt α*h^2/γ≤q := by
    apply (mul_le_mul_iff_left₀ hγ).mp
    have he : (1-m*h/(2*γ)+M2*Real.sqrt α*h^2/γ)*γ=γ-m*h/2+(M2*Real.sqrt α*h)*h := by field_simp <;> ring
    have he' : q*γ=γ-m*h/4 := by dsimp [q];field_simp <;> ring
    rw [he,he']
    nlinarith [mul_le_mul_of_nonneg_right hcut hh.le]
  have hr : ∀ k,e (k+1)≤q*e k+b := by
    intro k
    have hc := mul_le_mul_of_nonneg_right hcoef (hnonneg k)
    dsimp only [b]
    linarith [hlocal k]
  have hb : 0≤b := by dsimp [b];positivity
  have hq1 : q<1 := sub_lt_self _ (div_pos (mul_pos hm hh) (by positivity))
  have he := ULA.affine_recurrence_bound e q b hq hq1 hb hr n
  have hfloor : b/(1-q)=(4*γ/(m*h))*b := by dsimp [q];field_simp <;> ring
  rwa [hfloor] at he

/-- Projection yields the exact second-order bias with the unsimplified Gaussian fourth-moment dimension. -/
theorem secondOrder_projected_bound (e d : ℕ→ℝ) (m γ h M2 α p B C : ℝ)
    (hm : 0<m) (hγ : 0<γ) (hh : 0<h) (hB : 0≤B) (hC : 0≤C)
    (hq : 0≤1-m*h/(4*γ)) (hcut : M2*Real.sqrt α*h≤m/4)
    (hnonneg : ∀ n,0≤e n)
    (hlocal : ∀ n,e (n+1)≤(1-m*h/(2*γ)+M2*Real.sqrt α*h^2/γ)*e n+
      Real.sqrt 2*h^2*B*Real.exp (-(α-p)/8)+h^3*C/4)
    (hproject : ∀ n,d n≤Real.sqrt 2/γ*e n) (hinitial : e 0≤γ*d 0) (n : ℕ) :
    d n≤Real.sqrt 2*(1-m*h/(4*γ))^n*d 0+
      Real.sqrt 2*h^2*C/m+8*B*h/m*Real.exp (-(α-p)/8) := by
  have he := secondOrder_coupling_recurrence_bound e m γ h M2 α p B C hm hγ hh hB hC hq hcut hnonneg hlocal n
  have hp := mul_le_mul_of_nonneg_left he (by positivity : 0≤Real.sqrt 2/γ)
  have hi := mul_le_mul_of_nonneg_left hinitial (mul_nonneg (by positivity : 0≤Real.sqrt 2/γ) (pow_nonneg hq n))
  have hfirst : Real.sqrt 2/γ*(1-m*h/(4*γ))^n*(γ*d 0)=Real.sqrt 2*(1-m*h/(4*γ))^n*d 0 := by field_simp
  have hfloor : Real.sqrt 2/γ*((4*γ/(m*h))*(Real.sqrt 2*h^2*B*Real.exp (-(α-p)/8)+h^3*C/4))=
      Real.sqrt 2*h^2*C/m+8*B*h/m*Real.exp (-(α-p)/8) := by
    field_simp
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
    ring
  calc
    d n≤Real.sqrt 2/γ*e n := hproject n
    _ ≤ Real.sqrt 2/γ*((1-m*h/(4*γ))^n*e 0+(4*γ/(m*h))*(Real.sqrt 2*h^2*B*Real.exp (-(α-p)/8)+h^3*C/4)) := hp
    _ ≤ Real.sqrt 2/γ*(1-m*h/(4*γ))^n*(γ*d 0)+Real.sqrt 2/γ*((4*γ/(m*h))*(Real.sqrt 2*h^2*B*Real.exp (-(α-p)/8)+h^3*C/4)) := by nlinarith
    _ = _ := by rw [hfirst,hfloor];ring

/-- The printed linear-in-dimension Hessian term is valid for p≥2; the exact moment is retained below that range. -/
theorem secondOrder_source_dimension_bound (p M M2 : ℝ) (hp : 2≤p) (hM : 0≤M) (hM2 : 0≤M2) :
    Real.sqrt 2*(M2*Real.sqrt (p^2+2*p)+M*Real.sqrt (M*p))≤
      2*M2*p+M*Real.sqrt (2*M*p) := by
  have hs : Real.sqrt 2*Real.sqrt (p^2+2*p)≤2*p := by
    have hsq := Real.sq_sqrt (by positivity : 0≤p^2+2*p)
    have hsq2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have he : (Real.sqrt 2*Real.sqrt (p^2+2*p))^2=2*(p^2+2*p) := by rw [mul_pow,hsq,hsq2]
    nlinarith [mul_nonneg (by linarith : 0≤p) (by linarith : 0≤p-2),Real.sqrt_nonneg 2,Real.sqrt_nonneg (p^2+2*p)]
  have he : Real.sqrt (2*M*p)=Real.sqrt 2*Real.sqrt (M*p) := by rw [mul_assoc,Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hs hM2]

end KineticLangevin
