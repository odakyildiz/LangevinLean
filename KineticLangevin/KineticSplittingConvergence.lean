import KineticLangevin.KineticSplitting

/-! # Concrete kinetic splitting converges to actual additive integral paths -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The splitting uses exact filtered increments of the supplied continuous
additive velocity input, at every actual grid interval. -/
def kineticSplitChain (g : E → E) (γ h : ℝ) (initial : E×E) (B : ℝ → E) : ℕ → E×E
  | 0 => initial
  | k+1 => kineticSplitStep g γ h (kineticSplitChain g γ h initial B k)
      (ouInputIncrement γ B ((k : ℝ)*h) h)

/-- A finite error estimate in terms of the actual drift and input moduli.
The following convergence theorem derives those moduli by compact continuity. -/
theorem kineticSplitChain_error_of_modulus (g : E → E) (M γ : ℝ≥0)
    (hg : LipschitzWith M g) (initial : E×E) (B : ℝ → E) (Y : ℝ → E×E)
    (hB0 : B 0=0) (hY : Continuous Y) (T h η R : ℝ)
    (hT : 0≤T) (hh : 0≤h) (hh1 : h≤1) (hη : 0≤η) (hR : 0≤R)
    (n : ℕ) (hpartition : (n : ℝ)*h=T)
    (heY : ∀ t ∈ Icc 0 T, Y t-initial =
      -(∫ s in 0..t, kineticNegativeDrift g γ 1 (Y s))+(B t,0))
    (hbound : ∀ t ∈ Icc 0 T, ‖Y t‖≤R)
    (hmodD : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t≤h →
      ‖kineticNegativeDrift g γ 1 (Y s)-kineticNegativeDrift g γ 1 (Y t)‖≤η)
    (hmodB : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, dist s t≤h → ‖B s-B t‖≤η) :
    ‖kineticSplitChain g γ h initial B n-Y T‖ ≤
      T*(h*(((M : ℝ)+1)*((M : ℝ)+2)+(γ : ℝ)^2/2+(γ : ℝ)*((M : ℝ)+1))*
        (R+‖g 0‖)+(1+(γ : ℝ))*η)*Real.exp (((M : ℝ)+1)^2*T) := by
  let d := kineticNegativeDrift g γ 1
  let C : ℝ := ((M : ℝ)+1)*((M : ℝ)+2)+(γ : ℝ)^2/2+(γ : ℝ)*((M : ℝ)+1)
  let ε : ℝ := h*C*(R+‖g 0‖)+(1+(γ : ℝ))*η
  have hC : 0≤C := by dsimp [C]; positivity
  have hε : 0≤ε := by dsimp [ε]; positivity
  have hd : LipschitzWith (γ+M+1) d := by
    simpa [d] using kineticNegativeDrift_lipschitz g M γ 1 hg
  let X := kineticSplitChain g γ h initial B
  let e : ℕ → ℝ := fun k ↦ ‖X k-Y ((k : ℝ)*h)‖
  have hY0 : Y 0=initial := by
    have he0 := heY 0 ⟨le_rfl,hT⟩
    simpa only [intervalIntegral.integral_same,neg_zero,hB0,Prod.mk_zero_zero,add_zero,
      sub_eq_zero] using he0
  have he0 : e 0=0 := by simp [e,X,kineticSplitChain,hY0]
  have hgrid (k : ℕ) (hk : k≤n) : (k : ℝ)*h ∈ Icc 0 T := by
    refine ⟨by positivity,?_⟩
    rw [← hpartition]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hh
  have hstep (k : ℕ) (hk : k<n) :
      e (k+1)≤(1+((M : ℝ)+1)^2*h)*e k+h*ε := by
    let a : ℝ := (k : ℝ)*h
    let N := ouInputIncrement γ B a h
    let S := kineticSplitStep g γ h (Y a) N
    let D := ULA.localDefect d (fun s ↦ Y (a+s)) h
    have ha : a ∈ Icc 0 T := hgrid k hk.le
    have hb : a+h ∈ Icc 0 T := by
      convert hgrid (k+1) (Nat.succ_le_of_lt hk) using 1
      dsimp [a]
      push_cast
      ring
    have hosc (s : ℝ) (hs : s∈Icc 0 h) : a+s ∈ Icc 0 T :=
      ⟨by linarith [ha.1,hs.1],by linarith [hb.2,hs.2]⟩
    have hdist (s : ℝ) (hs : s∈Icc 0 h) : dist (a+s) a≤h := by
      simpa only [Real.dist_eq,add_sub_cancel_left,abs_of_nonneg hs.1] using hs.2
    have hD : ‖D‖≤h*η := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := h) (C := η) (f := fun s ↦ d (Y (a+s))-d (Y a))
        (fun s hs ↦ ?_)
      · simpa only [D,ULA.localDefect,add_zero,sub_zero,abs_of_nonneg hh,mul_comm] using hi
      · rw [uIoc_of_le hh] at hs
        exact hmodD (a+s) (hosc s ⟨hs.1.le,hs.2⟩) a ha (hdist s ⟨hs.1.le,hs.2⟩)
    have hN : ‖N-(B (a+h)-B a)‖≤(γ : ℝ)*h*η :=
      ouInputIncrement_defect γ γ.coe_nonneg B a h η hh hη
        (fun s hs ↦ hmodB (a+s) (hosc s hs) a ha (hdist s hs))
    have hinc := ULA.langevin_integral_increment d (γ+M+1) hd initial
      (fun t ↦ (B t,0)) Y hY T heY a (a+h) ha hb
    have hinc' : Y (a+h)-Y a = -(∫ s in 0..h,d (Y (a+s)))+(B (a+h)-B a,0) := by
      have hi : (∫ s in a..a+h,d (Y s))=∫ s in 0..h,d (Y (a+s)) := by
        simpa only [add_zero] using (intervalIntegral.integral_comp_add_left
          (f := fun s ↦ d (Y s)) (a := 0) (b := h) a).symm
      rw [hi] at hinc
      simpa only [Prod.mk_sub_mk,sub_zero] using hinc
    have hid := ULA.localDefect_euler_identity d (fun s ↦ Y (a+s))
      (fun s ↦ (B (a+s)-B a,0)) h
      ((hd.continuous.comp (hY.comp (continuous_const.add continuous_id))).intervalIntegrable 0 h)
      (by simpa only [add_zero] using hinc')
    have heuler : Y a-h • d (Y a)+(N,0)-Y (a+h) =
        (N-(B (a+h)-B a),0)+D := by
      rw [hid]
      simp only [add_zero]
      dsimp [D]
      ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
        Prod.smul_fst,Prod.smul_snd] <;> module
    have hS : ‖S-Y (a+h)‖≤h*ε := by
      have hs := kineticSplitStep_euler_defect g M hg γ h γ.coe_nonneg hh hh1 (Y a) N
      have hsb := mul_le_mul_of_nonneg_left (add_le_add_right (hbound a ha) ‖g 0‖)
        (by positivity : 0≤h^2*C)
      calc
        _ ≤ ‖S-(Y a-h • d (Y a)+(N,0))‖+
          ‖Y a-h • d (Y a)+(N,0)-Y (a+h)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ h^2*C*(R+‖g 0‖)+((γ : ℝ)*h*η+h*η) := by
          apply add_le_add (hs.trans (by simpa only [C,add_comm] using hsb))
          rw [heuler]
          exact (norm_add_le _ _).trans
            (add_le_add (by simpa using hN) hD)
        _ = _ := by dsimp [ε]; ring
    have hstab := kineticSplitStep_norm_sub_le g M hg γ h γ.coe_nonneg hh hh1 (X k) (Y a) N
    have htime : (((k+1 : ℕ) : ℝ)*h)=a+h := by dsimp [a]; push_cast; ring
    change ‖X (k+1)-Y (((k+1 : ℕ) : ℝ)*h)‖≤_
    rw [htime]
    change ‖kineticSplitStep g γ h (X k) N-Y (a+h)‖≤_
    exact (norm_sub_le_norm_sub_add_norm_sub _ S _).trans (add_le_add hstab hS)
  have he := ULA.finite_euler_recurrence_bound e (1+((M : ℝ)+1)^2*h) (h*ε)
    (by nlinarith [mul_nonneg (sq_nonneg ((M : ℝ)+1)) hh]) (by positivity) he0 n hstep
  have hpow : (1+((M : ℝ)+1)^2*h)^n≤Real.exp (((M : ℝ)+1)^2*T) := by
    calc
      _ ≤ Real.exp (((M : ℝ)+1)^2*h)^n :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (((M : ℝ)+1)^2*h)]) n
      _ = Real.exp ((n : ℝ)*(((M : ℝ)+1)^2*h)) := (Real.exp_nat_mul _ _).symm
      _ = _ := by rw [← hpartition]; congr 1; ring
  calc
    _ = e n := by simp only [e,X,hpartition]
    _ ≤ (n : ℝ)*(h*ε)*(1+((M : ℝ)+1)^2*h)^n := he
    _ ≤ (n : ℝ)*(h*ε)*Real.exp (((M : ℝ)+1)^2*T) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by rw [← hpartition]; dsimp [ε,C]; ring

/-- Actual Verlet--OU splitting converges to every continuous solution of
the kinetic additive integral equation for the same continuous forcing. -/
theorem kineticSplitChain_tendsto (g : E → E) (M γ : ℝ≥0)
    (hg : LipschitzWith M g) (initial : E×E) (B : ℝ → E) (Y : ℝ → E×E)
    (hB : Continuous B) (hB0 : B 0=0) (hY : Continuous Y) (T : ℝ) (hT : 0≤T)
    (heY : ∀ t ∈ Icc 0 T, Y t-initial =
      -(∫ s in 0..t, kineticNegativeDrift g γ 1 (Y s))+(B t,0)) :
    Tendsto (fun n : ℕ ↦ kineticSplitChain g γ (T/((n+1 : ℕ) : ℝ)) initial B (n+1))
      atTop (𝓝 (Y T)) := by
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hY.continuousOn
  have hR0 : 0≤R := (norm_nonneg (Y 0)).trans (hR 0 ⟨le_rfl,hT⟩)
  let C : ℝ := ((M : ℝ)+1)*((M : ℝ)+2)+(γ : ℝ)^2/2+(γ : ℝ)*((M : ℝ)+1)
  let D : ℝ := T*(C*(R+‖g 0‖)+(1+(γ : ℝ)))*Real.exp (((M : ℝ)+1)^2*T)
  have hC : 0≤C := by dsimp [C]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hmesh : Tendsto (fun n : ℕ ↦ T/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat T)
  have hd := kineticNegativeDrift_lipschitz g M γ 1 hg
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε/(D+1)
  have hη : 0<η := div_pos hε (by positivity)
  have hscale : η*(D+1)=ε := div_mul_cancel₀ _ (by positivity)
  have hsmall : η*D<ε := by nlinarith
  have hucD : UniformContinuousOn (fun t ↦ kineticNegativeDrift g γ 1 (Y t)) (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hd.continuous.comp hY).continuousOn
  have hucB : UniformContinuousOn B (Icc 0 T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hB.continuousOn
  obtain ⟨δD,hδD,hoscD⟩ := Metric.uniformContinuousOn_iff_le.mp hucD η hη
  obtain ⟨δB,hδB,hoscB⟩ := Metric.uniformContinuousOn_iff_le.mp hucB η hη
  have hnear : ∀ᶠ n : ℕ in atTop, T/((n+1 : ℕ) : ℝ)≤1 ∧
      T/((n+1 : ℕ) : ℝ)≤η ∧ T/((n+1 : ℕ) : ℝ)≤δD ∧
      T/((n+1 : ℕ) : ℝ)≤δB := by
    filter_upwards [hmesh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),
      hmesh.eventually (eventually_lt_nhds hη),hmesh.eventually (eventually_lt_nhds hδD),
      hmesh.eventually (eventually_lt_nhds hδB)] with n h1 h2 h3 h4
    exact ⟨h1.le,h2.le,h3.le,h4.le⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hnear
  refine ⟨N,fun n hn ↦ ?_⟩
  let h := T/((n+1 : ℕ) : ℝ)
  have hh : 0≤h := div_nonneg hT (by positivity)
  have he := kineticSplitChain_error_of_modulus g M γ hg initial B Y hB0 hY T h η R
    hT hh (hN n hn).1 hη.le hR0 (n+1) (by dsimp [h]; field_simp) heY hR
    (by
      intro s hs t ht hst
      simpa only [dist_eq_norm] using (hoscD s hs t ht (hst.trans (hN n hn).2.2.1)))
    (by
      intro s hs t ht hst
      simpa only [dist_eq_norm] using (hoscB s hs t ht (hst.trans (hN n hn).2.2.2)))
  rw [dist_eq_norm]
  apply lt_of_le_of_lt he
  have hhη := (hN n hn).2.1
  have hb : h*C*(R+‖g 0‖)+(1+(γ : ℝ))*η ≤
      η*(C*(R+‖g 0‖)+(1+(γ : ℝ))) := by
    nlinarith [mul_le_mul_of_nonneg_right hhη (mul_nonneg hC (by positivity : 0≤R+‖g 0‖))]
  have hbound := mul_le_mul_of_nonneg_left hb (mul_nonneg hT (Real.exp_pos (((M : ℝ)+1)^2*T)).le)
  have hbound' : T*(h*C*(R+‖g 0‖)+(1+(γ : ℝ))*η)*Real.exp (((M : ℝ)+1)^2*T)≤η*D := by
    dsimp [D]
    nlinarith [hbound]
  exact hbound'.trans_lt hsmall

/-- In particular, splitting converges to the actual jointly continuous
kinetic solution map selected by the proved Picard construction. -/
theorem kineticSplitChain_tendsto_kineticFlow (g : E → E) (M γ : ℝ≥0)
    (hg : LipschitzWith M g) (T : ℝ) (hT : 0≤T) (initial : E×E)
    (B : VelocityForcing (E := E) T) :
    Tendsto (fun n : ℕ ↦ kineticSplitChain g γ (T/((n+1 : ℕ) : ℝ)) initial
      (normalizedForcing T hT B) (n+1)) atTop
      (𝓝 (kineticFlow g M γ 1 hg T hT initial B T)) := by
  have hs := kineticFlow_spec g M γ 1 hg T hT initial B
  exact kineticSplitChain_tendsto g M γ hg initial (normalizedForcing T hT B) _
    (continuous_normalizedForcing T hT B) (normalizedForcing_zero T hT B) hs.1 T hT hs.2.2

end KineticLangevin
