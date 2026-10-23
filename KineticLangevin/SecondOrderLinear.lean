import KineticLangevin.PotentialContraction
import KineticLangevin.Coefficients

noncomputable section
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace NNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared transformed kinetic drift separates a damping multiple of its energy derivative. -/
theorem kinetic_drift_energy_identity (γ : ℝ) (v x F : E) :
    transformEnergy γ 0 (-γ • v-F,v)=
      -γ/2*forceEnergyDerivative γ v x F+2*‖F‖^2-γ^2*⟪x,F⟫ := by
  simp only [transformEnergy,transform,sub_zero,zero_smul,sub_zero,norm_neg,
    forceEnergyDerivative,norm_add_sq_real,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,inner_neg_left,inner_neg_right,
    real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,
    real_inner_comm F v,real_inner_comm F x,real_inner_comm x v]
  ring

/-- Exact Euler energy expansion for the genuine phase geometry. -/
theorem kinetic_euler_energy_identity (γ s : ℝ) (v x F : E) :
    transformEnergy γ 0 (v+s • (-γ • v-F),x+s • v)=
      transformEnergy γ 0 (v,x)+s*forceEnergyDerivative γ v x F+
        s^2*transformEnergy γ 0 (-γ • v-F,v) := by
  simp only [transformEnergy,transform,sub_zero,zero_smul,sub_zero,norm_neg,
    forceEnergyDerivative,norm_add_sq_real,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,
    inner_neg_left,inner_neg_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm F v,real_inner_comm F x,real_inner_comm x v,
    smul_add,smul_sub,smul_smul,smul_neg,neg_add_rev,inner_zero_left,inner_zero_right,norm_zero]
  ring

/-- Cocoercivity yields a remainder controlled by M, rather than by the potentially much larger γ². -/
theorem kinetic_drift_energy_bound (γ m M : ℝ) (hγ : 0<γ) (hm : 0≤m) (hmM : m≤M)
    (hfriction : m+M≤γ^2) (v x F : E)
    (hcoco : ‖F‖^2≤M*⟪x,F⟫) (hupper : ⟪x,F⟫≤M*‖x‖^2) :
    transformEnergy γ 0 (-γ • v-F,v)≤-γ/2*forceEnergyDerivative γ v x F+
      (2*M*(M-m)/γ^2)*transformEnergy γ 0 (v,x) := by
  have hM : 0≤M := hm.trans hmM
  have hpair : 0≤⟪x,F⟫ := by
    by_cases hzero : M=0
    · have hF : F=0 := by
        apply norm_eq_zero.mp
        simp only [hzero,zero_mul] at hcoco
        nlinarith [sq_nonneg ‖F‖,norm_nonneg F]
      simp [hF]
    · have hMpos : 0<M := lt_of_le_of_ne hM (Ne.symm hzero)
      nlinarith [sq_nonneg ‖F‖]
  have he := position_sq_le_energy γ 0 (v,x)
  simp only [mul_zero,sub_zero] at he
  have hγ2 : 0<γ^2 := sq_pos_of_pos hγ
  have hgap : 0≤M-m := sub_nonneg.mpr hmM
  have hrem : (2*M-γ^2)*⟪x,F⟫≤(2*M*(M-m)/γ^2)*transformEnergy γ 0 (v,x) := by
    calc
      _ ≤ (M-m)*⟪x,F⟫ := mul_le_mul_of_nonneg_right (by linarith only [hfriction]) hpair
      _ ≤ (M-m)*(M*‖x‖^2) := mul_le_mul_of_nonneg_left hupper hgap
      _ ≤ _ := by
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hγ2).mpr
        have hh := mul_le_mul_of_nonneg_left he (mul_nonneg hM hgap)
        convert hh using 1 <;> ring
  rw [kinetic_drift_energy_identity]
  calc
    _ = -γ/2*forceEnergyDerivative γ v x F+(2*‖F‖^2-γ^2*⟪x,F⟫) := by ring
    _ ≤ -γ/2*forceEnergyDerivative γ v x F+(2*(M*⟪x,F⟫)-γ^2*⟪x,F⟫) :=
      add_le_add le_rfl (sub_le_sub_right (mul_le_mul_of_nonneg_left hcoco (by norm_num : (0 : ℝ)≤2)) _)
    _ = -γ/2*forceEnergyDerivative γ v x F+(2*M-γ^2)*⟪x,F⟫ := by ring
    _ ≤ _ := add_le_add le_rfl hrem

/-- The Euler kinetic map contracts up to a second-order M-dependent correction. -/
theorem kinetic_euler_norm_bound (γ m M s : ℝ) (hγ : 0<γ) (hm : 0≤m) (hmM : m≤M)
    (hfriction : m+M≤γ^2) (hs : 0≤s) (hsmall : γ*s≤1)
    (v x F : E) (hdiss : forceEnergyDerivative γ v x F≤(-2*m/γ)*transformEnergy γ 0 (v,x))
    (hcoco : ‖F‖^2≤M*⟪x,F⟫) (hupper : ⟪x,F⟫≤M*‖x‖^2) :
    transformNorm γ 0 (v+s • (-γ • v-F),x+s • v)≤
      (1-m*s/γ+(m/2+M*(M-m)/γ^2)*s^2)*transformNorm γ 0 (v,x) := by
  let C : ℝ := m/2+M*(M-m)/γ^2
  have hM : 0≤M := hm.trans hmM
  have hgap : 0≤M-m := sub_nonneg.mpr hmM
  have hC : 0≤C := by dsimp [C];positivity
  have hms : m*s/γ≤1 := by
    apply (div_le_one hγ).mpr
    have hh : m≤γ^2 := by linarith only [hm.trans hmM,hfriction]
    nlinarith only [mul_le_mul_of_nonneg_right hh hs,mul_le_mul_of_nonneg_left hsmall hγ.le]
  have hq : 0≤1-m*s/γ+C*s^2 := add_nonneg (sub_nonneg.mpr hms) (mul_nonneg hC (sq_nonneg s))
  have hE : 0≤transformEnergy γ 0 (v,x) := transformEnergy_nonneg _ _ _
  have hA := kinetic_drift_energy_bound γ m M hγ hm hmM hfriction v x F hcoco hupper
  have hD := mul_le_mul_of_nonneg_left hdiss (show 0≤s*(1-γ*s/2) from mul_nonneg hs (by linarith))
  have he : transformEnergy γ 0 (v+s • (-γ • v-F),x+s • v)≤
      (1-2*m*s/γ+2*C*s^2)*transformEnergy γ 0 (v,x) := by
    rw [kinetic_euler_energy_identity]
    calc
      _ ≤ transformEnergy γ 0 (v,x)+s*forceEnergyDerivative γ v x F+
          s^2*(-γ/2*forceEnergyDerivative γ v x F+(2*M*(M-m)/γ^2)*transformEnergy γ 0 (v,x)) := by
        gcongr
      _ = transformEnergy γ 0 (v,x)+s*(1-γ*s/2)*forceEnergyDerivative γ v x F+
          s^2*(2*M*(M-m)/γ^2)*transformEnergy γ 0 (v,x) := by ring
      _ ≤ transformEnergy γ 0 (v,x)+s*(1-γ*s/2)*((-2*m/γ)*transformEnergy γ 0 (v,x))+
          s^2*(2*M*(M-m)/γ^2)*transformEnergy γ 0 (v,x) := by linarith only [hD]
      _ = _ := by dsimp [C];field_simp [hγ.ne'];ring
  have hsq : (1-2*m*s/γ+2*C*s^2)≤(1-m*s/γ+C*s^2)^2 := by
    have hid : (1-m*s/γ+C*s^2)^2-(1-2*m*s/γ+2*C*s^2)=(-m*s/γ+C*s^2)^2 := by ring
    linarith only [hid,sq_nonneg (-m*s/γ+C*s^2)]
  apply (sq_le_sq₀ (transformNorm_nonneg _ _ _) (mul_nonneg hq (transformNorm_nonneg _ _ _))).mp
  rw [mul_pow,transformNorm_sq,transformNorm_sq]
  exact he.trans (mul_le_mul_of_nonneg_right hsq hE)

/-- The frozen Hessian and position-force correction costs at most 3Mt²/2 in transformed norm. -/
theorem secondOrder_frozen_correction_bound (γ M t : ℝ) (hγ : 0<γ) (hM : 0≤M) (ht : 0≤t)
    (H : E →L[ℝ] E) (hH : ‖H‖≤M) (v x F : E) (hF : ‖F‖≤M*‖x‖) :
    transformNorm γ 0 (-phi γ 2 t • H v,-psi γ 2 t • F-phi γ 3 t • H v)≤
      (3/2 : ℝ)*M*t^2*transformNorm γ 0 (v,x) := by
  let N := transformNorm γ 0 (v,x)
  let B := M*t^2*N
  have hN : 0≤N := transformNorm_nonneg _ _ _
  have hB : 0≤B := by dsimp only [B];positivity
  have hv : ‖v‖≤N := velocity_le_transformNorm γ (v,x)
  have hx : γ*‖x‖≤(3/2 : ℝ)*N := by
    have hs := position_sq_le_energy γ 0 (v,x)
    simp only [mul_zero,sub_zero,← transformNorm_sq] at hs
    apply (sq_le_sq₀ (mul_nonneg hγ.le (norm_nonneg _)) (mul_nonneg (by norm_num : (0 : ℝ)≤3/2) hN)).mp
    nlinarith only [hs,sq_nonneg N]
  have hHv : ‖H v‖≤M*N := (H.le_opNorm v).trans
    ((mul_le_mul_of_nonneg_right hH (norm_nonneg v)).trans (mul_le_mul_of_nonneg_left hv hM))
  have hγF : ‖γ • F‖≤(3/2 : ℝ)*M*N := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hγ]
    have h1 := mul_le_mul_of_nonneg_left hF hγ.le
    have h2 := mul_le_mul_of_nonneg_left hx hM
    nlinarith only [h1,h2]
  have hsum : ‖H v+γ • F‖≤(5/2 : ℝ)*M*N := by
    exact (norm_add_le _ _).trans (by linarith only [hHv,hγF])
  have hpsi : 0≤psi γ 2 t := psi_nonneg γ 2 ht
  have hphi : 0≤phi γ 2 t := phi_nonneg γ 2 ht
  have hp := psi_two_le hγ.le ht
  have hφ := (phi_two_le_psi_two hγ.le ht).trans hp
  have hid : transform γ 0 (-phi γ 2 t • H v,-psi γ 2 t • F-phi γ 3 t • H v)=
      (-psi γ 2 t • (H v+γ • F),phi γ 2 t • H v) := by
    have hc := phi_two_add_friction_phi_three γ t
    ext <;> simp only [transform,sub_zero,zero_smul,sub_zero,smul_sub,smul_smul,smul_neg,smul_add,neg_neg]
    · rw [← hc]
      module
    · module
  have hfirst : ‖-psi γ 2 t • (H v+γ • F)‖≤(5/4 : ℝ)*B := by
    rw [norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg hpsi]
    have hh := mul_le_mul hp hsum (norm_nonneg _) (by positivity : (0 : ℝ)≤t^2/2)
    dsimp only [B]
    nlinarith only [hh]
  have hsecond : ‖phi γ 2 t • H v‖≤B/2 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hphi]
    have hh := mul_le_mul hφ hHv (norm_nonneg _) (by positivity : (0 : ℝ)≤t^2/2)
    dsimp only [B]
    nlinarith only [hh]
  apply transformNorm_le_of_energy_le γ 0 ((3/2 : ℝ)*M*t^2*N) _ (by positivity)
  rw [transformEnergy,hid]
  have h1 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤(5/4 : ℝ)*B)).mpr hfirst
  have h2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤B/2)).mpr hsecond
  have he : ‖-psi γ 2 t • (H v+γ • F)‖^2+‖phi γ 2 t • H v‖^2≤((3/2 : ℝ)*B)^2 := by
    nlinarith only [h1,h2,sq_nonneg B]
  simpa only [B,mul_assoc] using he

/-- The exact ψ₁ coefficient and source step size absorb the entire frozen second-order correction. -/
theorem secondOrder_linear_scalar_bound (γ m M t : ℝ) (hγ : 0<γ) (hm : 0≤m) (hmM : m≤M)
    (hfriction : m+M≤γ^2) (ht : 0≤t) (hstep : 5*γ*M*t≤m) :
    1-m*psi γ 1 t/γ+(m/2+M*(M-m)/γ^2)*(psi γ 1 t)^2+(3/2 : ℝ)*M*t^2≤
      1-m*t/(2*γ) := by
  have hM : 0≤M := hm.trans hmM
  have hgap : 0≤M-m := sub_nonneg.mpr hmM
  have hMγ : M≤γ^2 := by linarith only [hfriction,hm]
  have hdiv : M*(M-m)/γ^2≤M-m := by
    apply (div_le_iff₀ (sq_pos_of_pos hγ)).mpr
    convert mul_le_mul_of_nonneg_right hMγ hgap using 1 <;> ring
  let C : ℝ := m/2+M*(M-m)/γ^2
  have hC : 0≤C := by dsimp only [C];positivity
  have hCsum : m/2+C≤M := by
    calc
      _ = m+M*(M-m)/γ^2 := by dsimp only [C];ring
      _ ≤ m+(M-m) := add_le_add le_rfl hdiv
      _ = M := by ring
  have hpsi := psi_one_le hγ.le ht
  have hpsi0 : 0≤psi γ 1 t := psi_nonneg γ 1 ht
  have hlower : t-γ*t^2/2≤psi γ 1 t := by
    have hb := mul_le_mul_of_nonneg_left (psi_two_le hγ.le ht) hγ.le
    rw [friction_mul_psi_two] at hb
    linarith only [hb]
  have hlin : -m*psi γ 1 t/γ≤-m*t/γ+m*t^2/2 := by
    have hh := neg_le_neg (mul_le_mul_of_nonneg_left hlower (div_nonneg hm hγ.le))
    convert hh using 1 <;> field_simp [hγ.ne'] <;> ring
  have hquad := mul_le_mul_of_nonneg_left ((sq_le_sq₀ hpsi0 ht).mpr hpsi) hC
  have hcost := mul_le_mul_of_nonneg_right hCsum (sq_nonneg t)
  have hlast : (5/2 : ℝ)*M*t^2≤m*t/(2*γ) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ)<2) hγ)).mpr
    have hh := mul_le_mul_of_nonneg_right hstep ht
    nlinarith only [hh]
  calc
    _ ≤ 1-m*t/γ+(5/2 : ℝ)*M*t^2 := by
      change 1-m*psi γ 1 t/γ+C*(psi γ 1 t)^2+(3/2 : ℝ)*M*t^2≤_
      calc
        _ = 1+(-m*psi γ 1 t/γ)+C*(psi γ 1 t)^2+(3/2 : ℝ)*M*t^2 := by ring
        _ ≤ 1+(-m*t/γ+m*t^2/2)+C*t^2+(3/2 : ℝ)*M*t^2 := by gcongr
        _ = 1-m*t/γ+(m/2+C)*t^2+(3/2 : ℝ)*M*t^2 := by ring
        _ ≤ 1-m*t/γ+M*t^2+(3/2 : ℝ)*M*t^2 := add_le_add (add_le_add le_rfl hcost) le_rfl
        _ = _ := by ring
    _ ≤ _ := by
      have he : 1-m*t/γ+(m*t/(2*γ))=1-m*t/(2*γ) := by field_simp [hγ.ne'];ring
      exact (add_le_add le_rfl hlast).trans_eq he

/-- The frozen-Hessian part of the implemented second-order difference. -/
def frozenSecondOrderStep (γ t : ℝ) (H : E →L[ℝ] E) (v x F : E) : E×E :=
  (psi γ 0 t • v-psi γ 1 t • F-phi γ 2 t • H v,
   x+psi γ 1 t • v-psi γ 2 t • F-phi γ 3 t • H v)

/-- This is an actual Euler phase plus the genuine frozen-Hessian correction. -/
theorem frozenSecondOrderStep_decomposition (γ t : ℝ) (H : E →L[ℝ] E) (v x F : E) :
    frozenSecondOrderStep γ t H v x F=
      (v+psi γ 1 t • (-γ • v-F),x+psi γ 1 t • v)+
        (-phi γ 2 t • H v,-psi γ 2 t • F-phi γ 3 t • H v) := by
  have hpsi : psi γ 0 t=1-γ*psi γ 1 t := by linarith only [friction_mul_psi_one γ t]
  ext <;> simp only [frozenSecondOrderStep,Prod.fst_add,Prod.snd_add,hpsi,smul_sub,smul_add,
    smul_smul,sub_smul,one_smul] <;> module

/-- The actual frozen-linear part contracts with the paper's factor and step-size regime. -/
theorem frozenSecondOrderStep_contract (γ m M t : ℝ) (hγ : 0<γ) (hm : 0<m) (hmM : m≤M)
    (hfriction : m+M≤γ^2) (ht : 0≤t) (hstep : 5*γ*M*t≤m)
    (H : E →L[ℝ] E) (hH : ‖H‖≤M) (v x F : E)
    (hF : ‖F‖≤M*‖x‖)
    (hinterp : m*M*‖x‖^2+‖F‖^2≤(m+M)*⟪F,x⟫) :
    transformNorm γ 0 (frozenSecondOrderStep γ t H v x F)≤
      (1-m*t/(2*γ))*transformNorm γ 0 (v,x) := by
  have hM : 0<M := hm.trans_le hmM
  have hupper : ⟪x,F⟫≤M*‖x‖^2 := by
    calc
      _ ≤ ‖x‖*‖F‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖*(M*‖x‖) := mul_le_mul_of_nonneg_left hF (norm_nonneg _)
      _ = _ := by ring
  have hcoco : ‖F‖^2≤M*⟪x,F⟫ := by
    have hi := hinterp
    rw [real_inner_comm x F] at hi
    have hh := mul_le_mul_of_nonneg_left hupper hm.le
    nlinarith only [hi,hh]
  have hsmall : γ*t≤1 := by
    have h1 : (5*(γ*t))*m≤(5*(γ*t))*M :=
      mul_le_mul_of_nonneg_left hmM (mul_nonneg (by norm_num) (mul_nonneg hγ.le ht))
    have hh : m*(5*γ*t)≤m*1 := by nlinarith only [h1,hstep]
    have h5 := (mul_le_mul_iff_right₀ hm).mp (by simpa only [mul_comm] using hh)
    linarith only [h5]
  have hpsmall : γ*psi γ 1 t≤1 := (mul_le_mul_of_nonneg_left (psi_one_le hγ.le ht) hγ.le).trans hsmall
  have hdiss := force_dissipativity γ m M hγ hmM hfriction v x F (interpolation_sector m M x F hinterp)
  have hEuler := kinetic_euler_norm_bound γ m M (psi γ 1 t) hγ hm.le hmM hfriction
    (psi_nonneg γ 1 ht) hpsmall v x F hdiss hcoco hupper
  have hCorr := secondOrder_frozen_correction_bound γ M t hγ hM.le ht H hH v x F hF
  rw [frozenSecondOrderStep_decomposition]
  calc
    _ ≤ _ := transformNorm_add_le _ _ _ _
    _ ≤ (1-m*psi γ 1 t/γ+(m/2+M*(M-m)/γ^2)*(psi γ 1 t)^2)*transformNorm γ 0 (v,x)+
        (3/2 : ℝ)*M*t^2*transformNorm γ 0 (v,x) := add_le_add hEuler hCorr
    _ = (1-m*psi γ 1 t/γ+(m/2+M*(M-m)/γ^2)*(psi γ 1 t)^2+(3/2 : ℝ)*M*t^2)*transformNorm γ 0 (v,x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (secondOrder_linear_scalar_bound γ m M t hγ hm.le hmM hfriction ht hstep)
      (transformNorm_nonneg _ _ _)

end KineticLangevin
