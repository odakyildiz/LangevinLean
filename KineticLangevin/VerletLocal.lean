import KineticLangevin.OBABORemainder
import KineticLangevin.OBABO
import KineticLangevin.LocalError

/-! # Actual local state error of the OBABO Hamiltonian step

These estimates compare velocity Verlet with genuine Hamiltonian integral
paths. They apply also in an L² Hilbert space, where C and G are moment norms.
The final theorem compares the implemented OBABO step to the exact O-H-O
reference under the same two thermostat noises.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory Set
open scoped NNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hamiltonian_velocity_increment_bound (g : E → E) (v x : ℝ → E) (T G : ℝ)
    (hbound : ∀ s ∈ Icc 0 T, ‖g (x s)‖ ≤ G)
    (heq : ∀ t ∈ Icc 0 T, v t - v 0 = -(∫ s in 0..t, g (x s)))
    (t : ℝ) (ht : t ∈ Icc 0 T) : ‖v t - v 0‖ ≤ G * t := by
  rw [heq t ht, norm_neg]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := G) (f := fun s ↦ g (x s)) (fun s hs ↦ ?_)
  · simpa only [sub_zero, abs_of_nonneg ht.1] using hb
  · rw [uIoc_of_le ht.1] at hs
    exact hbound s ⟨hs.1.le,hs.2.trans ht.2⟩

theorem hamiltonian_position_euler_defect (g : E → E) (v x : ℝ → E) (T G : ℝ)
    (hv : Continuous v)
    (hbound : ∀ s ∈ Icc 0 T, ‖g (x s)‖ ≤ G)
    (heq : ∀ t ∈ Icc 0 T, v t - v 0 = -(∫ s in 0..t, g (x s)))
    (hkin : ∀ t ∈ Icc 0 T, x t - x 0 = ∫ s in 0..t, v s)
    (t : ℝ) (ht : t ∈ Icc 0 T) : ‖x t - (x 0 + t • v 0)‖ ≤ G * t ^ 2 / 2 := by
  have hid : x t - (x 0 + t • v 0) = ∫ s in 0..t, v s - v 0 := by
    rw [intervalIntegral.integral_sub (hv.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero]
    rw [← hkin t ht]
    module
  rw [hid]
  calc
    _ ≤ ∫ s in 0..t, G * s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht.1
      · exact Filter.Eventually.of_forall (fun s hs ↦
          hamiltonian_velocity_increment_bound g v x T G hbound heq s ⟨hs.1.le,hs.2.trans ht.2⟩)
      · exact (by fun_prop : Continuous (fun s : ℝ ↦ G * s)).intervalIntegrable _ _
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id];ring

theorem verlet_local_component_bounds (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (v x : ℝ → E) (h C G : ℝ) (hh : 0 ≤ h) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hv : Continuous v) (hx : Continuous x)
    (hvelocity : ∀ s ∈ Icc 0 h, ‖v s‖ ≤ C)
    (hforce : ∀ s ∈ Icc 0 h, ‖g (x s)‖ ≤ G)
    (heq : ∀ t ∈ Icc 0 h, v t - v 0 = -(∫ s in 0..t, g (x s)))
    (hkin : ∀ t ∈ Icc 0 h, x t - x 0 = ∫ s in 0..t, v s) :
    ‖(verletStep g h (v 0,x 0)).2 - x h‖ ≤ G * h ^ 2 ∧
      ‖(verletStep g h (v 0,x 0)).1 - v h‖ ≤ (M : ℝ) * C * h ^ 2 + (M : ℝ) * G * h ^ 3 / 4 := by
  have h0 : (0 : ℝ) ∈ Icc 0 h := ⟨le_rfl, hh⟩
  have hhmem : h ∈ Icc 0 h := ⟨hh,le_rfl⟩
  have hV0 := hvelocity 0 h0
  have hF0 := hforce 0 h0
  let xe := x 0 + h • v 0
  let xn := x 0 + h • (v 0 - (h / 2) • g (x 0))
  have hxn : xn - xe = -(h ^ 2 / 2) • g (x 0) := by dsimp [xn, xe];module
  have hxne : ‖xn - xe‖ ≤ h ^ 2 / 2 * G := by
    rw [hxn, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / 2)]
    exact mul_le_mul_of_nonneg_left hF0 (by positivity)
  have hxe := hamiltonian_position_euler_defect g v x h G hv hforce heq hkin h hhmem
  have hxf : ‖xn - x 0‖ ≤ h * C + h ^ 2 / 2 * G := by
    have hid : xn - x 0 = h • v 0 - (h ^ 2 / 2) • g (x 0) := by dsimp [xn];module
    rw [hid]
    have ht := norm_sub_le (h • v 0) ((h ^ 2 / 2) • g (x 0))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / 2)] at ht
    have hVs := mul_le_mul_of_nonneg_left hV0 hh
    have hFs := mul_le_mul_of_nonneg_left hF0 (by positivity : 0 ≤ h ^ 2 / 2)
    nlinarith only [ht, hVs, hFs]
  have hvfrozen : v h - (v 0 - h • g (x 0)) = -velocityDefect g x 0 h := by
    unfold velocityDefect
    simp only [neg_zero, zero_mul, Real.exp_zero, one_smul]
    have hgc : Continuous (fun s : ℝ ↦ g (x s)) := hg.continuous.comp hx
    rw [intervalIntegral.integral_sub (f := fun s ↦ g (x s)) (g := fun _ ↦ g (x 0))
      (hgc.intervalIntegrable _ _) intervalIntegrable_const, intervalIntegral.integral_const, sub_zero]
    have he := heq h hhmem
    rw [sub_eq_iff_eq_add] at he
    rw [he]
    module
  have hvexact : ‖v h - (v 0 - h • g (x 0))‖ ≤ (M : ℝ) * C * h ^ 2 / 2 := by
    rw [hvfrozen, norm_neg]
    exact velocityDefect_bound g M hg x v 0 h C (le_refl _) hC hvelocity hkin hhmem
  have hvn : (verletStep g h (v 0, x 0)).1 - (v 0 - h • g (x 0)) =
      -(h / 2) • (g xn - g (x 0)) := by
    dsimp [verletStep, kickStep, driftStep, xn]
    module
  have hvne : ‖(verletStep g h (v 0, x 0)).1 - (v 0 - h • g (x 0))‖ ≤
      (h / 2) * ((M : ℝ) * (h * C + h ^ 2 / 2 * G)) := by
    rw [hvn, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ h / 2)]
    exact mul_le_mul_of_nonneg_left ((hg.norm_sub_le xn (x 0)).trans
      (mul_le_mul_of_nonneg_left hxf M.coe_nonneg)) (by positivity)
  constructor
  · change ‖xn - x h‖ ≤ _
    have ht := norm_sub_le_norm_sub_add_norm_sub xn xe (x h)
    rw [norm_sub_rev xe (x h)] at ht
    nlinarith only [ht, hxne, hxe]
  · have ht := norm_sub_le_norm_sub_add_norm_sub (verletStep g h (v 0,x 0)).1
      (v 0 - h • g (x 0)) (v h)
    rw [norm_sub_rev (v 0 - h • g (x 0)) (v h)] at ht
    nlinarith only [ht, hvexact, hvne]

theorem weightedPhaseNorm_le_components (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L)
    (hfriction : 4 * L ≤ γ ^ 2) (s : E × E) :
    weightedPhaseNorm (1 / L) (1 / γ) s ≤ 2 * (‖s.2‖ + ‖s.1‖ / Real.sqrt L) := by
  have hmetric := obabo_metric_condition γ L hγ hL hfriction
  have hab : (1 / γ) ^ 2 ≤ 1 / L := by nlinarith [sq_nonneg (1 / γ)]
  have hu := (weightedPhaseEnergy_equiv (1 / L) (1 / γ) (by positivity) hmetric s).2
  have hn := weightedPhaseNorm_sq (1 / L) (1 / γ) hab s
  have hsq : (‖s.1‖ / Real.sqrt L) ^ 2 = ‖s.1‖ ^ 2 / L := by
    rw [div_pow, Real.sq_sqrt hL.le]
  have hp : 0 ≤ ‖s.2‖ * (‖s.1‖ / Real.sqrt L) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  change weightedPhaseNorm (1 / L) (1 / γ) s ^ 2 ≤ _
  rw [hn]
  unfold weightedBaseEnergy at hu
  simp only [div_eq_mul_inv, one_mul] at hu hsq hp ⊢
  norm_num at hu
  nlinarith only [hu, hsq, hp, sq_nonneg ‖s.2‖, sq_nonneg (‖s.1‖ / Real.sqrt L)]

theorem verlet_local_weighted_bound (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (v x : ℝ → E) (γ h C G : ℝ) (hγ : 0 < γ) (hM : 0 < (M : ℝ))
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hh : 0 ≤ h) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hv : Continuous v) (hx : Continuous x)
    (hvelocity : ∀ s ∈ Icc 0 h, ‖v s‖ ≤ C)
    (hforce : ∀ s ∈ Icc 0 h, ‖g (x s)‖ ≤ G)
    (heq : ∀ t ∈ Icc 0 h, v t - v 0 = -(∫ s in 0..t, g (x s)))
    (hkin : ∀ t ∈ Icc 0 h, x t - x 0 = ∫ s in 0..t, v s) :
    weightedPhaseNorm (1 / (M : ℝ)) (1 / γ) (verletStep g h (v 0,x 0) - (v h,x h)) ≤
      2 * h ^ 2 * (G + Real.sqrt (M : ℝ) * C + Real.sqrt (M : ℝ) * G * h / 4) := by
  have he := verlet_local_component_bounds g M hg v x h C G hh hC hG hv hx hvelocity hforce heq hkin
  have hroot : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hM
  have hratio : (M : ℝ) / Real.sqrt (M : ℝ) = Real.sqrt (M : ℝ) := by
    apply (div_eq_iff hroot.ne').mpr
    nlinarith only [Real.sq_sqrt M.coe_nonneg]
  calc
    _ ≤ 2 * (‖(verletStep g h (v 0,x 0)).2 - x h‖ +
        ‖(verletStep g h (v 0,x 0)).1 - v h‖ / Real.sqrt (M : ℝ)) :=
      weightedPhaseNorm_le_components γ M hγ hM hfriction _
    _ ≤ 2 * (G * h ^ 2 + ((M : ℝ) * C * h ^ 2 + (M : ℝ) * G * h ^ 3 / 4) / Real.sqrt (M : ℝ)) := by
      gcongr
      · exact he.1
      · exact he.2
    _ = 2 * h ^ 2 * (G + ((M : ℝ) / Real.sqrt (M : ℝ)) * C +
        ((M : ℝ) / Real.sqrt (M : ℝ)) * G * h / 4) := by ring
    _ = _ := by rw [hratio]

theorem obabo_hamiltonian_local_bound (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (v x : ℝ → E) (γ h δ σ C G : ℝ) (hγ : 0 < γ) (hM : 0 < (M : ℝ))
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hh : 0 ≤ h) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hδ : |δ| ≤ 1) (hv : Continuous v) (hx : Continuous x)
    (hvelocity : ∀ s ∈ Icc 0 h, ‖v s‖ ≤ C)
    (hforce : ∀ s ∈ Icc 0 h, ‖g (x s)‖ ≤ G)
    (heq : ∀ t ∈ Icc 0 h, v t - v 0 = -(∫ s in 0..t, g (x s)))
    (hkin : ∀ t ∈ Icc 0 h, x t - x 0 = ∫ s in 0..t, v s)
    (z : E × E) (ξ ξ' : E) (hinit : (v 0,x 0) = ornsteinStep δ σ ξ z) :
    weightedPhaseNorm (1 / (M : ℝ)) (1 / γ)
      (obaboStep g h δ σ z ξ ξ' - ornsteinStep δ σ ξ' (v h,x h)) ≤
      2 * h ^ 2 * (G + Real.sqrt (M : ℝ) * C + Real.sqrt (M : ℝ) * G * h / 4) := by
  have hc := verlet_local_component_bounds g M hg v x h C G hh hC hG hv hx hvelocity hforce heq hkin
  have hid : obaboStep g h δ σ z ξ ξ' = ornsteinStep δ σ ξ' (verletStep g h (v 0,x 0)) := by
    rw [hinit]
    rfl
  have hp : ‖(obaboStep g h δ σ z ξ ξ' - ornsteinStep δ σ ξ' (v h,x h)).2‖ ≤ G * h ^ 2 := by
    rw [hid]
    exact hc.1
  have hvbound : ‖(obaboStep g h δ σ z ξ ξ' - ornsteinStep δ σ ξ' (v h,x h)).1‖ ≤
      (M : ℝ) * C * h ^ 2 + (M : ℝ) * G * h ^ 3 / 4 := by
    rw [hid]
    have he : (ornsteinStep δ σ ξ' (verletStep g h (v 0,x 0)) - ornsteinStep δ σ ξ' (v h,x h)).1 =
        δ • ((verletStep g h (v 0,x 0)).1 - v h) := by simp only [ornsteinStep, Prod.fst_sub];module
    rw [he,norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right hδ (norm_nonneg _)).trans (by simpa only [one_mul] using hc.2)
  have hroot : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.2 hM
  have hratio : (M : ℝ) / Real.sqrt (M : ℝ) = Real.sqrt (M : ℝ) := by
    apply (div_eq_iff hroot.ne').mpr
    nlinarith only [Real.sq_sqrt M.coe_nonneg]
  calc
    _ ≤ 2 * (‖(obaboStep g h δ σ z ξ ξ' - ornsteinStep δ σ ξ' (v h,x h)).2‖ +
        ‖(obaboStep g h δ σ z ξ ξ' - ornsteinStep δ σ ξ' (v h,x h)).1‖ / Real.sqrt (M : ℝ)) :=
      weightedPhaseNorm_le_components γ M hγ hM hfriction _
    _ ≤ 2 * (G * h ^ 2 + ((M : ℝ) * C * h ^ 2 + (M : ℝ) * G * h ^ 3 / 4) / Real.sqrt (M : ℝ)) := by
      gcongr
    _ = 2 * h ^ 2 * (G + ((M : ℝ) / Real.sqrt (M : ℝ)) * C +
        ((M : ℝ) / Real.sqrt (M : ℝ)) * G * h / 4) := by ring
    _ = _ := by rw [hratio]

end KineticLangevin
