import KineticLangevin.Hamiltonian
import UnadjustedLangevin.EulerLimit

/-! # Consistency and convergence of velocity Verlet

The force is only required to be globally Lipschitz. The finite-horizon
convergence proof compares the actual Verlet iterates with explicit Euler;
the latter already converges to the selected Picard integral flow.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

namespace KineticLangevin

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem kickStep_norm_sub_le (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (h : ℝ) (hh : 0 ≤ h) (z w : E × E) :
    ‖kickStep g h z - kickStep g h w‖ ≤ (1 + (M : ℝ) * h) * ‖z - w‖ := by
  have hv : ‖z.1-w.1‖ ≤ ‖z-w‖ := by simpa using norm_fst_le (z-w)
  have hx : ‖z.2-w.2‖ ≤ ‖z-w‖ := by simpa using norm_snd_le (z-w)
  have hf := hg.norm_sub_le z.2 w.2
  have hq : ‖z-w‖ ≤ (1+(M:ℝ)*h)*‖z-w‖ := by
    nlinarith [mul_nonneg M.coe_nonneg hh, norm_nonneg (z-w)]
  change max ‖(z.1-h • g z.2)-(w.1-h • g w.2)‖ ‖z.2-w.2‖ ≤ _
  apply max_le
  · have he : (z.1-h • g z.2)-(w.1-h • g w.2) =
        (z.1-w.1)-h • (g z.2-g w.2) := by module
    rw [he]
    have hn := norm_sub_le (z.1-w.1) (h • (g z.2-g w.2))
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh] at hn
    have hfh := mul_le_mul_of_nonneg_left hf hh
    have hxh := mul_le_mul_of_nonneg_left hx (mul_nonneg hh M.coe_nonneg)
    nlinarith
  · exact hx.trans hq

theorem driftStep_norm_sub_le (h : ℝ) (hh : 0 ≤ h) (z w : E × E) :
    ‖driftStep h z-driftStep h w‖ ≤ (1+h)*‖z-w‖ := by
  have hv : ‖z.1-w.1‖ ≤ ‖z-w‖ := by simpa using norm_fst_le (z-w)
  have hx : ‖z.2-w.2‖ ≤ ‖z-w‖ := by simpa using norm_snd_le (z-w)
  have hq : ‖z-w‖ ≤ (1+h)*‖z-w‖ := by nlinarith [norm_nonneg (z-w)]
  change max ‖z.1-w.1‖ ‖(z.2+h • z.1)-(w.2+h • w.1)‖ ≤ _
  apply max_le (hv.trans hq)
  have he : (z.2+h • z.1)-(w.2+h • w.1) = (z.2-w.2)+h • (z.1-w.1) := by module
  rw [he]
  have hn := norm_add_le (z.2-w.2) (h • (z.1-w.1))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh] at hn
  nlinarith [mul_le_mul_of_nonneg_left hv hh]

/-- A horizon-independent first-order stability bound for the symmetric map. -/
theorem verletStep_norm_sub_le (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (z w : E × E) :
    ‖verletStep g h z-verletStep g h w‖ ≤
      (1+((M:ℝ)+1)^2*h)*‖z-w‖ := by
  have hk := kickStep_norm_sub_le g M hg (h/2) (by positivity)
    (driftStep h (kickStep g (h/2) z)) (driftStep h (kickStep g (h/2) w))
  have ha := driftStep_norm_sub_le h hh (kickStep g (h/2) z) (kickStep g (h/2) w)
  have hb := kickStep_norm_sub_le g M hg (h/2) (by positivity) z w
  have hprod : ‖verletStep g h z-verletStep g h w‖ ≤
      (1+(M:ℝ)*(h/2)) * (1+h) * (1+(M:ℝ)*(h/2)) * ‖z-w‖ := by
    calc
      _ ≤ (1+(M:ℝ)*(h/2)) *
          ‖driftStep h (kickStep g (h/2) z)-driftStep h (kickStep g (h/2) w)‖ := hk
      _ ≤ (1+(M:ℝ)*(h/2)) * ((1+h)*((1+(M:ℝ)*(h/2))*‖z-w‖)) :=
        mul_le_mul_of_nonneg_left (ha.trans
          (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 1+h)))
          (by positivity : 0 ≤ 1+(M:ℝ)*(h/2))
      _ = _ := by ring
  have hp : (1+(M:ℝ)*(h/2)) * (1+h) * (1+(M:ℝ)*(h/2)) ≤
      1+((M:ℝ)+1)^2*h := by
    have h2 : h^2 ≤ h := by nlinarith
    have h3 : h^3 ≤ h := by nlinarith [mul_nonneg hh (sub_nonneg.mpr hh1)]
    nlinarith [mul_le_mul_of_nonneg_left h2 M.coe_nonneg,
      mul_le_mul_of_nonneg_left h2 (sq_nonneg (M:ℝ)),
      mul_le_mul_of_nonneg_left h3 (sq_nonneg (M:ℝ))]
  exact hprod.trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))

/-- Verlet differs from one explicit Hamiltonian Euler step by a genuine
quadratic local state defect, under only a Lipschitz force assumption. -/
theorem verletStep_euler_defect (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (h : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (z : E × E) :
    ‖verletStep g h z - (z - h • kineticNegativeDrift g 0 1 z)‖ ≤
      h ^ 2 * ((M : ℝ)+1) * ((M : ℝ)+2) * (‖z‖+‖g 0‖) := by
  let R : ℝ := ‖z‖+‖g 0‖
  let vhalf : E := z.1-(h/2) • g z.2
  let xnext : E := z.2+h • vhalf
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hgx : ‖g z.2‖ ≤ ((M : ℝ)+1)*R := by
    have he : g z.2 = (g z.2-g 0)+g 0 := by abel
    rw [he]
    calc
      _ ≤ ‖g z.2-g 0‖+‖g 0‖ := norm_add_le _ _
      _ ≤ (M : ℝ)*‖z.2‖+‖g 0‖ := by simpa using add_le_add_right (hg.norm_sub_le z.2 0) ‖g 0‖
      _ ≤ (M : ℝ)*‖z‖+‖g 0‖ := by
        nlinarith [mul_le_mul_of_nonneg_left (norm_snd_le z) M.coe_nonneg]
      _ ≤ _ := by dsimp [R]; nlinarith [norm_nonneg z, norm_nonneg (g 0), mul_nonneg M.coe_nonneg (norm_nonneg (g 0))]
  have hvhalf : ‖vhalf‖ ≤ ((M : ℝ)+2)*R := by
    have hn := norm_sub_le z.1 ((h/2) • g z.2)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ h/2)] at hn
    have hhg : (h/2)*‖g z.2‖ ≤ ‖g z.2‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    have hzv : ‖z.1‖ ≤ R := (norm_fst_le z).trans (by dsimp [R]; linarith [norm_nonneg (g 0)])
    change ‖z.1-(h/2) • g z.2‖ ≤ _
    nlinarith
  have hgdiff : ‖g xnext-g z.2‖ ≤ (M : ℝ)*(h*(((M : ℝ)+2)*R)) := by
    have he : xnext-z.2 = h • vhalf := by dsimp [xnext]; abel
    have hn := hg.norm_sub_le xnext z.2
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh] at hn
    exact hn.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hvhalf hh) M.coe_nonneg)
  have hvel : (vhalf-(h/2) • g xnext)-(z.1-h • g z.2) =
      -(h/2) • (g xnext-g z.2) := by dsimp [vhalf]; module
  have hpos : xnext-(z.2+h • z.1) = -(h^2/2) • g z.2 := by
    dsimp [xnext, vhalf]
    module
  have heuler : z-h • kineticNegativeDrift g 0 1 z =
      (z.1-h • g z.2,z.2+h • z.1) := by
    ext <;> simp [kineticNegativeDrift]
  rw [heuler]
  change max ‖(vhalf-(h/2) • g xnext)-(z.1-h • g z.2)‖ ‖xnext-(z.2+h • z.1)‖ ≤ _
  apply max_le
  · rw [hvel, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ h/2)]
    calc
      _ ≤ (h/2)*((M : ℝ)*(h*(((M : ℝ)+2)*R))) := mul_le_mul_of_nonneg_left hgdiff (by positivity)
      _ = ((M : ℝ)/2)*(h^2*((M : ℝ)+2)*R) := by ring
      _ ≤ ((M : ℝ)+1)*(h^2*((M : ℝ)+2)*R) :=
        mul_le_mul_of_nonneg_right (by linarith [M.coe_nonneg]) (by positivity)
      _ = _ := by ring
  · rw [hpos, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity : 0 ≤ h^2/2)]
    calc
      _ ≤ (h^2/2)*(((M : ℝ)+1)*R) := mul_le_mul_of_nonneg_left hgx (by positivity)
      _ = (1/2 : ℝ)*(h^2*((M : ℝ)+1)*R) := by ring
      _ ≤ ((M : ℝ)+2)*(h^2*((M : ℝ)+1)*R) :=
        mul_le_mul_of_nonneg_right (by linarith [M.coe_nonneg]) (by positivity)
      _ = _ := by ring


/-- Uniform finite-horizon growth of the comparison Euler chain. -/
theorem eulerChain_norm_le (d : E → E) (L : ℝ≥0) (hd : LipschitzWith L d)
    (h T : ℝ) (hh : 0 ≤ h) (x : E) (n : ℕ) (hpartition : (n : ℝ)*h=T)
    (k : ℕ) (hk : k ≤ n) :
    ‖ULA.additiveEulerChain d h x (fun _ => 0) k‖ ≤
      ‖x‖+T*‖d x‖*Real.exp ((L : ℝ)*T) := by
  let X := ULA.additiveEulerChain d h x (fun _ => 0)
  let e : ℕ → ℝ := fun k => ‖X k-x‖
  have he0 : e 0 = 0 := by simp [e,X]
  have hnext (j : ℕ) : X (j+1) = X j-h • d (X j) := by
    simp [X,ULA.additiveEulerChain_succ]
  have hstep (j : ℕ) (_hj : j < k) :
      e (j+1) ≤ (1+(L : ℝ)*h)*e j+h*‖d x‖ := by
    have he : X (j+1)-x = ((X j-h • d (X j))-(x-h • d x))-h • d x := by
      rw [hnext]
      module
    change ‖X (j+1)-x‖ ≤ _
    rw [he]
    have hn := norm_sub_le ((X j-h • d (X j))-(x-h • d x)) (h • d x)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hh] at hn
    exact hn.trans (add_le_add (ULA.explicitEuler_norm_sub_le d L hd h hh (X j) x) le_rfl)
  have heb := ULA.finite_euler_recurrence_bound e (1+(L : ℝ)*h) (h*‖d x‖)
    (by linarith [mul_nonneg L.coe_nonneg hh]) (by positivity) he0 k hstep
  have hkh : (k : ℝ)*h ≤ T := by
    rw [← hpartition]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hh
  have hpow : (1+(L : ℝ)*h)^k ≤ Real.exp ((L : ℝ)*T) := by
    calc
      _ ≤ Real.exp ((L : ℝ)*h)^k := pow_le_pow_left₀ (by positivity)
        (by linarith [Real.add_one_le_exp ((L : ℝ)*h)]) k
      _ = Real.exp ((k : ℝ)*((L : ℝ)*h)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hkh L.coe_nonneg])
  have hnorm : ‖X k‖ ≤ e k+‖x‖ := by
    have he : X k = (X k-x)+x := by abel
    calc
      ‖X k‖ = ‖(X k-x)+x‖ := congrArg norm he
      _ ≤ _ := norm_add_le _ _
  have hbound : e k ≤ T*‖d x‖*Real.exp ((L : ℝ)*T) := by
    calc
      _ ≤ (k : ℝ)*(h*‖d x‖)*(1+(L : ℝ)*h)^k := heb
      _ ≤ (k : ℝ)*(h*‖d x‖)*Real.exp ((L : ℝ)*T) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = ((k : ℝ)*h)*‖d x‖*Real.exp ((L : ℝ)*T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hkh (norm_nonneg _)) (Real.exp_nonneg _)
  exact hnorm.trans (by linarith)


/-- Explicit global comparison of Verlet with Euler over a fixed horizon. -/
theorem verlet_iterate_euler_error_le (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (h T : ℝ) (hh : 0 ≤ h) (hh1 : h ≤ 1) (hT : 0 ≤ T)
    (x : E × E) (n : ℕ) (hpartition : (n : ℝ)*h=T) :
    ‖(verletStep g h)^[n] x -
      ULA.additiveEulerChain (kineticNegativeDrift g 0 1) h x (fun _ => 0) n‖ ≤
      T*h*((M : ℝ)+1)*((M : ℝ)+2)*
        (‖x‖+T*‖kineticNegativeDrift g 0 1 x‖*Real.exp (((M : ℝ)+1)*T)+‖g 0‖)*
        Real.exp (((M : ℝ)+1)^2*T) := by
  let d := kineticNegativeDrift g 0 1
  let X := ULA.additiveEulerChain d h x (fun _ => 0)
  let V : ℕ → E × E := fun k => (verletStep g h)^[k] x
  let e : ℕ → ℝ := fun k => ‖V k-X k‖
  let C : ℝ := ((M : ℝ)+1)*((M : ℝ)+2)*
    (‖x‖+T*‖d x‖*Real.exp (((M : ℝ)+1)*T)+‖g 0‖)
  let A : ℝ := ((M : ℝ)+1)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := sq_nonneg _
  have hd : LipschitzWith (M+1) d := by
    simpa [d] using kineticNegativeDrift_lipschitz g M 0 1 hg
  have hlocal (k : ℕ) (hk : k < n) :
      ‖verletStep g h (X k)-(X k-h • d (X k))‖ ≤ h^2*C := by
    have hbound := eulerChain_norm_le d (M+1) hd h T hh x n hpartition k hk.le
    have hdef := verletStep_euler_defect g M hg h hh hh1 (X k)
    have hcoef : 0 ≤ h^2*((M : ℝ)+1)*((M : ℝ)+2) := by positivity
    calc
      _ ≤ h^2*((M : ℝ)+1)*((M : ℝ)+2)*(‖X k‖+‖g 0‖) := hdef
      _ ≤ h^2*((M : ℝ)+1)*((M : ℝ)+2)*
          (‖x‖+T*‖d x‖*Real.exp (((M : ℝ)+1)*T)+‖g 0‖) :=
        mul_le_mul_of_nonneg_left (by simpa [X] using add_le_add_right hbound ‖g 0‖) hcoef
      _ = _ := by dsimp [C]; ring
  have he0 : e 0 = 0 := by simp [e,V,X]
  have hstep (k : ℕ) (hk : k < n) : e (k+1) ≤ (1+A*h)*e k+h^2*C := by
    have hV : V (k+1) = verletStep g h (V k) := by simp [V,Function.iterate_succ_apply']
    have hX : X (k+1) = X k-h • d (X k) := by simp [X,ULA.additiveEulerChain_succ]
    have he : V (k+1)-X (k+1) =
        (verletStep g h (V k)-verletStep g h (X k))+
          (verletStep g h (X k)-(X k-h • d (X k))) := by rw [hV,hX]; abel
    change ‖V (k+1)-X (k+1)‖ ≤ _
    rw [he]
    exact (norm_add_le _ _).trans
      (add_le_add (verletStep_norm_sub_le g M hg h hh hh1 (V k) (X k)) (hlocal k hk))
  have he := ULA.finite_euler_recurrence_bound e (1+A*h) (h^2*C)
    (by nlinarith [mul_nonneg hA hh]) (by positivity) he0 n hstep
  have hpow : (1+A*h)^n ≤ Real.exp (A*T) := by
    calc
      _ ≤ Real.exp (A*h)^n := pow_le_pow_left₀ (by positivity)
        (by linarith [Real.add_one_le_exp (A*h)]) n
      _ = Real.exp ((n : ℝ)*(A*h)) := (Real.exp_nat_mul _ _).symm
      _ = _ := by rw [← hpartition]; congr 1; ring
  change e n ≤ _
  calc
    _ ≤ (n : ℝ)*(h^2*C)*(1+A*h)^n := he
    _ ≤ (n : ℝ)*(h^2*C)*Real.exp (A*T) := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = T*h*C*Real.exp (A*T) := by rw [← hpartition]; ring
    _ = _ := by dsimp [C,A,d]; ring


/-- The difference between the actual Verlet and Euler endpoints tends to zero. -/
theorem verlet_iterate_sub_euler_tendsto (g : E → E) (M : ℝ≥0)
    (hg : LipschitzWith M g) (T : ℝ) (hT : 0 ≤ T) (x : E × E) :
    Tendsto (fun n : ℕ => (verletStep g (T/((n+1 : ℕ) : ℝ)))^[n+1] x -
      ULA.additiveEulerChain (kineticNegativeDrift g 0 1)
        (T/((n+1 : ℕ) : ℝ)) x (fun _ => 0) (n+1)) atTop (𝓝 0) := by
  let C : ℝ := T*((M : ℝ)+1)*((M : ℝ)+2)*
    (‖x‖+T*‖kineticNegativeDrift g 0 1 x‖*Real.exp (((M : ℝ)+1)*T)+‖g 0‖)*
    Real.exp (((M : ℝ)+1)^2*T)
  have hmesh : Tendsto (fun n : ℕ => T/((n+1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat T)
  have hsmall : ∀ᶠ n : ℕ in atTop, T/((n+1 : ℕ) : ℝ) ≤ 1 :=
    (hmesh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))).mono (fun _ hn => hn.le)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hdom : ∀ᶠ n : ℕ in atTop,
      ‖(verletStep g (T/((n+1 : ℕ) : ℝ)))^[n+1] x -
        ULA.additiveEulerChain (kineticNegativeDrift g 0 1)
          (T/((n+1 : ℕ) : ℝ)) x (fun _ => 0) (n+1)‖ ≤ (T/((n+1 : ℕ) : ℝ))*C := by
    filter_upwards [hsmall] with n hn
    have he := verlet_iterate_euler_error_le g M hg (T/((n+1 : ℕ) : ℝ)) T
      (by positivity) hn hT x (n+1) (by field_simp)
    convert he using 1 <;> dsimp [C] <;> ring
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hdom
    (by simpa only [zero_mul] using hmesh.mul_const C)

/-- Velocity Verlet converges to every actual Hamiltonian integral solution. -/
theorem verlet_iterate_tendsto_integral [CompleteSpace E]
    (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (T : ℝ) (hT : 0 ≤ T) (x : E × E) (Y : ℝ → E × E) (hY : Continuous Y)
    (heY : ∀ t ∈ Icc 0 T, Y t-x = -(∫ s in 0..t, kineticNegativeDrift g 0 1 (Y s))) :
    Tendsto (fun n : ℕ => (verletStep g (T/((n+1 : ℕ) : ℝ)))^[n+1] x)
      atTop (𝓝 (Y T)) := by
  have hd : LipschitzWith (M+1) (kineticNegativeDrift g 0 1) := by
    simpa using kineticNegativeDrift_lipschitz g M 0 1 hg
  have hEuler := ULA.additiveEulerChain_tendsto (kineticNegativeDrift g 0 1)
    (M+1) hd x (fun _ => 0) Y rfl hY T hT
    (fun t ht => by simpa only [add_zero] using heY t ht)
  have hVerlet := verlet_iterate_sub_euler_tendsto g M hg T hT x
  have hsum := hVerlet.add hEuler
  convert hsum using 1
  · funext n
    abel
  · simp

end Normed

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The numerical limit is the selected Picard Hamiltonian flow, from only a
globally Lipschitz gradient; no Hessian or numerical-limit premise is added. -/
theorem verlet_iterate_tendsto_hamiltonianFlow
    (f : E → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (T : ℝ) (hT : 0 ≤ T) (initial : E × E) :
    Tendsto (fun n : ℕ => (verletStep (gradient f) (T/((n+1 : ℕ) : ℝ)))^[n+1] initial)
      atTop (𝓝 (hamiltonianFlow f M hLip T hT initial T)) := by
  have hs := kineticFlow_spec (gradient f) M 0 1 hLip T hT initial 0
  apply verlet_iterate_tendsto_integral (gradient f) M hLip T hT initial
    (hamiltonianFlow f M hLip T hT initial) hs.1
  intro t ht
  have he := hs.2.2 t ht
  simpa [hamiltonianFlow, normalizedForcing, Prod.mk_zero_zero] using he

end Hilbert

end KineticLangevin
