import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Exponential-integrator coefficients

The functions `psi γ k` are the iterated primitives used in Dalalyan and
Riou-Durand, Sections 4 and 5. Defining them by integrals, rather than quotients
by the friction, also gives the correct zero-friction limit. The function
`phi γ (k+1)` is the exponential convolution of `psi γ k`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace KineticLangevin

/-- The exponential response and its successive time primitives. -/
def psi (γ : ℝ) : ℕ → ℝ → ℝ
  | 0, t => Real.exp (-γ * t)
  | k + 1, t => ∫ s in 0..t, psi γ k s

@[simp] theorem psi_zero (γ t : ℝ) : psi γ 0 t = Real.exp (-γ * t) := rfl

@[simp] theorem psi_succ (γ t : ℝ) (k : ℕ) :
    psi γ (k + 1) t = ∫ s in 0..t, psi γ k s := rfl

theorem continuous_psi (γ : ℝ) (k : ℕ) : Continuous (psi γ k) := by
  induction k with
  | zero => exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  | succ k ih => exact intervalIntegral.continuous_primitive ih.intervalIntegrable 0

/-- Each response coefficient is the primitive of the previous one. -/
theorem hasDerivAt_psi_succ (γ t : ℝ) (k : ℕ) :
    HasDerivAt (psi γ (k + 1)) (psi γ k t) t :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_psi γ k).intervalIntegrable _ _)
    (continuous_psi γ k).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuous_psi γ k).continuousAt

/-- The response of the velocity solves the homogeneous friction equation. -/
theorem hasDerivAt_psi_zero (γ t : ℝ) :
    HasDerivAt (psi γ 0) (-γ * psi γ 0 t) t := by
  convert ((hasDerivAt_id t).const_mul (-γ)).exp using 1 <;> simp [psi, mul_comm]

/-- Exact fluctuation/decay identity, without division by the friction. -/
theorem friction_mul_psi_one (γ t : ℝ) :
    γ * psi γ 1 t = 1 - psi γ 0 t := by
  have hd : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun s => 1 - psi γ 0 s) (γ * psi γ 0 s) s := by
    intro s _
    convert (hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_psi_zero γ s) using 1 <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_const.mul (continuous_psi γ 0)).intervalIntegrable _ _)
  simpa [intervalIntegral.integral_const_mul, psi_succ] using hi

/-- The integrated friction balance is the exact frozen-force position identity. -/
theorem friction_mul_psi_two (γ t : ℝ) :
    γ * psi γ 2 t = t - psi γ 1 t := by
  have he : (fun s => γ * psi γ 1 s) = (fun s => 1 - psi γ 0 s) :=
    funext (friction_mul_psi_one γ)
  have hi := congrArg (fun f : ℝ → ℝ => ∫ s in 0..t, f s) he
  change (∫ s in 0..t, γ * psi γ 1 s) = (∫ s in 0..t, 1 - psi γ 0 s) at hi
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable 0 t)
    ((continuous_psi γ 0).intervalIntegrable 0 t)] at hi
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
    ← psi_succ] using hi

theorem psi_one_closed {γ : ℝ} (hγ : γ ≠ 0) (t : ℝ) :
    psi γ 1 t = (1 - Real.exp (-γ * t)) / γ := by
  apply (eq_div_iff hγ).mpr
  simpa only [psi_zero, mul_comm] using friction_mul_psi_one γ t

theorem psi_two_closed {γ : ℝ} (hγ : γ ≠ 0) (t : ℝ) :
    psi γ 2 t = (t - (1 - Real.exp (-γ * t)) / γ) / γ := by
  apply (eq_div_iff hγ).mpr
  rw [← psi_one_closed hγ]
  simpa only [mul_comm] using friction_mul_psi_two γ t

/-- Exact time-rescaling identity. It is used when converting a non-unit
inverse mass to the paper's convention `u = 1`. -/
theorem psi_scale (c γ t : ℝ) (hc : c ≠ 0) (k : ℕ) :
    psi (c * γ) k t = (c⁻¹) ^ k * psi γ k (c * t) := by
  induction k generalizing t with
  | zero => simp only [psi_zero, pow_zero, one_mul]; congr 1; ring
  | succ k ih =>
    rw [psi_succ]
    simp_rw [ih]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (psi γ k) hc]
    simp only [mul_zero, smul_eq_mul, pow_succ, psi_succ]
    ring

theorem psi_scale_div (c γ h : ℝ) (hc : c ≠ 0) (k : ℕ) :
    psi (c * γ) k (h / c) = psi γ k h / c ^ k := by
  rw [psi_scale c γ (h / c) hc k]
  have ht : c * (h / c) = h := by field_simp
  rw [ht]
  simp only [inv_pow, div_eq_mul_inv, mul_comm]

@[simp] theorem psi_at_zero (γ : ℝ) (k : ℕ) :
    psi γ k 0 = if k = 0 then 1 else 0 := by
  cases k <;> simp [psi]

theorem psi_nonneg (γ : ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ psi γ k t := by
  induction k generalizing t with
  | zero => exact (Real.exp_pos _).le
  | succ k ih => exact intervalIntegral.integral_nonneg ht fun s hs => ih hs.1

theorem psi_pos (γ : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) : 0 < psi γ k t := by
  induction k generalizing t with
  | zero => exact Real.exp_pos _
  | succ k ih =>
    apply intervalIntegral.integral_pos ht (continuous_psi γ k).continuousOn
    · intro s hs
      exact psi_nonneg γ k hs.1.le
    · exact ⟨t, ⟨ht.le, le_rfl⟩, ih ht⟩

theorem psi_zero_le_one {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    psi γ 0 t ≤ 1 := by
  rw [psi_zero, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) ht

theorem psi_one_le {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    psi γ 1 t ≤ t := by
  calc
    psi γ 1 t ≤ ∫ s in 0..t, (1 : ℝ) :=
      intervalIntegral.integral_mono_on ht (continuous_psi γ 0 |>.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) fun s hs => psi_zero_le_one hγ hs.1
    _ = t := by simp

theorem psi_two_le {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    psi γ 2 t ≤ t ^ 2 / 2 := by
  calc
    psi γ 2 t ≤ ∫ s in 0..t, s :=
      intervalIntegral.integral_mono_on ht (continuous_psi γ 1 |>.intervalIntegrable _ _)
        (continuous_id.intervalIntegrable _ _) fun s hs => psi_one_le hγ hs.1
    _ = t ^ 2 / 2 := by simpa using (integral_pow (a := 0) (b := t) 1)

@[simp] theorem psi_friction_zero_zero (t : ℝ) : psi 0 0 t = 1 := by simp [psi]

@[simp] theorem psi_friction_zero_one (t : ℝ) : psi 0 1 t = t := by simp [psi]

@[simp] theorem psi_friction_zero_two (t : ℝ) : psi 0 2 t = t ^ 2 / 2 := by
  simpa [psi] using (integral_pow (a := 0) (b := t) 1)

/-- At zero friction, every response coefficient is the usual Taylor coefficient. -/
theorem psi_friction_zero (t : ℝ) (k : ℕ) :
    psi 0 k t = t ^ k / (k.factorial : ℝ) := by
  induction k generalizing t with
  | zero => simp [psi]
  | succ k ih =>
    rw [psi_succ]
    simp_rw [ih]
    rw [intervalIntegral.integral_div, integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero k), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    simp only [div_div, mul_comm]

/-- Friction can only decrease each positive-time primitive. -/
theorem psi_le_taylor {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) (k : ℕ) :
    psi γ k t ≤ t ^ k / (k.factorial : ℝ) := by
  have hm : ∀ k, ∀ t : ℝ, 0 ≤ t → psi γ k t ≤ psi 0 k t := by
    intro k
    induction k with
    | zero => intro t ht; simpa using psi_zero_le_one hγ ht
    | succ k ih =>
      intro t ht
      exact intervalIntegral.integral_mono_on ht
        ((continuous_psi γ k).intervalIntegrable _ _)
        ((continuous_psi 0 k).intervalIntegrable _ _) fun s hs => ih s hs.1
  simpa only [psi_friction_zero] using hm k t ht

/-- Exponential convolution, numbered as `φ` in the paper (`φ₀ = 0`). -/
def phi (γ : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | k + 1, t => ∫ s in 0..t, Real.exp (-γ * (t - s)) * psi γ k s

@[simp] theorem phi_zero (γ t : ℝ) : phi γ 0 t = 0 := rfl

@[simp] theorem phi_succ (γ t : ℝ) (k : ℕ) :
    phi γ (k + 1) t = ∫ s in 0..t, Real.exp (-γ * (t - s)) * psi γ k s := rfl

theorem phi_nonneg (γ : ℝ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ phi γ k t := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact intervalIntegral.integral_nonneg ht fun s hs =>
      mul_nonneg (Real.exp_pos _).le (psi_nonneg γ k hs.1)

theorem phi_factor (γ t : ℝ) (k : ℕ) :
    phi γ (k + 1) t = Real.exp (-γ * t) *
      ∫ s in 0..t, Real.exp (γ * s) * psi γ k s := by
  rw [phi_succ, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem continuous_phi (γ : ℝ) (k : ℕ) : Continuous (phi γ k) := by
  cases k with
  | zero => exact continuous_const
  | succ k =>
    have hc : Continuous (fun t : ℝ => Real.exp (-γ * t) *
        ∫ s in 0..t, Real.exp (γ * s) * psi γ k s) :=
      (continuous_psi γ 0).mul (intervalIntegral.continuous_primitive (μ := volume)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_psi γ k)).intervalIntegrable 0)
    exact hc.congr (fun t => (phi_factor γ t k).symm)

@[simp] theorem phi_at_zero (γ : ℝ) (k : ℕ) : phi γ k 0 = 0 := by
  cases k <;> simp [phi]

theorem phi_le_psi {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) (k : ℕ) :
    phi γ (k + 1) t ≤ psi γ (k + 1) t := by
  apply intervalIntegral.integral_mono_on ht
    (((Real.continuous_exp.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).mul (continuous_psi γ k)).intervalIntegrable _ _)
    ((continuous_psi γ k).intervalIntegrable _ _)
  intro s hs
  exact mul_le_of_le_one_left (psi_nonneg γ k hs.1)
    (by exact psi_zero_le_one hγ (sub_nonneg.mpr hs.2))

@[simp] theorem phi_friction_zero (k : ℕ) (t : ℝ) :
    phi 0 (k + 1) t = psi 0 (k + 1) t := by simp [phi, psi_succ]

theorem phi_one (γ t : ℝ) : phi γ 1 t = t * psi γ 0 t := by
  rw [phi_succ]
  have he : (fun s => Real.exp (-γ * (t - s)) * psi γ 0 s) =
      (fun _ : ℝ => psi γ 0 t) := by
    funext s
    simp only [psi_zero, ← Real.exp_add]
    congr 1
    ring
  rw [he, intervalIntegral.integral_const]
  simp [smul_eq_mul]

theorem integral_reverse_exponential (γ t : ℝ) :
    (∫ s in 0..t, Real.exp (-γ * (t - s))) = psi γ 1 t := by
  simpa only [sub_self, sub_zero, psi_succ, psi_zero] using
    intervalIntegral.integral_comp_sub_left (psi γ 0) t (a := 0) (b := t)

theorem friction_mul_phi_two (γ t : ℝ) :
    γ * phi γ 2 t = psi γ 1 t - t * psi γ 0 t := by
  have hc1 : Continuous (fun s : ℝ => Real.exp (-γ * (t - s))) := by fun_prop
  have he : (fun s => γ * (Real.exp (-γ * (t - s)) * psi γ 1 s)) =
      (fun s => Real.exp (-γ * (t - s)) - psi γ 0 t) := by
    funext s
    calc
      γ * (Real.exp (-γ * (t - s)) * psi γ 1 s) =
          Real.exp (-γ * (t - s)) * (γ * psi γ 1 s) := by ring
      _ = Real.exp (-γ * (t - s)) * (1 - psi γ 0 s) := by rw [friction_mul_psi_one]
      _ = Real.exp (-γ * (t - s)) - psi γ 0 t := by
        simp only [psi_zero, mul_sub, mul_one, ← Real.exp_add]
        congr 2
        ring
  have hi := congrArg (fun f : ℝ → ℝ => ∫ s in 0..t, f s) he
  change (∫ s in 0..t, γ * (Real.exp (-γ * (t - s)) * psi γ 1 s)) = _ at hi
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (hc1.intervalIntegrable 0 t) (continuous_const.intervalIntegrable 0 t)] at hi
  rw [integral_reverse_exponential, intervalIntegral.integral_const] at hi
  simpa only [← phi_succ, sub_zero, smul_eq_mul] using hi

theorem integral_reverse_exponential_mul (γ t : ℝ) :
    (∫ s in 0..t, Real.exp (-γ * (t - s)) * s) = psi γ 2 t := by
  have hd : ∀ s ∈ uIcc 0 t,
      HasDerivAt (fun s => (t - s) * psi γ 1 s + psi γ 2 s)
        ((t - s) * psi γ 0 s) s := by
    intro s _
    convert (((hasDerivAt_const s t).sub (hasDerivAt_id s)).mul
      (hasDerivAt_psi_succ γ s 0)).add (hasDerivAt_psi_succ γ s 1) using 1 <;>
      simp only [Pi.add_def, Pi.sub_def, Pi.mul_def]
    all_goals try funext u
    all_goals simp only [id_eq]
    all_goals ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_const.sub continuous_id).mul (continuous_psi γ 0)).intervalIntegrable 0 t)
  have hr := intervalIntegral.integral_comp_sub_left
    (fun s => (t - s) * psi γ 0 s) t (a := 0) (b := t)
  simp only [sub_self, sub_zero] at hr hi
  rw [← hr] at hi
  simpa only [sub_sub_cancel, psi_zero, mul_zero, zero_add, psi_at_zero,
    zero_mul, add_zero, sub_zero, one_ne_zero, ↓reduceIte, OfNat.ofNat_ne_zero,
    mul_comm] using hi

/-- Exact balance between the second-order correction coefficients. In
particular, `φ₂ ≤ ψ₂` for nonnegative friction and positive time. -/
theorem phi_two_add_friction_phi_three (γ t : ℝ) :
    phi γ 2 t + γ * phi γ 3 t = psi γ 2 t := by
  have hc : Continuous (fun s : ℝ => Real.exp (-γ * (t - s))) := by fun_prop
  have h1 : IntervalIntegrable (fun s => Real.exp (-γ * (t - s)) * psi γ 1 s)
      volume 0 t := (hc.mul (continuous_psi γ 1)).intervalIntegrable 0 t
  have h2 : IntervalIntegrable (fun s => γ * (Real.exp (-γ * (t - s)) * psi γ 2 s))
      volume 0 t := (continuous_const.mul (hc.mul (continuous_psi γ 2))).intervalIntegrable 0 t
  rw [phi_succ, phi_succ, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add h1 h2]
  calc
    _ = ∫ s in 0..t, Real.exp (-γ * (t - s)) * s := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      have hi := friction_mul_psi_two γ s
      linear_combination Real.exp (-γ * (t - s)) * hi
    _ = _ := integral_reverse_exponential_mul γ t

theorem phi_two_le_psi_two {γ t : ℝ} (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    phi γ 2 t ≤ psi γ 2 t := by
  have hi := phi_two_add_friction_phi_three γ t
  have hp := mul_nonneg hγ (phi_nonneg γ 3 ht)
  linarith

/-- The covariance matrix of Brownian convolutions with deterministic kernels. -/
def gramCovariance {ι : Type*} (kernels : ι → ℝ → ℝ) (h : ℝ) : Matrix ι ι ℝ :=
  fun i j => ∫ t in 0..h, kernels i t * kernels j t

theorem gramCovariance_symmetric {ι : Type*} (kernels : ι → ℝ → ℝ) (h : ℝ) :
    (gramCovariance kernels h).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, gramCovariance, mul_comm]

/-- A covariance quadratic form is an integral of a square. This proves that
the correlations in the algorithms define valid Gaussian covariance matrices. -/
theorem gramCovariance_quadratic {ι : Type*} [Fintype ι]
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i))
    (h : ℝ) (z : ι → ℝ) :
    (∑ i, ∑ j, z i * gramCovariance kernels h i j * z j) =
      ∫ t in 0..h, (∑ i, z i * kernels i t) ^ 2 := by
  have hi (i j : ι) : IntervalIntegrable
      (fun t => z i * (kernels i t * kernels j t) * z j) volume 0 h :=
    ((continuous_const.mul ((hc i).mul (hc j))).mul continuous_const).intervalIntegrable _ _
  simp_rw [gramCovariance, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_mul_const]
  have hs (i : ι) : (∑ j, ∫ t in 0..h, z i * (kernels i t * kernels j t) * z j) =
      ∫ t in 0..h, ∑ j, z i * (kernels i t * kernels j t) * z j :=
    (intervalIntegral.integral_finsetSum (fun j _ => hi i j)).symm
  simp_rw [hs]
  rw [← intervalIntegral.integral_finsetSum]
  · congr 1
    funext t
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro i _
    exact (continuous_finsetSum _ fun j _ =>
      (continuous_const.mul ((hc i).mul (hc j))).mul continuous_const).intervalIntegrable _ _

theorem gramCovariance_posSemidef {ι : Type*} [Fintype ι]
    (kernels : ι → ℝ → ℝ) (hc : ∀ i, Continuous (kernels i))
    {h : ℝ} (hh : 0 ≤ h) : (gramCovariance kernels h).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr (gramCovariance_symmetric kernels h), ?_⟩
  intro z
  simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
  have he : (∑ i, ∑ j, z i * (gramCovariance kernels h i j * z j)) =
      (∑ i, ∑ j, z i * gramCovariance kernels h i j * z j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, gramCovariance_quadratic kernels hc]
  exact intervalIntegral.integral_nonneg_of_forall hh fun t => sq_nonneg _

/-- The two Brownian kernels in the first-order KLMC update. -/
def klmcKernels (γ : ℝ) : Fin 2 → ℝ → ℝ := ![psi γ 0, psi γ 1]

/-- The four jointly sampled Brownian kernels in the second-order KLMC update. -/
def klmc2Kernels (γ : ℝ) : Fin 4 → ℝ → ℝ :=
  ![psi γ 0, psi γ 1, phi γ 2, phi γ 3]

/-- Covariance of the unscaled, correlated velocity-position innovation. -/
def klmcCovariance (γ h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  gramCovariance (klmcKernels γ) h

/-- Covariance of the four jointly Gaussian innovations used by KLMC2. -/
def klmc2Covariance (γ h : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  gramCovariance (klmc2Kernels γ) h

theorem continuous_klmcKernels (γ : ℝ) (i : Fin 2) :
    Continuous (klmcKernels γ i) := by
  fin_cases i <;> simp [klmcKernels, continuous_psi]

theorem continuous_klmc2Kernels (γ : ℝ) (i : Fin 4) :
    Continuous (klmc2Kernels γ i) := by
  fin_cases i <;> simp [klmc2Kernels, continuous_psi, continuous_phi]

theorem klmcCovariance_posSemidef (γ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    (klmcCovariance γ h).PosSemidef :=
  gramCovariance_posSemidef _ (continuous_klmcKernels γ) hh

theorem klmc2Covariance_posSemidef (γ : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    (klmc2Covariance γ h).PosSemidef :=
  gramCovariance_posSemidef _ (continuous_klmc2Kernels γ) hh

theorem klmcCovariance_velocity (γ h : ℝ) :
    klmcCovariance γ h 0 0 = psi (2 * γ) 1 h := by
  change (∫ t in 0..h, Real.exp (-γ * t) * Real.exp (-γ * t)) = _
  rw [psi_succ]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [psi_zero]
  rw [← Real.exp_add]
  congr 1
  ring

theorem klmcCovariance_cross (γ h : ℝ) :
    klmcCovariance γ h 0 1 = (psi γ 1 h) ^ 2 / 2 := by
  have hd : ∀ s ∈ uIcc 0 h,
      HasDerivAt (fun s => (psi γ 1 s) ^ 2 / 2) (psi γ 0 s * psi γ 1 s) s := by
    intro s _
    convert ((hasDerivAt_psi_succ γ s 0).pow 2).div_const 2 using 1 <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_psi γ 0).mul (continuous_psi γ 1)).intervalIntegrable 0 h)
  change (∫ s in 0..h, psi γ 0 s * psi γ 1 s) = _
  simpa only [psi_at_zero, one_ne_zero, ↓reduceIte,
    zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using hi

/-- Fluctuation and friction preserve unit stationary velocity variance. -/
theorem velocity_variance_balance (γ h : ℝ) :
    (psi γ 0 h) ^ 2 + 2 * γ * klmcCovariance γ h 0 0 = 1 := by
  rw [klmcCovariance_velocity, friction_mul_psi_one]
  have he : psi (2 * γ) 0 h = (psi γ 0 h) ^ 2 := by
    simp only [psi_zero, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

end KineticLangevin
