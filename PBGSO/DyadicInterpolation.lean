import PBGSO.TimeGridContinuity

/-! # Literal continuous polygons on uniform dyadic grids
Finite continuous hat functions interpolate actual node values. The analytic
bounds use only adjacent node increments and do not assume stochastic facts.
-/
noncomputable section
set_option linter.unusedSectionVars false
open Set Filter
open scoped BigOperators Topology
namespace PBGSO.DyadicInterpolation
variable {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]

def hat (N k : ℕ) (t : ℝ) : ℝ := max 0 (1 - |(N : ℝ) * t - k|)

def polygon (N : ℕ) (f : ℕ → R) (t : ℝ) : R :=
  ∑ k ∈ Finset.range (N + 1), hat N k t • f k

theorem hat_continuous (N k : ℕ) : Continuous (hat N k) := by
  unfold hat
  fun_prop

theorem polygon_continuous (N : ℕ) (f : ℕ → R) : Continuous (polygon N f) := by
  unfold polygon
  exact continuous_finsetSum _ (fun k _ => (hat_continuous N k).smul continuous_const)

theorem hat_left (N k : ℕ) (t : ℝ) (hlo : (k : ℝ) ≤ N * t)
    (hhi : (N : ℝ) * t ≤ k + 1) : hat N k t = (k + 1 : ℝ) - N * t := by
  rw [hat, abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  ring

theorem hat_right (N k : ℕ) (t : ℝ) (hlo : (k : ℝ) ≤ N * t)
    (hhi : (N : ℝ) * t ≤ k + 1) : hat N (k + 1) t = (N : ℝ) * t - k := by
  rw [hat, Nat.cast_add, Nat.cast_one, abs_of_nonpos (by linarith),
    max_eq_right (by linarith)]
  ring

theorem hat_other (N k j : ℕ) (t : ℝ) (hlo : (k : ℝ) ≤ N * t)
    (hhi : (N : ℝ) * t ≤ k + 1) (hj : j ≠ k) (hj' : j ≠ k + 1) :
    hat N j t = 0 := by
  unfold hat
  apply max_eq_left
  by_cases hjk : j ≤ k
  · have hlt : j + 1 ≤ k := by omega
    have hc : (j : ℝ) + 1 ≤ k := by exact_mod_cast hlt
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hlt : k + 2 ≤ j := by omega
    have hc : (k : ℝ) + 2 ≤ j := by exact_mod_cast hlt
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- On any actual uniform-grid cell, the polygon is exactly the convex
combination of its two endpoint values. -/
theorem polygon_cell (N k : ℕ) (hk : k < N) (f : ℕ → R) (t : ℝ)
    (hlo : (k : ℝ) ≤ N * t) (hhi : (N : ℝ) * t ≤ k + 1) :
    polygon N f t = ((k + 1 : ℝ) - N * t) • f k +
      ((N : ℝ) * t - k) • f (k + 1) := by
  classical
  have hsub : ({k, k + 1} : Finset ℕ) ⊆ Finset.range (N + 1) := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  calc
    polygon N f t = ∑ j ∈ ({k, k + 1} : Finset ℕ), hat N j t • f j := by
      symm
      apply Finset.sum_subset hsub
      intro j _ hj
      have hn : j ≠ k ∧ j ≠ k + 1 := by
        simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hj
      rw [hat_other N k j t hlo hhi hn.1 hn.2, zero_smul]
    _ = _ := by simp [hat_left N k t hlo hhi, hat_right N k t hlo hhi]

/-- Every point in the unit interval lies in an actual positive-grid cell. -/
theorem exists_cell (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : t ∈ Icc 0 1) :
    ∃ k : ℕ, k < N ∧ (k : ℝ) ≤ N * t ∧ (N : ℝ) * t ≤ k + 1 := by
  have hx : 0 ≤ (N : ℝ) * t := mul_nonneg (Nat.cast_nonneg N) ht.1
  have hxN : (N : ℝ) * t ≤ N := mul_le_of_le_one_right (Nat.cast_nonneg N) ht.2
  by_cases hk : ⌊(N : ℝ) * t⌋₊ < N
  · exact ⟨_, hk, Nat.floor_le hx, (Nat.lt_floor_add_one _).le⟩
  · refine ⟨N - 1, by omega, ?_, ?_⟩
    · have hf : (N : ℝ) ≤ ⌊(N : ℝ) * t⌋₊ := by exact_mod_cast (by omega : N ≤ ⌊(N : ℝ) * t⌋₊)
      have hs : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (Nat.sub_le N 1)
      exact hs.trans (hf.trans (Nat.floor_le hx))
    · have he : ((N - 1 : ℕ) : ℝ) + 1 = N := by exact_mod_cast (Nat.sub_add_cancel hN)
      linarith

/-- Convex interpolation inherits a common endpoint distance bound. -/
theorem polygon_cell_bound (N k : ℕ) (hk : k < N) (f : ℕ → R) (t : ℝ)
    (hlo : (k : ℝ) ≤ N * t) (hhi : (N : ℝ) * t ≤ k + 1)
    (v : R) (C : ℝ) (hleft : ‖f k - v‖ ≤ C) (hright : ‖f (k + 1) - v‖ ≤ C) :
    ‖polygon N f t - v‖ ≤ C := by
  rw [polygon_cell N k hk f t hlo hhi]
  let a : ℝ := (k + 1 : ℝ) - N * t
  let b : ℝ := (N : ℝ) * t - k
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have he : a • f k + b • f (k + 1) - v = a • (f k - v) + b • (f (k + 1) - v) := by
    calc
      _ = a • f k + b • f (k + 1) - (a • v + b • v) := by
        rw [← add_smul, hab, one_smul]
      _ = _ := by rw [smul_sub, smul_sub]; abel
  change ‖a • f k + b • f (k + 1) - v‖ ≤ C
  rw [he]
  calc
    _ ≤ ‖a • (f k - v)‖ + ‖b • (f (k + 1) - v)‖ := norm_add_le _ _
    _ = a * ‖f k - v‖ + b * ‖f (k + 1) - v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * C + b * C := add_le_add (mul_le_mul_of_nonneg_left hleft ha)
      (mul_le_mul_of_nonneg_left hright hb)
    _ = C := by rw [← add_mul, hab, one_mul]

/-- Adjacent node control gives the actual discrete Lipschitz bound. -/
theorem node_dist_forward (M : ℕ) (f : ℕ → R) (a : ℝ)
    (hstep : ∀ j < M, ‖f (j + 1) - f j‖ ≤ a)
    (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ M) :
    ‖f k - f j‖ ≤ ((k : ℝ) - j) * a := by
  induction k with
  | zero =>
    have hj : j = 0 := by omega
    simp [hj]
  | succ k ih =>
    by_cases he : j = k + 1
    · simp [he]
    · have hjk' : j ≤ k := by omega
      have hkm : k ≤ M := by omega
      calc
        ‖f (k + 1) - f j‖ ≤ ‖f (k + 1) - f k‖ + ‖f k - f j‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ a + ((k : ℝ) - j) * a := add_le_add (hstep k (by omega)) (ih hjk' hkm)
        _ = (((k + 1 : ℕ) : ℝ) - j) * a := by push_cast; ring

/-- The node bound is symmetric and valid at both grid endpoints. -/
theorem node_dist (M : ℕ) (f : ℕ → R) (a : ℝ)
    (hstep : ∀ j < M, ‖f (j + 1) - f j‖ ≤ a)
    (j k : ℕ) (hj : j ≤ M) (hk : k ≤ M) :
    ‖f j - f k‖ ≤ |(j : ℝ) - k| * a := by
  by_cases hjk : j ≤ k
  · have hcast : (j : ℝ) ≤ k := by exact_mod_cast hjk
    rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hcast)]
    have h := node_dist_forward M f a hstep j k hjk hk
    linarith
  · have hkj : k ≤ j := by omega
    have hcast : (k : ℝ) ≤ j := by exact_mod_cast hkj
    rw [abs_of_nonneg (sub_nonneg.mpr hcast)]
    exact node_dist_forward M f a hstep k j hkj hj

/-- Doubling a grid changes its actual polygon by at most five times the
largest fine-grid adjacent increment. This bound is uniform on the unit interval. -/
theorem polygon_refine_bound (N : ℕ) (hN : 0 < N) (f g : ℕ → R)
    (hmatch : ∀ j ≤ N, f j = g (2 * j)) (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ j < 2 * N, ‖g (j + 1) - g j‖ ≤ a)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖polygon (2 * N) g t - polygon N f t‖ ≤ 5 * a := by
  obtain ⟨k, hk, hklo, hkhi⟩ := exists_cell N hN t ht
  obtain ⟨l, hl, hllo, hlhi⟩ := exists_cell (2 * N) (by omega) t ht
  have hklim : 2 * k ≤ 2 * N := by omega
  have hfine (j : ℕ) (hjlo : l ≤ j) (hjhi : j ≤ l + 1) : ‖g j - g (2 * k)‖ ≤ 3 * a := by
    have hjlim : j ≤ 2 * N := by omega
    have hi : |(j : ℝ) - (2 * k : ℕ)| ≤ 3 := by
      have hjlo' : (l : ℝ) ≤ j := by exact_mod_cast hjlo
      have hjhi' : (j : ℝ) ≤ l + 1 := by exact_mod_cast hjhi
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hllo hlhi ⊢
      rw [abs_le]
      constructor <;> nlinarith
    exact (node_dist (2 * N) g a hstep j (2 * k) hjlim hklim).trans
      (mul_le_mul_of_nonneg_right hi ha)
  have hF : ‖polygon (2 * N) g t - g (2 * k)‖ ≤ 3 * a :=
    polygon_cell_bound (2 * N) l hl g t hllo hlhi _ _
      (hfine l le_rfl (Nat.le_succ l)) (hfine (l + 1) (Nat.le_succ l) le_rfl)
  have hC : ‖polygon N f t - g (2 * k)‖ ≤ 2 * a := by
    apply polygon_cell_bound N k hk f t hklo hkhi
    · rw [hmatch k (by omega), sub_self, norm_zero]
      positivity
    · rw [hmatch (k + 1) (by omega)]
      have hb := node_dist_forward (2 * N) g a hstep (2 * k) (2 * (k + 1))
        (by omega) (by omega)
      convert hb using 1 <;> push_cast <;> ring
  calc
    ‖polygon (2 * N) g t - polygon N f t‖ ≤
        ‖polygon (2 * N) g t - g (2 * k)‖ + ‖g (2 * k) - polygon N f t‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 * a + 2 * a := by rw [norm_sub_rev (g (2 * k))]; exact add_le_add hF hC
    _ = 5 * a := by ring

/-- The actual polygon sampled from one arbitrary real-indexed curve. -/
def sampledPolygon (N : ℕ) (F : ℝ → R) : ℝ → R :=
  polygon N (fun k => F ((k : ℝ) / N))

theorem sampledPolygon_continuous (N : ℕ) (F : ℝ → R) :
    Continuous (sampledPolygon N F) := polygon_continuous N _

/-- Actual dyadic polygons use the same underlying curve at every level. -/
def dyadicPolygon (n : ℕ) (F : ℝ → R) : ℝ → R := sampledPolygon (2 ^ n) F

theorem dyadicPolygon_continuous (n : ℕ) (F : ℝ → R) :
    Continuous (dyadicPolygon n F) := sampledPolygon_continuous _ _

/-- Exact dyadic refinement consistency follows from the actual sample
indices; no relationship between independently supplied interpolants is assumed. -/
theorem dyadicPolygon_succ_bound (n : ℕ) (F : ℝ → R) (a : ℝ) (ha : 0 ≤ a)
    (hstep : ∀ j < 2 ^ (n + 1),
      ‖F (((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) -
        F ((j : ℝ) / (2 : ℝ) ^ (n + 1))‖ ≤ a)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    ‖dyadicPolygon (n + 1) F t - dyadicPolygon n F t‖ ≤ 5 * a := by
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := by omega
  have hc : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hmatch : ∀ (j : ℕ), j ≤ (2 ^ n : ℕ) →
      F ((j : ℝ) / (2 : ℝ) ^ n) = F (((2 * j : ℕ) : ℝ) / (2 * (2 : ℝ) ^ n)) := by
    intro j _
    congr 1
    push_cast
    field_simp
  have hst : ∀ j < 2 * 2 ^ n,
      ‖F (((j + 1 : ℕ) : ℝ) / (2 * (2 : ℝ) ^ n)) -
        F ((j : ℝ) / (2 * (2 : ℝ) ^ n))‖ ≤ a := by
    intro j hj
    simpa only [pow_succ, mul_comm ((2 : ℝ) ^ n) 2] using hstep j (by omega)
  have hb := polygon_refine_bound (2 ^ n) (by positivity)
    (fun j => F ((j : ℝ) / (2 : ℝ) ^ n))
    (fun j => F ((j : ℝ) / (2 * (2 : ℝ) ^ n))) hmatch a ha hst t ht
  simpa only [dyadicPolygon, sampledPolygon, hp, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hb

/-- A polygon's distance from its left endpoint is bounded by that actual
cell increment. This later identifies continuous polygon limits with past-only
sample limits. -/
theorem polygon_left_bound (N k : ℕ) (hk : k < N) (f : ℕ → R) (t : ℝ)
    (hlo : (k : ℝ) ≤ N * t) (hhi : (N : ℝ) * t ≤ k + 1)
    (a : ℝ) (ha : 0 ≤ a) (hstep : ‖f (k + 1) - f k‖ ≤ a) :
    ‖polygon N f t - f k‖ ≤ a :=
  polygon_cell_bound N k hk f t hlo hhi (f k) a (by simpa using ha) hstep

end PBGSO.DyadicInterpolation
