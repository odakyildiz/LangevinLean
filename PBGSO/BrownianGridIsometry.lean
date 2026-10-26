import PBGSO.PredictableIsometry
import UnadjustedLangevin.CanonicalBrownian
import Mathlib.Probability.Process.Adapted

/-! # Consistent predictable sums on one actual Brownian source

Every time grid uses increments of the same Brownian process. Coefficients
may depend on its full past. No stochastic-integral or quadratic-forward
identity is an input.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.BrownianGridIsometry
open PBGSO.PredictableIsometry
variable {Ω Z : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]
  (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B Q)
  (hBm : ∀ t, Measurable (B t))

abbrev brownianFiltration : Filtration ℝ≥0 mΩ :=
  Filtration.natural B (fun t => (hBm t).stronglyMeasurable)

def increment (s t : ℝ≥0) (ω : Ω) : ℝ := B t ω - B s ω

include hB

theorem increment_hasLaw (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw (increment B s t) (gaussianReal 0 (t - s)) Q := by
  change HasLaw (fun ω => B t ω - B s ω) _ Q
  simpa only [add_tsub_cancel_of_le hst] using (hB.shift s).hasLaw_eval (t - s)

theorem increment_memLp (s t : ℝ≥0) (hst : s ≤ t) :
    MemLp (increment B s t) 2 Q :=
  (increment_hasLaw Q B hB s t hst).memLp (memLp_id_gaussianReal (2 : ℝ≥0))

theorem increment_mean (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, increment B s t ω ∂Q) = 0 := by
  exact ((increment_hasLaw Q B hB s t hst).integral_comp
    (f := id) (by fun_prop)).trans integral_id_gaussianReal

theorem increment_second_moment (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ ω, increment B s t ω ^ 2 ∂Q) = (t : ℝ) - s := by
  have he := ((increment_hasLaw Q B hB s t hst).integral_comp
    (f := fun x : ℝ => x ^ 2) (by fun_prop)).trans
    (ULA.centered_gaussian_second_moment (t - s))
  simpa only [NNReal.coe_sub hst, Function.comp_apply] using he

/-- A future increment is independent from the entire natural past,
not merely from one previously chosen grid. -/
theorem increment_independent_past (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (increment B s t) inferInstance)
      (brownianFiltration B hBm s) Q := by
  have hind := (hB.indepFun_shift s).comp (measurable_pi_apply (t - s)) measurable_id
  rw [brownianFiltration, Filtration.natural_eq_comap]
  change IndepFun (fun ω => B t ω - B s ω) (fun ω (u : Iic s) => B u ω) Q
  change IndepFun (fun ω => B (s + (t - s)) ω - B s ω)
    (fun ω (u : Iic s) => B u ω) Q at hind
  rw [add_tsub_cancel_of_le hst] at hind
  exact hind

theorem increment_independent_coefficient (s t : ℝ≥0) (hst : s ≤ t)
    (A : Ω → Z) (hA : StronglyMeasurable[brownianFiltration B hBm s] A) :
    IndepFun (increment B s t) A Q := by
  exact indep_of_indep_of_le_right (increment_independent_past Q B hB hBm s t hst)
    hA.measurable.comap_le

theorem increment_smul_memLp (s t : ℝ≥0) (hst : s ≤ t)
    (A : Ω → Z) (hA : StronglyMeasurable[brownianFiltration B hBm s] A)
    (hA2 : MemLp A 2 Q) : MemLp (fun ω => increment B s t ω • A ω) 2 Q :=
  independent_smul_memLp Q _ _ (increment_memLp Q B hB s t hst) hA2
    (increment_independent_coefficient Q B hB hBm s t hst A hA)

/-- Exact weighted one-step isometry, including zero-length intervals. -/
theorem increment_smul_isometry (W : Z →L[ℝ] Z) (s t : ℝ≥0) (hst : s ≤ t)
    (A : Ω → Z) (hA : StronglyMeasurable[brownianFiltration B hBm s] A)
    (hA2 : MemLp A 2 Q) :
    (∫ ω, ⟪increment B s t ω • A ω, W (increment B s t ω • A ω)⟫_ℝ ∂Q) =
      ((t : ℝ) - s) * (∫ ω, ⟪A ω, W (A ω)⟫_ℝ ∂Q) := by
  have hind := (increment_independent_coefficient Q B hB hBm s t hst A hA).comp
    (show Measurable (fun x : ℝ => x ^ 2) by fun_prop)
    (show Measurable (fun z : Z => ⟪z, W z⟫_ℝ) by fun_prop)
  have hi1 := ((memLp_two_iff_integrable_sq_norm
    (increment_memLp Q B hB s t hst).aestronglyMeasurable).mp
      (increment_memLp Q B hB s t hst))
  have hi2 := pairing_integrable Q W A A hA2 hA2
  have he := hind.integral_mul_eq_mul_integral
    ((continuous_pow 2).aestronglyMeasurable.comp_aemeasurable
      (increment_hasLaw Q B hB s t hst).aemeasurable) hi2.aestronglyMeasurable
  simp only [Function.comp_apply] at he
  rw [increment_second_moment Q B hB s t hst] at he
  convert he using 1
  apply integral_congr_ae
  exact ae_of_all Q fun ω => by
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right,
      Function.comp_apply, Pi.mul_apply]
    ring

theorem increment_smul_condExp_zero (s t : ℝ≥0) (hst : s ≤ t)
    (A : Ω → Z) (hA : StronglyMeasurable[brownianFiltration B hBm s] A)
    (hA2 : MemLp A 2 Q) :
    Q[(fun ω => increment B s t ω • A ω) | brownianFiltration B hBm s] =ᵐ[Q]
      (0 : Ω → Z) := by
  let F := brownianFiltration B hBm s
  let G := MeasurableSpace.comap (increment B s t) inferInstance
  have hF : F ≤ mΩ := (brownianFiltration (mΩ := mΩ) B hBm).le s
  have hm : @Measurable Ω ℝ mΩ inferInstance (increment B s t) :=
    (hBm t).sub (hBm s)
  have hG : G ≤ mΩ := hm.comap_le
  have hmeas : StronglyMeasurable[G] (increment B s t) :=
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have hzero := condExp_indep_eq (μ := Q) hG hF hmeas
    (increment_independent_past (mΩ := mΩ) Q B hB hBm s t hst)
  have hzero' : Q[increment B s t | F] =ᵐ[Q] (0 : Ω → ℝ) := by
    change Q[increment B s t | F] =ᵐ[Q] (fun _ => (0 : ℝ))
    simpa only [increment_mean (mΩ := mΩ) Q B hB s t hst] using hzero
  have hp := condExp_smul_of_aestronglyMeasurable_right (mΩ := mΩ)
    ((increment_memLp (mΩ := mΩ) Q B hB s t hst).integrable (by norm_num))
    ((increment_smul_memLp (mΩ := mΩ) Q B hB hBm s t hst A hA hA2).integrable (by norm_num))
    hA.aestronglyMeasurable
  have heqfun : increment B s t • A = (fun ω => increment B s t ω • A ω) := rfl
  rw [heqfun] at hp
  filter_upwards [hp, hzero'] with ω hp hz
  have hz' : Q[increment B s t | brownianFiltration (mΩ := mΩ) B hBm s] ω = 0 := hz
  simp only [Pi.smul_apply'] at hp
  rw [hz', zero_smul] at hp
  exact hp



omit hB in
/-- A finite predictable left-step integral on the actual Brownian path. -/
def gridSum (τ : ℕ → ℝ≥0) (A : ℕ → Ω → Z) (n : ℕ) (ω : Ω) : Z :=
  ∑ k : Fin n, increment B (τ k) (τ (k + 1)) ω • A k ω

omit hB in
theorem gridSum_zero (τ : ℕ → ℝ≥0) (A : ℕ → Ω → Z) (ω : Ω) :
    gridSum B τ A 0 ω = 0 := by simp [gridSum]

omit hB in
theorem gridSum_succ (τ : ℕ → ℝ≥0) (A : ℕ → Ω → Z) (n : ℕ) (ω : Ω) :
    gridSum B τ A (n + 1) ω = gridSum B τ A n ω +
      increment B (τ n) (τ (n + 1)) ω • A n ω := by
  simp only [gridSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem gridSum_memLp (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : ℕ → Ω → Z)
    (hA : ∀ k, StronglyMeasurable[brownianFiltration B hBm (τ k)] (A k))
    (hA2 : ∀ k, MemLp (A k) 2 Q) (n : ℕ) : MemLp (gridSum B τ A n) 2 Q := by
  apply memLp_finsetSum Finset.univ
  intro k _
  exact increment_smul_memLp Q B hB hBm _ _ (hτ (Nat.le_succ k)) (A k) (hA k) (hA2 k)

omit hB in
theorem gridSum_adapted (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : ℕ → Ω → Z)
    (hA : ∀ k, StronglyMeasurable[brownianFiltration B hBm (τ k)] (A k))
    (n : ℕ) : StronglyMeasurable[brownianFiltration B hBm (τ n)] (gridSum B τ A n) := by
  have hBmeas (k : ℕ) : StronglyMeasurable[brownianFiltration B hBm (τ k)] (B (τ k)) :=
    Filtration.stronglyAdapted_natural (fun t => (hBm t).stronglyMeasurable) (τ k)
  apply Finset.stronglyMeasurable_fun_sum
  intro k _
  have hb1 := (hBmeas (k + 1)).mono
    ((brownianFiltration B hBm).mono (hτ (Nat.succ_le_of_lt k.isLt)))
  have hb0 := (hBmeas k).mono
    ((brownianFiltration B hBm).mono (hτ (Nat.le_of_lt k.isLt)))
  have ha := (hA k).mono
    ((brownianFiltration B hBm).mono (hτ (Nat.le_of_lt k.isLt)))
  exact (hb1.sub hb0).smul ha

omit hB in
def gridFiltration (τ : ℕ → ℝ≥0) (hτ : Monotone τ) : Filtration ℕ mΩ where
  seq n := brownianFiltration B hBm (τ n)
  mono' _ _ h := (brownianFiltration B hBm).mono (hτ h)
  le' n := (brownianFiltration B hBm).le (τ n)


/-- The finite grid integral is a genuine martingale for the sampled
natural filtration. Brownian future/past independence discharges the
conditional-centering premise. -/
theorem gridSum_martingale (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : ℕ → Ω → Z)
    (hA : ∀ k, StronglyMeasurable[brownianFiltration B hBm (τ k)] (A k))
    (hA2 : ∀ k, MemLp (A k) 2 Q) :
    Martingale (gridSum B τ A) (gridFiltration B hBm τ hτ) Q := by
  apply martingale_of_condExp_sub_eq_zero_nat
    (show StronglyAdapted (gridFiltration B hBm τ hτ) (gridSum B τ A) from
      gridSum_adapted B hBm τ hτ A hA)
    (fun n => (gridSum_memLp Q B hB hBm τ hτ A hA hA2 n).integrable (by norm_num))
  intro n
  have heq : gridSum B τ A (n + 1) - gridSum B τ A n =
      (fun ω => increment B (τ n) (τ (n + 1)) ω • A n ω) := by
    funext ω
    simp only [Pi.sub_apply, gridSum_succ, add_sub_cancel_left]
  rw [heq]
  exact increment_smul_condExp_zero Q B hB hBm _ _ (hτ (Nat.le_succ n))
    (A n) (hA n) (hA2 n)

/-- Exact finite-grid weighted isometry on one Brownian source. -/
theorem gridSum_isometry (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : ℕ → Ω → Z)
    (hA : ∀ k, StronglyMeasurable[brownianFiltration B hBm (τ k)] (A k))
    (hA2 : ∀ k, MemLp (A k) 2 Q) (n : ℕ) :
    (∫ ω, ⟪gridSum B τ A n ω, W (gridSum B τ A n ω)⟫_ℝ ∂Q) =
      ∑ k : Fin n, ((τ (k + 1) : ℝ) - τ k) *
        (∫ ω, ⟪A k ω, W (A k ω)⟫_ℝ ∂Q) := by
  induction n with
  | zero => simp only [gridSum_zero, inner_zero_left, integral_zero,
      Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
    let Y : Ω → Z := fun ω => increment B (τ n) (τ (n + 1)) ω • A n ω
    have hX2 := gridSum_memLp Q B hB hBm τ hτ A hA hA2 n
    have hY2 := increment_smul_memLp Q B hB hBm _ _ (hτ (Nat.le_succ n))
      (A n) (hA n) (hA2 n)
    have hcross := conditional_zero_pairing Q W (brownianFiltration B hBm (τ n))
      ((brownianFiltration B hBm).le (τ n)) (gridSum B τ A n) Y hX2 hY2
      (gridSum_adapted B hBm τ hτ A hA n).aestronglyMeasurable
      (increment_smul_condExp_zero Q B hB hBm _ _ (hτ (Nat.le_succ n))
        (A n) (hA n) (hA2 n))
    have hpoint : (fun ω => ⟪gridSum B τ A (n + 1) ω, W (gridSum B τ A (n + 1) ω)⟫_ℝ) =
        (fun ω => ⟪gridSum B τ A n ω, W (gridSum B τ A n ω)⟫_ℝ +
          2 * ⟪gridSum B τ A n ω, W (Y ω)⟫_ℝ + ⟪Y ω, W (Y ω)⟫_ℝ) := by
      funext ω
      rw [gridSum_succ]
      change ⟪gridSum B τ A n ω + Y ω, W (gridSum B τ A n ω + Y ω)⟫_ℝ = _
      simp only [map_add, inner_add_left, inner_add_right]
      have hs : ⟪Y ω, W (gridSum B τ A n ω)⟫_ℝ =
          ⟪gridSum B τ A n ω, W (Y ω)⟫_ℝ :=
        (real_inner_comm _ _).trans (hW _ _).symm
      rw [hs]
      ring
    have h00 := pairing_integrable Q W _ _ hX2 hX2
    have h01 := (pairing_integrable Q W _ _ hX2 hY2).const_mul 2
    have h11 := pairing_integrable Q W _ _ hY2 hY2
    have hint1 := integral_add (h00.add h01) h11
    have hint2 := integral_add h00 h01
    simp only [Pi.add_apply] at hint1 hint2
    rw [hpoint, hint1, hint2, integral_const_mul, hcross, mul_zero, add_zero, ih]
    change _ + (∫ ω, ⟪increment B (τ n) (τ (n + 1)) ω • A n ω,
      W (increment B (τ n) (τ (n + 1)) ω • A n ω)⟫_ℝ ∂Q) = _
    rw [increment_smul_isometry Q B hB hBm W _ _ (hτ (Nat.le_succ n)) (A n) (hA n) (hA2 n),
      Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]



/-- The actual finite-grid L² norm is the coefficient time-energy. -/
theorem gridSum_norm_sq (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A : ℕ → Ω → Z)
    (hA : ∀ k, StronglyMeasurable[brownianFiltration B hBm (τ k)] (A k))
    (hA2 : ∀ k, MemLp (A k) 2 Q) (n : ℕ) :
    ‖(gridSum_memLp Q B hB hBm τ hτ A hA hA2 n).toLp (gridSum B τ A n)‖ ^ 2 =
      ∑ k : Fin n, ((τ (k + 1) : ℝ) - τ k) * (∫ ω, ‖A k ω‖ ^ 2 ∂Q) := by
  let hS := gridSum_memLp Q B hB hBm τ hτ A hA hA2 n
  rw [ProximalLangevin.lp_norm_sq_eq_integral]
  have he : (∫ ω, ‖hS.toLp (gridSum B τ A n) ω‖ ^ 2 ∂Q) =
      ∫ ω, ‖gridSum B τ A n ω‖ ^ 2 ∂Q :=
    integral_congr_ae (hS.coeFn_toLp.fun_comp (fun z : Z => ‖z‖ ^ 2))
  rw [he]
  simpa only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
    gridSum_isometry Q B hB hBm (ContinuousLinearMap.id ℝ Z) (fun _ _ => rfl)
      τ hτ A hA hA2 n

omit hB in
theorem gridSum_sub (τ : ℕ → ℝ≥0) (A C : ℕ → Ω → Z) (n : ℕ) (ω : Ω) :
    gridSum B τ (A - C) n ω = gridSum B τ A n ω - gridSum B τ C n ω := by
  simp only [gridSum, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Exact L² distance for two adapted integrands on the same actual grid. -/
theorem gridSum_distance_sq (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (A C : ℕ → Ω → Z)
    (hA : ∀ k, StronglyMeasurable[brownianFiltration B hBm (τ k)] (A k))
    (hC : ∀ k, StronglyMeasurable[brownianFiltration B hBm (τ k)] (C k))
    (hA2 : ∀ k, MemLp (A k) 2 Q) (hC2 : ∀ k, MemLp (C k) 2 Q) (n : ℕ) :
    ‖(gridSum_memLp Q B hB hBm τ hτ A hA hA2 n).toLp (gridSum B τ A n) -
      (gridSum_memLp Q B hB hBm τ hτ C hC hC2 n).toLp (gridSum B τ C n)‖ ^ 2 =
      ∑ k : Fin n, ((τ (k + 1) : ℝ) - τ k) * (∫ ω, ‖A k ω - C k ω‖ ^ 2 ∂Q) := by
  let hS := gridSum_memLp Q B hB hBm τ hτ (A - C)
    (fun k => (hA k).sub (hC k)) (fun k => (hA2 k).sub (hC2 k)) n
  have heq : hS.toLp (gridSum B τ (A - C) n) =
      (gridSum_memLp Q B hB hBm τ hτ A hA hA2 n).toLp (gridSum B τ A n) -
      (gridSum_memLp Q B hB hBm τ hτ C hC hC2 n).toLp (gridSum B τ C n) := by
    apply Lp.ext
    filter_upwards [hS.coeFn_toLp,
      (gridSum_memLp Q B hB hBm τ hτ A hA hA2 n).coeFn_toLp,
      (gridSum_memLp Q B hB hBm τ hτ C hC hC2 n).coeFn_toLp,
      Lp.coeFn_sub
        ((gridSum_memLp Q B hB hBm τ hτ A hA hA2 n).toLp (gridSum B τ A n))
        ((gridSum_memLp Q B hB hBm τ hτ C hC hC2 n).toLp (gridSum B τ C n))]
      with ω hs ha hc hsub
    rw [hsub, Pi.sub_apply, hs, ha, hc]
    exact gridSum_sub B τ A C n ω
  rw [← heq]
  exact gridSum_norm_sq Q B hB hBm τ hτ (A - C)
    (fun k => (hA k).sub (hC k)) (fun k => (hA2 k).sub (hC2 k)) n

omit hB in
/-- Subdividing every interval in two leaves the actual sum exactly
unchanged when its coefficient is held constant on the two subintervals.
The midpoint locations may be arbitrary. -/
theorem gridSum_refine_two (τ υ : ℕ → ℝ≥0) (hυ : ∀ k, υ (2 * k) = τ k)
    (A : ℕ → Ω → Z) (n : ℕ) (ω : Ω) :
    gridSum B υ (fun k => A (k / 2)) (2 * n) ω = gridSum B τ A n ω := by
  induction n with
  | zero => simp only [mul_zero, gridSum_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      gridSum_succ, gridSum_succ, ih, gridSum_succ]
    have hn0 : 2 * n / 2 = n := by omega
    have hn1 : (2 * n + 1) / 2 = n := by omega
    simp only [hn0, hn1]
    rw [add_assoc, ← add_smul]
    congr 2
    simp only [increment]
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, hυ n, hυ (n + 1)]
    ring

omit hB in
theorem refined_coefficients_adapted (τ υ : ℕ → ℝ≥0) (hυmono : Monotone υ)
    (hυ : ∀ k, υ (2 * k) = τ k) (A : ℕ → Ω → Z)
    (hA : ∀ k, StronglyMeasurable[brownianFiltration B hBm (τ k)] (A k)) (j : ℕ) :
    StronglyMeasurable[brownianFiltration B hBm (υ j)] (A (j / 2)) := by
  apply (hA (j / 2)).mono
  apply (brownianFiltration B hBm).mono
  rw [← hυ (j / 2)]
  exact hυmono (by omega)



omit hB in
theorem constant_block_sum (υ : ℕ → ℝ≥0) (a d : ℕ) (z : Z) (ω : Ω) :
    (∑ j ∈ Finset.range d, increment B (υ (a + j)) (υ (a + j + 1)) ω • z) =
      increment B (υ a) (υ (a + d)) ω • z := by
  induction d with
  | zero => simp [increment]
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, ← add_smul]
    congr 1
    simp only [increment, add_assoc]
    ring

omit hB in
/-- Exact consistency under any equal-count subdivision. The new grid
points may be arbitrary; only the old endpoints must match. -/
theorem gridSum_refine_mul (τ υ : ℕ → ℝ≥0) (d : ℕ) (hd : 0 < d)
    (hυ : ∀ k, υ (d * k) = τ k) (A : ℕ → Ω → Z) (n : ℕ) (ω : Ω) :
    gridSum B υ (fun k => A (k / d)) (d * n) ω = gridSum B τ A n ω := by
  have h1 (m : ℕ) : gridSum B υ (fun k => A (k / d)) m ω =
      ∑ j ∈ Finset.range m, increment B (υ j) (υ (j + 1)) ω • A (j / d) ω :=
    Fin.sum_univ_eq_sum_range (fun j => increment B (υ j) (υ (j + 1)) ω • A (j / d) ω) m
  have h2 (m : ℕ) : gridSum B τ A m ω =
      ∑ j ∈ Finset.range m, increment B (τ j) (τ (j + 1)) ω • A j ω :=
    Fin.sum_univ_eq_sum_range (fun j => increment B (τ j) (τ (j + 1)) ω • A j ω) m
  rw [h1, h2]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    have he : (∑ j ∈ Finset.range d,
        increment B (υ (d * n + j)) (υ (d * n + j + 1)) ω • A ((d * n + j) / d) ω) =
        ∑ j ∈ Finset.range d,
          increment B (υ (d * n + j)) (υ (d * n + j + 1)) ω • A n ω := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hj', add_zero]
    rw [he, constant_block_sum]
    rw [show d * n + d = d * (n + 1) by ring, hυ n, hυ (n + 1)]

end PBGSO.BrownianGridIsometry
