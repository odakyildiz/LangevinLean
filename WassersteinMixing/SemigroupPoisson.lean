import WassersteinMixing.ShiftedEnergy
import WassersteinMixing.MonotoneOperators
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Poisson correctors from a reversible contraction semigroup

The corrector is constructed from increasing partial sums of integrated
semigroup differences. No eigenbasis, compact resolvent, or additional
regularity of the potential is needed in this construction.
-/

noncomputable section
set_option linter.style.header false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace WassersteinMixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- The operator properties proved for the actual reversible Langevin process. -/
structure ReversibleSemigroup (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  op : ℝ → H →L[ℂ] H
  zero : op 0 = 1
  add : ∀ {s t}, 0 ≤ s → 0 ≤ t → op (s + t) = op s * op t
  selfAdjoint : ∀ {t}, 0 ≤ t → IsSelfAdjoint (op t)
  norm_le : ∀ {t}, 0 ≤ t → ∀ x, ‖op t x‖ ≤ ‖x‖
  continuous : ∀ x, ContinuousOn (fun t ↦ op t x) (Set.Ici 0)

namespace ReversibleSemigroup

variable (S : ReversibleSemigroup H)

private def innerLeft (x : H) : H →L[ℝ] ℂ :=
  RCLike.conjCLE.toContinuousLinearMap ∘L (innerSL ℂ x).restrictScalars ℝ

private theorem innerLeft_apply (x y : H) : innerLeft x y = inner ℂ y x := by
  exact inner_conj_symm (𝕜 := ℂ) y x

private theorem linear_intervalIntegrable {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] (L : H →L[ℝ] K) {f : ℝ → H} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t ↦ L (f t)) volume a b :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

theorem commute {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Commute (S.op s) (S.op t) := by
  change S.op s * S.op t = S.op t * S.op s
  rw [← S.add hs ht, ← S.add ht hs, add_comm]

theorem op_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ S.op t := by
  have hh : 0 ≤ t / 2 := by positivity
  have heq : S.op t = star (S.op (t / 2)) * S.op (t / 2) := by
    rw [(S.selfAdjoint hh).star_eq, ← S.add hh hh]
    congr 1
    ring
  rw [heq]
  exact star_mul_self_nonneg _

theorem op_le_one {t : ℝ} (ht : 0 ≤ t) : S.op t ≤ 1 := by
  apply ContinuousLinearMap.le_def.mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  refine ⟨(IsSelfAdjoint.one (H →L[ℂ] H)).sub
    (S.selfAdjoint ht), ?_⟩
  intro x
  change 0 ≤ RCLike.re (inner ℂ ((1 - S.op t) x) x)
  simp only [sub_apply, one_apply_eq_self,
    inner_sub_left, inner_self_eq_norm_sq_to_K, map_sub,
    pow_two, RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, mul_zero,
    sub_zero]
  have h := (RCLike.re_le_norm (inner ℂ (S.op t x) x)).trans
    ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (S.norm_le ht x) (norm_nonneg x)))
  nlinarith

theorem antitone : AntitoneOn S.op (Set.Ici 0) := by
  intro s hs t ht hst
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  have hc := (Commute.one_right (S.op s)).sub_right (S.commute hs hd)
  have hp := Commute.mul_nonneg (S.op_nonneg hs)
    (sub_nonneg.mpr (S.op_le_one hd)) hc
  have heq : S.op s * (1 - S.op (t - s)) = S.op s - S.op t := by
    rw [mul_sub, mul_one, ← S.add hs hd]
    congr 2
    ring
  rw [heq] at hp
  exact sub_nonneg.mp hp

theorem orbit_integrable (x : H) {h : ℝ} (hh : 0 ≤ h) :
    IntervalIntegrable (fun t ↦ S.op t x) volume 0 h := by
  apply ContinuousOn.intervalIntegrable
  exact (S.continuous x).mono (by simpa [Set.uIcc_of_le hh] using
    (show Set.Icc 0 h ⊆ Set.Ici 0 from fun _ ht ↦ ht.1))

/-- The integral on the right side of the discrete Poisson equation. -/
def defect (h : ℝ) (x : H) : H := ∫ t in 0..h, x - S.op t x

theorem defect_integrable (x : H) {h : ℝ} (hh : 0 ≤ h) :
    IntervalIntegrable (fun t ↦ x - S.op t x) volume 0 h :=
  intervalIntegrable_const.sub (S.orbit_integrable x hh)

theorem defect_norm_le (x : H) {h : ℝ} (hh : 0 ≤ h) :
    ‖S.defect h x‖ ≤ (2 * h) * ‖x‖ := by
  calc
    ‖S.defect h x‖ ≤ (2 * ‖x‖) * |h - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      have ht0 : 0 ≤ t := (show t ∈ Set.Ioc 0 h by
        simpa only [Set.uIoc_of_le hh] using ht).1.le
      exact (norm_sub_le _ _).trans (by linarith [S.norm_le ht0 x])
    _ = (2 * h) * ‖x‖ := by rw [sub_zero, abs_of_nonneg hh]; ring

/-- The integrated defect is a bounded complex-linear operator. -/
def defectOp (h : ℝ) (hh : 0 ≤ h) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := S.defect h
      map_add' := by
        intro x y
        simp only [defect, map_add]
        simp_rw [show ∀ t, x + y - (S.op t x + S.op t y) =
          (x - S.op t x) + (y - S.op t y) by intro t; abel]
        exact intervalIntegral.integral_add (S.defect_integrable x hh)
          (S.defect_integrable y hh)
      map_smul' := by
        intro c x
        simp only [defect, map_smul, RingHom.id_apply, ← smul_sub]
        exact intervalIntegral.integral_smul c _ }
    (2 * h) (fun x ↦ S.defect_norm_le x hh)

@[simp] theorem defectOp_apply (h : ℝ) (hh : 0 ≤ h) (x : H) :
    S.defectOp h hh x = S.defect h x := rfl

theorem defectOp_commute (h : ℝ) (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s) :
    Commute (S.op s) (S.defectOp h hh) := by
  ext x
  change S.op s (∫ t in 0..h, x - S.op t x) =
    ∫ t in 0..h, S.op s x - S.op t (S.op s x)
  rw [← (S.op s).intervalIntegral_comp_comm (S.defect_integrable x hh)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht0 : 0 ≤ t := (show t ∈ Set.Icc 0 h by
    simpa only [Set.uIcc_of_le hh] using ht).1
  simp only [map_sub]
  congr 1
  exact congrArg (fun T : H →L[ℂ] H ↦ T x) (S.commute hs ht0).eq

theorem defectOp_symmetric (h : ℝ) (hh : 0 ≤ h) :
    (S.defectOp h hh).IsSymmetric := by
  intro x y
  change inner ℂ (∫ t in 0..h, x - S.op t x) y =
    inner ℂ x (∫ t in 0..h, y - S.op t y)
  rw [← innerLeft_apply y (∫ t in 0..h, x - S.op t x)]
  rw [← (innerLeft y).intervalIntegral_comp_comm
      (S.defect_integrable x hh)]
  change (∫ t in 0..h, innerLeft y (x - S.op t x)) =
    (innerSL ℂ x) (∫ t in 0..h, y - S.op t y)
  rw [← (innerSL ℂ x).intervalIntegral_comp_comm (S.defect_integrable y hh)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht0 : 0 ≤ t := (show t ∈ Set.Icc 0 h by
    simpa only [Set.uIcc_of_le hh] using ht).1
  dsimp only
  rw [innerLeft_apply]
  change inner ℂ (x - S.op t x) y = inner ℂ x (y - S.op t y)
  rw [inner_sub_left, inner_sub_right]
  congr 1
  exact (S.selfAdjoint ht0).isSymmetric x y

/-- Every summand used in the corrector is self-adjoint. -/
theorem shiftedDefect_symmetric (h : ℝ) (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s) :
    (S.op s * S.defectOp h hh).IsSymmetric := by
  intro x y
  change inner ℂ (S.op s (S.defectOp h hh x)) y =
    inner ℂ x (S.op s (S.defectOp h hh y))
  have hs1 := (S.selfAdjoint hs).isSymmetric (S.defectOp h hh x) y
  change inner ℂ (S.op s (S.defectOp h hh x)) y =
    inner ℂ (S.defectOp h hh x) (S.op s y) at hs1
  have hs2 := S.defectOp_symmetric h hh x (S.op s y)
  change inner ℂ (S.defectOp h hh x) (S.op s y) =
    inner ℂ x (S.defectOp h hh (S.op s y)) at hs2
  rw [hs1, hs2]
  congr 1
  exact congrArg (fun T : H →L[ℂ] H ↦ T y) (S.defectOp_commute h hh hs).eq.symm

/-- Quadratic forms of the integrated summands are nonnegative and telescope
under the stepwise semigroup difference. -/
theorem shiftedDefect_bounds (h : ℝ) (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ S.op s * S.defectOp h hh ∧
      S.op s * S.defectOp h hh ≤ h • (S.op s - S.op (s + h)) := by
  have heval (x : H) :
      S.op s (S.defectOp h hh x) = ∫ t in 0..h, (S.op s - S.op (s + t)) x := by
    rw [defectOp_apply, defect, ← (S.op s).intervalIntegral_comp_comm
      (S.defect_integrable x hh)]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := (show t ∈ Set.Icc 0 h by
      simpa only [Set.uIcc_of_le hh] using ht).1
    simp only [map_sub, sub_apply, S.add hs ht0, ContinuousLinearMap.mul_apply]
  have hint (x : H) : IntervalIntegrable
      (fun t ↦ (S.op s - S.op (s + t)) x) volume 0 h := by
    apply (linear_intervalIntegrable ((S.op s).restrictScalars ℝ)
      (S.defect_integrable x hh)).congr
    intro t ht
    have ht0 : 0 ≤ t := (show t ∈ Set.Ioc 0 h by
      simpa only [Set.uIoc_of_le hh] using ht).1.le
    simp only [ContinuousLinearMap.coe_restrictScalars', map_sub, sub_apply,
      S.add hs ht0, ContinuousLinearMap.mul_apply]
  let L (x : H) := RCLike.reCLM.comp (innerLeft x)
  have hform (x : H) :
      RCLike.re (inner ℂ (S.op s (S.defectOp h hh x)) x) =
        ∫ t in 0..h, RCLike.re (inner ℂ ((S.op s - S.op (s + t)) x) x) := by
    rw [heval]
    have hi := (L x).intervalIntegral_comp_comm (hint x)
    simpa only [L, ContinuousLinearMap.comp_apply, innerLeft_apply,
      RCLike.reCLM_apply] using hi.symm
  constructor
  · apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    refine ⟨S.shiftedDefect_symmetric h hh hs, ?_⟩
    intro x
    change 0 ≤ RCLike.re (inner ℂ (S.op s (S.defectOp h hh x)) x)
    rw [hform]
    apply intervalIntegral.integral_nonneg hh
    intro t ht
    exact (ContinuousLinearMap.le_def.mp
      (S.antitone (a := s) (b := s + t) hs
        (show 0 ≤ s + t by linarith [ht.1])
        (show s ≤ s + t by linarith [ht.1]))).2 x
  · apply ContinuousLinearMap.le_def.mpr
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨?_, ?_⟩
    · exact ((IsSelfAdjoint.all h).smul
        ((S.selfAdjoint hs).sub (S.selfAdjoint (add_nonneg hs hh)))).sub
          (S.shiftedDefect_symmetric h hh hs).isSelfAdjoint
    · intro x
      change 0 ≤ inner ℝ
        ((h • (S.op s - S.op (s + h)) - S.op s * S.defectOp h hh) x) x
      simp only [sub_apply, smul_apply, inner_sub_left, real_inner_smul_left,
        mul_apply_eq_comp]
      rw [← inner_sub_left, ← sub_apply]
      change 0 ≤ h * RCLike.re (inner ℂ ((S.op s - S.op (s + h)) x) x) -
        RCLike.re (inner ℂ (S.op s (S.defectOp h hh x)) x)
      rw [hform]
      have hb : (∫ t in 0..h,
          RCLike.re (inner ℂ ((S.op s - S.op (s + t)) x) x)) ≤
          ∫ t in 0..h, RCLike.re (inner ℂ ((S.op s - S.op (s + h)) x) x) := by
        have hqi : IntervalIntegrable (fun t ↦
            RCLike.re (inner ℂ ((S.op s - S.op (s + t)) x) x)) volume 0 h := by
          have hL : IntervalIntegrable
              (fun t ↦ L x ((S.op s - S.op (s + t)) x)) volume 0 h :=
            ⟨(L x).integrable_comp (hint x).1, (L x).integrable_comp (hint x).2⟩
          simpa only [L, ContinuousLinearMap.comp_apply, innerLeft_apply,
            RCLike.reCLM_apply] using hL
        apply intervalIntegral.integral_mono_on hh hqi intervalIntegrable_const
        intro t ht
        have hp := (ContinuousLinearMap.le_def.mp
          (S.antitone (a := s + t) (b := s + h)
            (show s + t ∈ Set.Ici 0 from add_nonneg hs ht.1)
            (add_nonneg hs hh)
            (by simpa only [add_comm] using (add_le_add_left ht.2 s)))).2 x
        change 0 ≤ RCLike.re (inner ℂ
          ((S.op (s + t) - S.op (s + h)) x) x) at hp
        simp only [sub_apply, inner_sub_left, map_sub] at hp ⊢
        linarith
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hb
      linarith

/-- Finite partial sums of the actual semigroup Poisson construction. -/
def partialCorrector (h : ℝ) (hh : 0 ≤ h) (N : ℕ) : H →L[ℂ] H :=
  ∑ n ∈ Finset.range N, S.op (n * h) * S.defectOp h hh

theorem partialCorrector_succ (h : ℝ) (hh : 0 ≤ h) (N : ℕ) :
    S.partialCorrector h hh (N + 1) = S.partialCorrector h hh N +
      S.op (N * h) * S.defectOp h hh := by
  exact Finset.sum_range_succ _ N

theorem partialCorrector_nonneg (h : ℝ) (hh : 0 ≤ h) (N : ℕ) :
    0 ≤ S.partialCorrector h hh N := by
  apply Finset.sum_nonneg
  intro n _
  exact (S.shiftedDefect_bounds h hh (s := n * h) (by positivity)).1

theorem partialCorrector_mono (h : ℝ) (hh : 0 ≤ h) :
    Monotone (S.partialCorrector h hh) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [S.partialCorrector_succ h hh n]
  exact le_add_of_nonneg_right (S.shiftedDefect_bounds h hh (s := n * h)
    (by positivity)).1

/-- The upper estimate telescopes, independently of any spectral gap. -/
theorem partialCorrector_le_telescoping (h : ℝ) (hh : 0 ≤ h) (N : ℕ) :
    S.partialCorrector h hh N ≤ h • (1 - S.op (N * h)) := by
  induction N with
  | zero => simp [partialCorrector, S.zero]
  | succ n ih =>
    rw [S.partialCorrector_succ h hh n]
    have hb := add_le_add ih (S.shiftedDefect_bounds h hh
      (s := n * h) (by positivity)).2
    convert hb using 1 <;> simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    module

theorem partialCorrector_le (h : ℝ) (hh : 0 ≤ h) (N : ℕ) :
    S.partialCorrector h hh N ≤ h • (1 : H →L[ℂ] H) := by
  apply (S.partialCorrector_le_telescoping h hh N).trans
  exact smul_le_smul_of_nonneg_left
    (sub_le_self _ (S.op_nonneg (by positivity))) hh

/-- The corrector is the strong limit of its bounded increasing partial sums. -/
def corrector (h : ℝ) (hh : 0 ≤ h) : H →L[ℂ] H :=
  Classical.choose (exists_monotone_operator_limit (S.partialCorrector h hh) h hh
    (S.partialCorrector_mono h hh) (S.partialCorrector_nonneg h hh)
    (S.partialCorrector_le h hh))

theorem corrector_norm_le (h : ℝ) (hh : 0 ≤ h) : ‖S.corrector h hh‖ ≤ h :=
  (Classical.choose_spec (exists_monotone_operator_limit (S.partialCorrector h hh) h hh
    (S.partialCorrector_mono h hh) (S.partialCorrector_nonneg h hh)
    (S.partialCorrector_le h hh))).1

theorem partialCorrector_tendsto (h : ℝ) (hh : 0 ≤ h) (x : H) :
    Tendsto (fun N ↦ S.partialCorrector h hh N x) atTop (𝓝 (S.corrector h hh x)) :=
  (Classical.choose_spec (exists_monotone_operator_limit (S.partialCorrector h hh) h hh
    (S.partialCorrector_mono h hh) (S.partialCorrector_nonneg h hh)
    (S.partialCorrector_le h hh))).2 x

theorem corrector_order (h : ℝ) (hh : 0 ≤ h) :
    0 ≤ S.corrector h hh ∧ S.corrector h hh ≤ h • (1 : H →L[ℂ] H) :=
  strong_limit_order (S.partialCorrector h hh) (S.corrector h hh) h
    (S.partialCorrector_nonneg h hh) (S.partialCorrector_le h hh)
    (S.partialCorrector_tendsto h hh)

theorem partialCorrector_recursion (h : ℝ) (hh : 0 ≤ h) (N : ℕ) :
    S.partialCorrector h hh (N + 1) = S.defectOp h hh +
      S.op h * S.partialCorrector h hh N := by
  unfold partialCorrector
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, S.zero, one_mul]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [← mul_assoc, ← S.add hh (show 0 ≤ (n : ℝ) * h by positivity)]
  congr 2
  push_cast
  ring

/-- The integrated Poisson equation is proved by passage to the strong limit. -/
theorem corrector_poisson (h : ℝ) (hh : 0 ≤ h) (x : H) :
    S.corrector h hh x - S.op h (S.corrector h hh x) = S.defect h x := by
  have hlim := S.partialCorrector_tendsto h hh x
  have hsucc := hlim.comp (tendsto_add_atTop_nat 1)
  have heq : S.corrector h hh x = S.defectOp h hh x + S.op h (S.corrector h hh x) := by
    apply tendsto_nhds_unique hsucc
    have ht := (tendsto_const_nhds (x := S.defectOp h hh x)).add
      ((S.op h).continuous.tendsto (S.corrector h hh x) |>.comp hlim)
    convert ht using 1
    ext n
    exact congrArg (fun T : H →L[ℂ] H ↦ T x) (S.partialCorrector_recursion h hh n)
  change S.corrector h hh x - S.op h (S.corrector h hh x) = S.defectOp h hh x
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using heq)

theorem partialCorrector_commute (h : ℝ) (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s)
    (N : ℕ) : Commute (S.op s) (S.partialCorrector h hh N) := by
  unfold partialCorrector
  apply Commute.sum_right
  intro n _
  exact (S.commute hs (show 0 ≤ (n : ℝ) * h by positivity)).mul_right
    (S.defectOp_commute h hh hs)

/-- The constructed corrector commutes with the entire semigroup. -/
theorem corrector_commute (h : ℝ) (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s) :
    Commute (S.op s) (S.corrector h hh) := by
  ext x
  change S.op s (S.corrector h hh x) = S.corrector h hh (S.op s x)
  have hl := (S.op s).continuous.tendsto (S.corrector h hh x) |>.comp
    (S.partialCorrector_tendsto h hh x)
  have hr := S.partialCorrector_tendsto h hh (S.op s x)
  apply tendsto_nhds_unique hl
  convert hr using 1
  ext N
  exact congrArg (fun T : H →L[ℂ] H ↦ T x) (S.partialCorrector_commute h hh hs N).eq

/-- The paper's energy estimate for the corrector follows from its operator
norm and commutation, rather than being a hypothesis on a chosen function. -/
theorem corrector_energy_le (h : ℝ) (hh : 0 ≤ h) {s : ℝ} (hs : 0 ≤ s) (x : H) :
    inner ℝ (S.corrector h hh x)
      (S.corrector h hh x - S.op s (S.corrector h hh x)) ≤
      h ^ 2 * inner ℝ x (x - S.op s x) := by
  have hG := (ContinuousLinearMap.nonneg_iff_isPositive.mp (S.corrector_order h hh).1)
    |>.isSelfAdjoint
  have hc : Commute (S.corrector h hh) (1 - S.op s) :=
    (Commute.one_right _).sub_right (S.corrector_commute h hh hs).symm
  simpa only [sub_apply, one_apply_eq_self] using
    commuting_energy_bound (S.corrector h hh) (1 - S.op s) h hh hG
      (S.corrector_norm_le h hh) (sub_nonneg.mpr (S.op_le_one hs)) hc x

end ReversibleSemigroup
end WassersteinMixing
