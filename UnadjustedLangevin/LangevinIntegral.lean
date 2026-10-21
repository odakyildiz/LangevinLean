import Mathlib.Analysis.ODE.ExistUnique
import UnadjustedLangevin.LpDrift

set_option linter.style.header false

/-! # Constructing an additive-noise Langevin integral solution

For a globally Lipschitz drift and a continuous additive input, Picard iteration
constructs the solution in the Banach space itself. In particular the Banach
space may be L², so existence of the integral equation is proved rather than
postulated. This file does not establish Gibbs invariance of that solution.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped NNReal
namespace ULA

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Picard constructs the continuous solution of `Y = x + B - ∫g(Y)` on a
short interval. The noise need only be continuous in the Banach norm. The
condition `L*h ≤ 1/2` is a local construction condition, not an assumption on
the final Langevin diffusion; longer intervals require concatenation. -/
theorem exists_langevin_integral_small
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B : ℝ → H) (hB : Continuous B) (hB0 : B 0 = 0)
    (h : ℝ) (hh : 0 ≤ h) (hsmall : (L : ℝ) * h ≤ 1 / 2) :
    ∃ Y : ℝ → H, Continuous Y ∧ Y 0 = x ∧
      ∀ t ∈ Icc 0 h,
        Y t - x = -(∫ s in 0..t, g (Y s)) + B t := by
  have hbound := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) h)).image hB).isBounded.exists_norm_le
  obtain ⟨C, hC⟩ := hbound
  let C' : ℝ := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  have hBC (t : ℝ) (ht : t ∈ Icc 0 h) : ‖B t‖ ≤ C' :=
    (hC _ (mem_image_of_mem B ht)).trans (le_max_left _ _)
  let G : ℝ := ‖g x‖ + (L : ℝ) * C'
  have hG : 0 ≤ G := by dsimp [G]; positivity
  let a : ℝ≥0 := ⟨2 * h * G, by positivity⟩
  let M : ℝ≥0 := ⟨G + (L : ℝ) * a, by positivity⟩
  let f : ℝ → H → H := fun t z ↦ -g (z + B t)
  let t₀ : Icc 0 h := ⟨0, by simp [hh]⟩
  have hpicard : IsPicardLindelof f t₀ x a 0 M L := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro z hz w hw
      dsimp [f]
      simpa only [dist_neg_neg, dist_add_right] using hLip.dist_le_mul (z + B t) (w + B t)
    · intro z hz
      exact (hLip.continuous.comp (continuous_const.add hB)).neg.continuousOn
    · intro t ht z hz
      have hz' : ‖z - x‖ ≤ (a : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
      have hnorm : ‖z + B t - x‖ ≤ (a : ℝ) + C' := by
        have hid : z + B t - x = (z - x) + B t := by abel
        rw [hid]
        exact (norm_add_le _ _).trans (add_le_add hz' (hBC t ht))
      have hg : ‖g (z + B t) - g x‖ ≤ (L : ℝ) * ((a : ℝ) + C') := by
        exact (hLip.norm_sub_le (z + B t) x).trans
          (mul_le_mul_of_nonneg_left hnorm L.coe_nonneg)
      change ‖-g (z + B t)‖ ≤ (M : ℝ)
      rw [norm_neg]
      have hu : ‖g (z + B t)‖ ≤ ‖g x‖ + ‖g (z + B t) - g x‖ := by
        simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub (g x) (g (z + B t))
      change ‖g (z + B t)‖ ≤ G + (L : ℝ) * (a : ℝ)
      dsimp [G]
      nlinarith
    · change (M : ℝ) * max (h - 0) (0 - 0) ≤ (a : ℝ) - 0
      rw [sub_zero, sub_self, max_eq_left hh, sub_zero]
      change (G + (L : ℝ) * (2 * h * G)) * h ≤ 2 * h * G
      have hm := mul_le_mul_of_nonneg_right hsmall
        (by positivity : 0 ≤ 2 * h * G)
      nlinarith
  have hx : x ∈ closedBall x (0 : ℝ≥0) := by simp
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpicard hx
  let Z : ℝ → H := α.compProj
  have hZ : Continuous Z := α.continuous_compProj
  have hZeq (t : ℝ) (ht : t ∈ Icc 0 h) :
      Z t = x + ∫ s in 0..t, f s (Z s) := by
    change α.compProj t = x + ∫ s in 0..t, f s (α.compProj s)
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht, ODE.FunSpace.next_apply]
    rfl
  have hZ0 : Z 0 = x := by simpa using hZeq 0 ⟨le_rfl, hh⟩
  refine ⟨fun t ↦ Z t + B t, hZ.add hB, by simp [hZ0, hB0], ?_⟩
  intro t ht
  change (Z t + B t) - x = -(∫ s in 0..t, g (Z s + B s)) + B t
  rw [hZeq t ht]
  dsimp [f]
  rw [intervalIntegral.integral_neg]
  abel


omit [CompleteSpace H] in
/-- Two consecutive solutions splice into one continuous integral solution.
This is the finite-horizon extension step, with no new drift hypotheses. -/
lemma splice_langevin_integral
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y Z : ℝ → H) (hY : Continuous Y) (hZ : Continuous Z)
    (a b : ℝ) (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hY0 : Y 0 = x) (hZ0 : Z 0 = Y a)
    (hYe : ∀ t ∈ Icc 0 a, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (hZe : ∀ t ∈ Icc 0 b, Z t - Y a =
      -(∫ s in 0..t, g (Z s)) + (B (a + t) - B a)) :
    ∃ S : ℝ → H, Continuous S ∧ S 0 = x ∧
      ∀ t ∈ Icc 0 (a + b), S t - x = -(∫ s in 0..t, g (S s)) + B t := by
  classical
  let S : ℝ → H := fun t ↦ if t ≤ a then Y t else Z (t - a)
  have hSl (t : ℝ) (ht : t ≤ a) : S t = Y t := by simp [S, ht]
  have hSr (t : ℝ) (ht : a ≤ t) : S t = Z (t - a) := by
    by_cases hl : t ≤ a
    · have he : t = a := le_antisymm hl ht
      simp [S, he, hZ0]
    · simp [S, hl]
  have hS : Continuous S := hY.if_le (hZ.comp (continuous_id.sub continuous_const))
    continuous_id continuous_const (fun t ht ↦ by simp only [ht, sub_self, hZ0])
  have hSlint (t : ℝ) (ht : t ∈ Icc 0 a) :
      (∫ s in 0..t, g (S s)) = ∫ s in 0..t, g (Y s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change g (S s) = g (Y s)
    rw [hSl s (hs.2.trans ht.2)]
  refine ⟨S, hS, by rw [hSl 0 ha, hY0], ?_⟩
  intro t ht
  by_cases hta : t ≤ a
  · rw [hSl t hta, hSlint t ⟨ht.1, hta⟩]
    exact hYe t ⟨ht.1, hta⟩
  · have hat : a ≤ t := le_of_lt (lt_of_not_ge hta)
    have hz := hZe (t - a) ⟨sub_nonneg.mpr hat, by linarith [ht.2]⟩
    have hy := hYe a ⟨ha, le_rfl⟩
    have hright : (∫ s in a..t, g (S s)) = ∫ s in 0..(t - a), g (Z s) := by
      calc
        _ = ∫ s in a..t, g (Z (s - a)) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hat] at hs
          change g (S s) = g (Z (s - a))
          rw [hSr s hs.1]
        _ = _ := by
          simpa only [sub_self] using
            (intervalIntegral.integral_comp_sub_right (f := fun s ↦ g (Z s))
              (a := a) (b := t) a)
    have hint : (∫ s in 0..t, g (S s)) =
        (∫ s in 0..a, g (Y s)) + ∫ s in 0..(t - a), g (Z s) := by
      calc
        _ = (∫ s in 0..a, g (S s)) + ∫ s in a..t, g (S s) :=
          (intervalIntegral.integral_add_adjacent_intervals
            (show IntervalIntegrable (fun s ↦ g (S s)) volume 0 a from
              (hLip.continuous.comp hS).intervalIntegrable 0 a)
            (show IntervalIntegrable (fun s ↦ g (S s)) volume a t from
              (hLip.continuous.comp hS).intervalIntegrable a t)).symm
        _ = _ := by rw [hSlint a ⟨ha, le_rfl⟩, hright]
    have hyval : Y a = x - (∫ s in 0..a, g (Y s)) + B a := by
      rw [sub_eq_iff_eq_add] at hy
      rw [hy]
      abel
    have hzval : Z (t - a) = Y a - (∫ s in 0..(t - a), g (Z s)) + B t - B a := by
      rw [show a + (t - a) = t by ring, sub_eq_iff_eq_add] at hz
      rw [hz]
      abel
    rw [hSr t hat, hzval, hyval, hint]
    abel

/-- A globally Lipschitz drift admits an additive-noise integral solution on
any finite nonnegative horizon. The proof constructs short Picard segments and
splices them; no small-step restriction or reference process is assumed. -/
theorem exists_langevin_integral
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B : ℝ → H) (hB : Continuous B) (hB0 : B 0 = 0)
    (h : ℝ) (_hh : 0 ≤ h) :
    ∃ Y : ℝ → H, Continuous Y ∧ Y 0 = x ∧
      ∀ t ∈ Icc 0 h, Y t - x = -(∫ s in 0..t, g (Y s)) + B t := by
  let δ : ℝ := 1 / (2 * ((L : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsmall : (L : ℝ) * δ ≤ 1 / 2 := by
    dsimp [δ]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * ((L : ℝ) + 1))).mpr
    linarith
  have hex (n : ℕ) : ∃ Y : ℝ → H, Continuous Y ∧ Y 0 = x ∧
      ∀ t ∈ Icc 0 ((n : ℝ) * δ),
        Y t - x = -(∫ s in 0..t, g (Y s)) + B t := by
    induction n with
    | zero =>
        refine ⟨fun _ ↦ x, continuous_const, rfl, ?_⟩
        intro t ht
        simp only [Nat.cast_zero, zero_mul] at ht
        have ht0 : t = 0 := le_antisymm ht.2 ht.1
        simp [ht0, hB0]
    | succ n ih =>
        obtain ⟨Y, hY, hY0, hYe⟩ := ih
        let a : ℝ := (n : ℝ) * δ
        have ha : 0 ≤ a := by dsimp [a]; positivity
        obtain ⟨Z, hZ, hZ0, hZe⟩ := exists_langevin_integral_small g L hLip (Y a)
          (fun t ↦ B (a + t) - B a)
          ((hB.comp (continuous_const.add continuous_id)).sub continuous_const)
          (by simp) δ hδ.le hδsmall
        have hs := splice_langevin_integral g L hLip x B Y Z hY hZ a δ ha hδ.le hY0 hZ0 hYe hZe
        convert hs using 1
        simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, a]
  obtain ⟨n, hn⟩ := exists_nat_ge (h / δ)
  obtain ⟨Y, hY, hY0, hYe⟩ := hex n
  refine ⟨Y, hY, hY0, fun t ht ↦ hYe t ⟨ht.1, ht.2.trans ?_⟩⟩
  exact (div_le_iff₀ hδ).mp hn

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The actual gradient has an L² integral solution from its Lipschitz
hypothesis and a continuous L² additive noise path. No reference solution or
integral identity is assumed in this construction. -/
theorem exists_lp_langevin_integral_small
    (U : K → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp K 2 P) (B : ℝ → Lp K 2 P)
    (hB : Continuous B) (hB0 : B 0 = 0)
    (h : ℝ) (hh : 0 ≤ h) (hsmall : (L : ℝ) * h ≤ 1 / 2) :
    ∃ Y : ℝ → Lp K 2 P, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 h, Y t - initial =
        -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) + B t :=
  exists_langevin_integral_small (lpDrift P (gradient U) hLip) L
    (lpDrift_lipschitz P (gradient U) hLip) initial B hB hB0 h hh hsmall

/-- Finite-horizon existence of the actual L² Langevin integral equation from
only Lipschitz gradient and continuous additive noise, with no step restriction. -/
theorem exists_lp_langevin_integral
    (U : K → ℝ) (L : ℝ≥0) (hLip : LipschitzWith L (gradient U))
    (initial : Lp K 2 P) (B : ℝ → Lp K 2 P)
    (hB : Continuous B) (hB0 : B 0 = 0) (h : ℝ) (hh : 0 ≤ h) :
    ∃ Y : ℝ → Lp K 2 P, Continuous Y ∧ Y 0 = initial ∧
      ∀ t ∈ Icc 0 h, Y t - initial =
        -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) + B t :=
  exists_langevin_integral (lpDrift P (gradient U) hLip) L
    (lpDrift_lipschitz P (gradient U) hLip) initial B hB hB0 h hh


end ULA
