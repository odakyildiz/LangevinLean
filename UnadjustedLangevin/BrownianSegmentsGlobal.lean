import UnadjustedLangevin.BrownianReference
import UnadjustedLangevin.EulerLimit
import UnadjustedLangevin.LangevinUniqueness

set_option linter.style.header false

/-! # Constructed Brownian segments equal the global integral solution

Only the deterministic integral equation, the algebraic Brownian increment
cocycle, and finite-horizon uniqueness enter this file. No stationarity or
independence assertion is assumed in these identities.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace ULA
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (P : Measure Ω)

/-- The additive Brownian input has the exact algebraic increment cocycle. -/
theorem brownianLangevinNoise_increment
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P) (a t : ℝ) :
    brownianLangevinNoise P W hW 0 (a + t) - brownianLangevinNoise P W hW 0 a =
      brownianLangevinNoise P W hW a t := by
  unfold brownianLangevinNoise
  simp only [zero_add]
  module

variable [IsProbabilityMeasure P]

/-- Shifting a global integral solution by time `a` gives the actual segment
integral equation driven by the Brownian increments starting at `a`. -/
theorem lp_brownian_integral_shift
    (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hY : Continuous Y)
    (T : ℝ)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) +
        brownianLangevinNoise P W hW 0 t)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) (hah : a + h ≤ T) :
    ∀ t ∈ Icc 0 h, Y (a + t) - Y a =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y (a + s))) +
        brownianLangevinNoise P W hW a t := by
  intro t ht
  have hai : a ∈ Icc 0 T := ⟨ha, by linarith⟩
  have hati : a + t ∈ Icc 0 T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hinc := langevin_integral_increment (lpDrift P (gradient U) hLip) L
    (lpDrift_lipschitz P (gradient U) hLip) initial
    (brownianLangevinNoise P W hW 0) Y hY T hYe a (a + t) hai hati
  have hi : (∫ s in a..a + t, lpDrift P (gradient U) hLip (Y s)) =
      ∫ s in 0..t, lpDrift P (gradient U) hLip (Y (a + s)) := by
    simpa only [add_zero] using (intervalIntegral.integral_comp_add_left
      (f := fun s ↦ lpDrift P (gradient U) hLip (Y s)) (a := 0) (b := t) a).symm
  rw [hi, brownianLangevinNoise_increment] at hinc
  exact hinc

namespace Hilbert

/-- An actual segment selected by Picard equals the restriction of any global
solution with the matching knot, independently of the choice used in existence. -/
theorem brownianSegmentFrom_eq_global
    (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (initial initialAt : Lp (EuclideanSpace ℝ ι) 2 P)
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hY : Continuous Y)
    (T : ℝ)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) +
        brownianLangevinNoise P W hW 0 t)
    (h : ℝ) (hh : 0 ≤ h) (n : ℕ)
    (hstart : initialAt = Y ((n : ℝ) * h))
    (hend : ((n : ℝ) + 1) * h ≤ T) :
    EqOn (brownianSegmentFrom P U L hLip W hW h hh n initialAt)
      (fun t ↦ Y ((n : ℝ) * h + t)) (Icc 0 h) := by
  have hs := brownianSegmentFrom_spec P U L hLip W hW h hh n initialAt
  have he := lp_brownian_integral_shift P U L hLip initial W hW Y hY T hYe
    ((n : ℝ) * h) h (mul_nonneg (Nat.cast_nonneg _) hh) hh
    (by nlinarith)
  apply lp_langevin_integral_unique P U L hLip initialAt
    (brownianLangevinNoise P W hW ((n : ℝ) * h)) _ _ hs.1
    (hY.comp (continuous_const.add continuous_id)) h hh hs.2.2.1
  intro t ht
  rw [hstart]
  exact he t ht

/-- Every recursively constructed knot agrees with the global solution at its
absolute grid time, as soon as that time lies within the global horizon. -/
theorem brownianKnots_eq_global
    (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) +
        brownianLangevinNoise P W hW 0 t)
    (h : ℝ) (hh : 0 ≤ h) (n : ℕ) (hn : (n : ℝ) * h ≤ T) :
    brownianKnots P U L hLip W hW h hh initial n = Y ((n : ℝ) * h) := by
  have hY0 : Y 0 = initial := by
    have he := hYe 0 ⟨le_rfl, hT⟩
    simpa only [intervalIntegral.integral_same, neg_zero, brownianLangevinNoise_zero,
      add_zero, sub_eq_zero] using he
  induction n with
  | zero => simpa only [brownianKnots, Nat.cast_zero, zero_mul] using hY0.symm
  | succ n ih =>
    have hprev : (n : ℝ) * h ≤ T := by
      push_cast at hn
      nlinarith
    have hstart := ih hprev
    have he := brownianSegmentFrom_eq_global P U L hLip initial
      (brownianKnots P U L hLip W hW h hh initial n) W hW Y hY T hYe h hh n hstart
      (by exact_mod_cast hn)
    have heh := he (x := h) ⟨hh, le_rfl⟩
    change brownianSegmentFrom P U L hLip W hW h hh n
      (brownianKnots P U L hLip W hW h hh initial n) h = _
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using heh

/-- The actual reference segment at local time `t` is the global Langevin
solution at absolute time `n*h+t`. No law or stationarity premise occurs. -/
theorem brownianSegments_eq_global
    (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (Y : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, lpDrift P (gradient U) hLip (Y s)) +
        brownianLangevinNoise P W hW 0 t)
    (h : ℝ) (hh : 0 ≤ h) (n : ℕ) (hend : ((n : ℝ) + 1) * h ≤ T) :
    EqOn (brownianSegments P U L hLip W hW h hh initial n)
      (fun t ↦ Y ((n : ℝ) * h + t)) (Icc 0 h) := by
  have hkn := brownianKnots_eq_global P U L hLip initial W hW Y hY T hT hYe h hh n
    (by nlinarith)
  exact brownianSegmentFrom_eq_global P U L hLip initial
    (brownianKnots P U L hLip W hW h hh initial n) W hW Y hY T hYe h hh n hkn hend

end Hilbert
end ULA
