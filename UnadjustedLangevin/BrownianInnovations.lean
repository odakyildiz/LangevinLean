import UnadjustedLangevin.GaussianCoordinates
import Mathlib.Probability.Independence.InfinitePi

set_option linter.style.header false

/-! # Independent standard Gaussian innovations from Brownian coordinates

Each scalar Brownian coordinate has independent increments on the regular time
grid. Independence of the coordinate grid paths combines with this within-path
independence to give independence across every time-coordinate pair. All laws
and independence facts are proved from Brownian laws; no potential regularity
or stationary diffusion is involved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ULA

variable {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- The standard normalized increment of a scalar Brownian coordinate. -/
def normalizedBrownianIncrement (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  (B (((n + 1 : ℕ) : ℝ≥0) * h) ω - B ((n : ℝ≥0) * h) ω) /
    Real.sqrt (h : ℝ)

/-- Its distribution is standard Gaussian at every iteration. -/
theorem normalizedBrownianIncrement_hasLaw
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (h : ℝ≥0) (hh : 0 < h) (n : ℕ) :
    HasLaw (normalizedBrownianIncrement B h n) (gaussianReal 0 1) P := by
  have hv : nndist (((((n + 1 : ℕ) : ℝ≥0) * h) : ℝ≥0) : ℝ)
      ((((n : ℝ≥0) * h) : ℝ≥0) : ℝ) = h := by
    apply NNReal.eq
    simp only [coe_nndist, Real.dist_eq, NNReal.coe_mul, NNReal.coe_natCast,
      Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
    rw [show ((n : ℝ) + 1) * (h : ℝ) - (n : ℝ) * (h : ℝ) = (h : ℝ) by ring,
      abs_of_nonneg h.coe_nonneg]
  have hraw := hB.hasLaw_sub (((n + 1 : ℕ) : ℝ≥0) * h) ((n : ℝ≥0) * h)
  simp only [NNReal.val_eq_coe] at hraw
  rw [hv] at hraw
  have hn := gaussianReal_div_const hraw (Real.sqrt (h : ℝ))
  have hs : NNReal.mk (Real.sqrt (h : ℝ) ^ 2) (sq_nonneg _) = h := by
    apply NNReal.eq
    exact Real.sq_sqrt h.coe_nonneg
  rw [hs, div_self hh.ne', zero_div] at hn
  exact hn

/-- Square integrability follows from the actual standard Gaussian law. -/
theorem normalizedBrownianIncrement_memLp
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (h : ℝ≥0) (hh : 0 < h) (n : ℕ) :
    MemLp (normalizedBrownianIncrement B h n) 2 P :=
  (normalizedBrownianIncrement_hasLaw P B hB h hh n).memLp
    (memLp_id_gaussianReal (2 : ℝ≥0))

/-- The normalized scalar innovation has exactly unit second moment. -/
theorem normalizedBrownianIncrement_second_moment
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (h : ℝ≥0) (hh : 0 < h) (n : ℕ) :
    (∫ ω, normalizedBrownianIncrement B h n ω ^ 2 ∂P) = 1 := by
  exact (normalizedBrownianIncrement_hasLaw P B hB h hh n).integral_comp
    (f := fun x : ℝ ↦ x ^ 2) (by fun_prop) |>.trans (centered_gaussian_second_moment 1)

/-- Within one Brownian coordinate, the whole sequence of normalized grid
increments is independent. -/
theorem normalizedBrownianIncrement_independent
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (h : ℝ≥0) :
    iIndepFun (normalizedBrownianIncrement B h) P := by
  have ht : Monotone (fun n : ℕ ↦ (n : ℝ≥0) * h) := by
    intro a b hab
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) h.coe_nonneg
  exact (hB.hasIndepIncrements.nat ht).comp
    (fun _ x ↦ x / Real.sqrt (h : ℝ)) (by fun_prop)

/-- An a.e.-measurable version of the independence-of-independent-families
criterion. Countability of each row permits using measurable representatives
without strengthening any hypotheses on the original random variables. -/
theorem iIndepFun_uncurry_nat_of_aemeasurable
    (X : ι → ℕ → Ω → ℝ) (hX : ∀ i n, AEMeasurable (X i n) P)
    (hrows : iIndepFun (fun i ω n ↦ X i n ω) P)
    (hwithin : ∀ i, iIndepFun (X i) P) :
    iIndepFun (fun p : ι × ℕ ↦ X p.1 p.2) P := by
  have hp (i : ι) : AEMeasurable (fun ω n ↦ X i n ω) P :=
    aemeasurable_pi_iff.mpr (hX i)
  let G : ι → Ω → ℕ → ℝ := fun i ↦ (hp i).mk (fun ω n ↦ X i n ω)
  have hG (i : ι) : Measurable (G i) := (hp i).measurable_mk
  have heq (i : ι) : (fun ω n ↦ X i n ω) =ᵐ[P] G i := (hp i).ae_eq_mk
  have hr : iIndepFun G P := hrows.congr heq
  have hw (i : ι) : iIndepFun (fun n ω ↦ G i ω n) P :=
    (hwithin i).congr (fun n ↦ (heq i).fun_comp (fun w ↦ w n))
  have hall : iIndepFun (fun p : ι × ℕ ↦ fun ω ↦ G p.1 ω p.2) P :=
    iIndepFun_uncurry' (fun i n ↦ (measurable_pi_apply n).comp (hG i)) hr hw
  exact hall.congr (fun p ↦ ((heq p.1).fun_comp (fun w ↦ w p.2)).symm)

/-- Independence of the coordinate grid paths and Brownian independent
increments imply independence across all coordinate-time pairs. -/
theorem normalizedBrownianIncrements_independent
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (h : ℝ≥0) (hh : 0 < h)
    (hpaths : iIndepFun (fun i ω (n : ℕ) ↦ B i ((n : ℝ≥0) * h) ω) P) :
    iIndepFun (fun p : ι × ℕ ↦ normalizedBrownianIncrement (B p.1) h p.2) P := by
  have hrows : iIndepFun (fun i ω n ↦ normalizedBrownianIncrement (B i) h n ω) P :=
    hpaths.comp
      (fun _ w n ↦ (w (n + 1) - w n) / Real.sqrt (h : ℝ))
      (by intro i; exact measurable_pi_iff.mpr fun n ↦ by fun_prop)
  exact iIndepFun_uncurry_nat_of_aemeasurable P _
    (fun i n ↦ (normalizedBrownianIncrement_hasLaw P (B i) (hB i) h hh n).aemeasurable)
    hrows (fun i ↦ normalizedBrownianIncrement_independent P (B i) (hB i) h)

/-- Independence of the entire scalar coordinate processes implies the grid
path hypothesis; no measurability of an uncountable path-valued map is added. -/
theorem normalizedBrownianIncrements_independent_of_paths
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (h : ℝ≥0) (hh : 0 < h)
    (hpaths : iIndepFun (fun i ω t ↦ B i t ω) P) :
    iIndepFun (fun p : ι × ℕ ↦ normalizedBrownianIncrement (B p.1) h p.2) P := by
  apply normalizedBrownianIncrements_independent P B hB h hh
  exact hpaths.comp (fun _ w (n : ℕ) ↦ w ((n : ℝ≥0) * h))
    (by intro i; exact measurable_pi_iff.mpr fun n ↦ measurable_pi_apply _)

/-- The complete scalar innovation path has the canonical product law. -/
theorem normalizedBrownianIncrements_hasLaw [Countable ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P)
    (h : ℝ≥0) (hh : 0 < h)
    (hpaths : iIndepFun (fun i ω (n : ℕ) ↦ B i ((n : ℝ≥0) * h) ω) P) :
    HasLaw (fun ω (p : ι × ℕ) ↦ normalizedBrownianIncrement (B p.1) h p.2 ω)
      (Measure.infinitePi (fun _ : ι × ℕ ↦ gaussianReal 0 1)) P := by
  have hcoord (p : ι × ℕ) : HasLaw (normalizedBrownianIncrement (B p.1) h p.2)
      (gaussianReal 0 1) P := normalizedBrownianIncrement_hasLaw P _ (hB p.1) h hh p.2
  exact (normalizedBrownianIncrements_independent P B hB h hh hpaths).hasLaw_infinitePi
    hcoord (aemeasurable_pi_iff.mpr fun p ↦ (hcoord p).aemeasurable)

end ULA
