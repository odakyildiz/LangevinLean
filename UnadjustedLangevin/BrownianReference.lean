import UnadjustedLangevin.HilbertDalalyan
import UnadjustedLangevin.BrownianLangevin
import UnadjustedLangevin.StationaryMoments

set_option linter.style.header false

/-! # An actual Brownian Langevin reference, conditional on Gibbs invariance

The integral equation, continuity, matching Euler noise, and both moment bounds
are constructed or proved here. The only remaining process-law input is the
explicit assertion that the constructed segments have the Gibbs law at every
time. This file does not claim to prove that invariance assertion.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace ULA.Hilbert
open ULA

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The canonical choice of the constructed solution over the `n`th time
segment, starting from the supplied knot. -/
def brownianSegmentFrom (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (h : ℝ) (hh : 0 ≤ h) (n : ℕ) (initial : Lp (EuclideanSpace ℝ ι) 2 P) :
    ℝ → Lp (EuclideanSpace ℝ ι) 2 P :=
  Classical.choose (exists_lp_langevin_integral_of_brownian P U L hLip initial W hW
    ((n : ℝ) * h) h (mul_nonneg (Nat.cast_nonneg n) hh) hh)

/-- The properties of the actual integral solution used to define a segment. -/
theorem brownianSegmentFrom_spec (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (h : ℝ) (hh : 0 ≤ h) (n : ℕ) (initial : Lp (EuclideanSpace ℝ ι) 2 P) :
    Continuous (brownianSegmentFrom P U L hLip W hW h hh n initial) ∧
      brownianSegmentFrom P U L hLip W hW h hh n initial 0 = initial ∧
      (∀ t ∈ Icc 0 h,
        brownianSegmentFrom P U L hLip W hW h hh n initial t - initial =
          -(∫ s in 0..t, lpDrift P (gradient U) hLip
            (brownianSegmentFrom P U L hLip W hW h hh n initial s)) +
            brownianLangevinNoise P W hW ((n : ℝ) * h) t) ∧
      (∀ t ∈ Icc 0 h, ‖brownianLangevinNoise P W hW ((n : ℝ) * h) t‖ =
        Real.sqrt (2 * (Fintype.card ι : ℝ)) * Real.sqrt t) :=
  Classical.choose_spec (exists_lp_langevin_integral_of_brownian P U L hLip initial W hW
    ((n : ℝ) * h) h (mul_nonneg (Nat.cast_nonneg n) hh) hh)

/-- Successive knots are the endpoints of the constructed integral solutions. -/
def brownianKnots (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (h : ℝ) (hh : 0 ≤ h) (initial : Lp (EuclideanSpace ℝ ι) 2 P) :
    ℕ → Lp (EuclideanSpace ℝ ι) 2 P
  | 0 => initial
  | n + 1 => brownianSegmentFrom P U L hLip W hW h hh n
      (brownianKnots U L hLip W hW h hh initial n) h

/-- The reference segments use the recursively constructed endpoints. -/
def brownianSegments (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (h : ℝ) (hh : 0 ≤ h) (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (n : ℕ) : ℝ → Lp (EuclideanSpace ℝ ι) 2 P :=
  brownianSegmentFrom P U L hLip W hW h hh n
    (brownianKnots P U L hLip W hW h hh initial n)

/-- Each segment starts exactly at its recursively constructed knot. -/
@[simp] theorem brownianSegments_start (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (h : ℝ) (hh : 0 ≤ h) (initial : Lp (EuclideanSpace ℝ ι) 2 P) (n : ℕ) :
    brownianSegments P U L hLip W hW h hh initial n 0 =
      brownianKnots P U L hLip W hW h hh initial n :=
  (brownianSegmentFrom_spec P U L hLip W hW h hh n _).2.1

/-- The constructed process starts from precisely the prescribed random
variable, including its chosen joint realization with the Euler initialization. -/
@[simp] theorem brownianSegments_initial (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient U))
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (h : ℝ) (hh : 0 ≤ h) (initial : Lp (EuclideanSpace ℝ ι) 2 P) :
    brownianSegments P U L hLip W hW h hh initial 0 0 = initial := by
  rw [brownianSegments_start]
  rfl

/-- Normalize each actual Brownian endpoint to the Euler innovation. -/
def brownianEulerNoise (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (h : ℝ) (n : ℕ) :
    Lp (EuclideanSpace ℝ ι) 2 P :=
  (Real.sqrt (2 * h))⁻¹ • brownianLangevinNoise P W hW ((n : ℝ) * h) h

omit [IsProbabilityMeasure P] in
/-- The normalized endpoint matches the same additive noise used by the
integral equation exactly, without a supplied endpoint hypothesis. -/
theorem brownianEulerNoise_endpoint (W : ι → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) P) (h : ℝ) (hh : 0 < h) (n : ℕ) :
    brownianLangevinNoise P W hW ((n : ℝ) * h) h =
      Real.sqrt (2 * h) • brownianEulerNoise P W hW h n := by
  have hs : Real.sqrt (2 * h) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  simp only [brownianEulerNoise, smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- All analytic and noise fields of `L2Reference` follow from the constructed
Brownian integral solutions and the sharp Gibbs score theorem. The all-time
Gibbs-law premise is the single remaining process-law obligation. -/
def brownianReference (U : EuclideanSpace ℝ ι → ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (hZ : gibbsPartition U ≠ ⊤)
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (h : ℝ) (hh : 0 < h) (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (hstationary : ∀ n t, t ∈ Icc 0 h →
      P.map (brownianSegments P U L hLip W hW h hh.le initial n t) = gibbsMeasure U) :
    L2Reference P (Fintype.card ι) U h L hLip
      (brownianEulerNoise P W hW h) (gibbsMeasure U) where
  segment := brownianSegments P U L hLip W hW h hh.le initial
  increment := fun n ↦ brownianLangevinNoise P W hW ((n : ℝ) * h)
  continuous n := (brownianSegmentFrom_spec P U L hLip W hW h hh.le n _).1
  join n := by
    change brownianSegments P U L hLip W hW h hh.le initial n h =
      brownianSegmentFrom P U L hLip W hW h hh.le (n + 1)
        (brownianKnots P U L hLip W hW h hh.le initial (n + 1)) 0
    rw [(brownianSegmentFrom_spec P U L hLip W hW h hh.le (n + 1) _).2.1]
    rfl
  noiseEndpoint := brownianEulerNoise_endpoint P W hW h hh
  stationary n := hstationary n 0 ⟨le_rfl, hh.le⟩
  integralEquation n t ht := by
    change brownianSegmentFrom P U L hLip W hW h hh.le n _ t -
      brownianSegmentFrom P U L hLip W hW h hh.le n _ 0 = _
    rw [(brownianSegmentFrom_spec P U L hLip W hW h hh.le n _).2.1]
    exact (brownianSegmentFrom_spec P U L hLip W hW h hh.le n _).2.2.1 t ht
  scoreBound n t ht := by
    simpa using lpDrift_norm_le_of_gibbs_law P U L hdiff hLip hZ
      (brownianSegments P U L hLip W hW h hh.le initial n t) (hstationary n t ht)
  noiseBound n t ht :=
    (brownianLangevinNoise_norm P W hW ((n : ℝ) * h) t
      (mul_nonneg (Nat.cast_nonneg n) hh.le) ht.1).le

/-- The strong-convexity version has no separate normalization or moment
hypothesis: only Gibbs invariance of the actual constructed segments remains. -/
def brownianReference_of_strongConvex
    (U : EuclideanSpace ℝ ι → ℝ) (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn Set.univ m U)
    (hLip : LipschitzWith L (gradient U))
    (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) P)
    (h : ℝ) (hh : 0 < h) (initial : Lp (EuclideanSpace ℝ ι) 2 P)
    (hstationary : ∀ n t, t ∈ Icc 0 h →
      P.map (brownianSegments P U L hLip W hW h hh.le initial n t) = gibbsMeasure U) :
    L2Reference P (Fintype.card ι) U h L hLip
      (brownianEulerNoise P W hW h) (gibbsMeasure U) :=
  brownianReference P U L hdiff hLip (gibbsPartition_ne_top U m hm hdiff hsc)
    W hW h hh initial hstationary

end ULA.Hilbert
