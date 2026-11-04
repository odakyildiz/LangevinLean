import WassersteinMixing.ActualMarkovInput
import WassersteinMixing.SemigroupEulerActual

/-! # The finite Euler map of the actual restarted state and raw future

The measurable pointwise recursion is identified with the square-integrable
Euler recursion, so independence and time-homogeneity of its actual inputs
can be used without assuming a Markov transition law.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped NNReal Topology

namespace WassersteinMixing.CanonicalSemigroup

/-- The deterministic Euler endpoint, as a map of its state and raw future. -/
def pointwiseEulerMap (P : Parameters) (V : E P.dimension → ℝ) (h : ℝ) (n : ℕ)
    (p : E P.dimension × (Fin P.dimension → ℝ≥0 → ℝ)) : E P.dimension :=
  ULA.additiveEulerChain (gradient V) h p.1
    (fun s ↦ Real.sqrt 2 • WithLp.toLp 2 (fun i ↦ p.2 i s.toNNReal)) n

/-- Every finite Euler endpoint depends measurably on the genuine input. -/
theorem pointwiseEulerMap_measurable (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (h : ℝ) (n : ℕ) :
    Measurable (pointwiseEulerMap P V h n) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    change Measurable (fun p ↦ pointwiseEulerMap P V h n p -
      h • gradient V (pointwiseEulerMap P V h n p) +
      (Real.sqrt 2 • WithLp.toLp 2 (fun i ↦ p.2 i (((n + 1 : ℕ) : ℝ) * h).toNNReal) -
        Real.sqrt 2 • WithLp.toLp 2 (fun i ↦ p.2 i ((n : ℝ) * h).toNNReal)))
    apply (ih.sub ((hV.gradientLipschitz.continuous.measurable.comp ih).const_smul h)).add
    have hnoise (s : ℝ) : Measurable (fun p : E P.dimension ×
        (Fin P.dimension → ℝ≥0 → ℝ) ↦
        Real.sqrt 2 • WithLp.toLp 2 (fun i ↦ p.2 i s.toNNReal)) := by
      have hm : Measurable (fun p : E P.dimension × (Fin P.dimension → ℝ≥0 → ℝ) ↦
          fun i ↦ p.2 i s.toNNReal) := by fun_prop
      exact ((WithLp.measurable_toLp 2 _).comp hm).const_smul (Real.sqrt 2)
    exact (hnoise _).sub (hnoise _)

/-- The future additive Brownian noise has exactly its raw coordinate-path
representative, simultaneously for each fixed nonnegative requested time. -/
theorem shiftedNoise_coe (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a : ℝ≥0) (s : ℝ) (hs : 0 ≤ s) :
    ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
      (brownian_preBrownian P V hV) a s =ᵐ[actualProbability P V]
      fun ω ↦ Real.sqrt 2 • WithLp.toLp 2 (fun i ↦ actualBrownianFuture P a ω i s.toNNReal) := by
  let := actualProbability_isProbability P V hV
  have htime : ((a : ℝ) + s).toNNReal = a + s.toNNReal := by
    ext
    simp only [Real.coe_toNNReal _ (add_nonneg a.coe_nonneg hs), NNReal.coe_add,
      Real.coe_toNNReal _ hs]
  unfold ULA.brownianLangevinNoise ULA.brownianCoordinatesRealLp
  rw [htime, Real.toNNReal_coe]
  filter_upwards [Lp.coeFn_smul (Real.sqrt 2)
      (ULA.brownianCoordinatesLp (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) (a + s.toNNReal) -
       ULA.brownianCoordinatesLp (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) a),
    Lp.coeFn_sub
      (ULA.brownianCoordinatesLp (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) (a + s.toNNReal))
      (ULA.brownianCoordinatesLp (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) a),
    ULA.brownianCoordinatesLp_coe (actualProbability P V) (brownian P)
      (brownian_preBrownian P V hV) (a + s.toNNReal),
    ULA.brownianCoordinatesLp_coe (actualProbability P V) (brownian P)
      (brownian_preBrownian P V hV) a] with ω hsm hsub h1 h0
  simp only [Pi.smul_apply, Pi.sub_apply] at hsm hsub
  rw [hsm, hsub, h1, h0]
  congr 1

/-- The actual shifted `L²` Euler endpoint has the deterministic finite-input
representative. No conditional transition is an assumption. -/
theorem shiftedEuler_coe (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (a : ℝ≥0) (h : ℝ) (hh : 0 ≤ h) (n : ℕ) :
    letI := actualProbability_isProbability P V hV
    ULA.additiveEulerChain
      (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz) h
      (state P V hV a)
      (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
        (brownian_preBrownian P V hV) a) n =ᵐ[actualProbability P V]
      fun ω ↦ pointwiseEulerMap P V h n (state P V hV a ω, actualBrownianFuture P a ω) := by
  let := actualProbability_isProbability P V hV
  let X := ULA.additiveEulerChain
    (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz) h
    (state P V hV a)
    (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
      (brownian_preBrownian P V hV) a)
  induction n with
  | zero => exact EventuallyEq.rfl
  | succ n ih =>
    have hN := shiftedNoise_coe P V hV a (((n + 1 : ℕ) : ℝ) * h) (mul_nonneg (by positivity) hh)
    have hn := shiftedNoise_coe P V hV a ((n : ℝ) * h) (mul_nonneg (by positivity) hh)
    have he : X (n + 1) = X n - h • ULA.lpDrift (actualProbability P V)
        (gradient V) hV.gradientLipschitz (X n) +
        (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
          (brownian_preBrownian P V hV) a (((n + 1 : ℕ) : ℝ) * h) -
         ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
          (brownian_preBrownian P V hV) a ((n : ℝ) * h)) := rfl
    change X (n + 1) =ᵐ[_] _
    rw [he]
    filter_upwards [ih, ULA.lpDrift_coe (actualProbability P V) (gradient V)
        hV.gradientLipschitz (X n), hN, hn,
      Lp.coeFn_add (X n - h • ULA.lpDrift (actualProbability P V) (gradient V)
        hV.gradientLipschitz (X n))
        (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
          (brownian_preBrownian P V hV) a (((n + 1 : ℕ) : ℝ) * h) -
         ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
          (brownian_preBrownian P V hV) a ((n : ℝ) * h)),
      Lp.coeFn_sub (X n) (h • ULA.lpDrift (actualProbability P V) (gradient V)
        hV.gradientLipschitz (X n)),
      Lp.coeFn_smul h (ULA.lpDrift (actualProbability P V) (gradient V) hV.gradientLipschitz (X n)),
      Lp.coeFn_sub
        (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
          (brownian_preBrownian P V hV) a (((n + 1 : ℕ) : ℝ) * h))
        (ULA.brownianLangevinNoise (actualProbability P V) (brownian P)
          (brownian_preBrownian P V hV) a ((n : ℝ) * h))]
      with ω hi hd hN hn hadd hsub hsm hnoise
    change X n ω = _ at hi
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at hadd hsub hsm hnoise
    rw [hadd, hsub, hsm, hnoise, hN, hn, hd, hi]
    rfl

end WassersteinMixing.CanonicalSemigroup
