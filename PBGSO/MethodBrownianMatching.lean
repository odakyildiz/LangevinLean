import PBGSO.ConstructedNumerics
import KineticLangevin.VectorSegmentEquations

/-! # The implementation reference innovations are the actual Brownian inputs
The two normalized half-grid innovations sum to the kinetic Brownian input.
The fourth HOL kernel equals its physical final-auxiliary Brownian input on
an arbitrary measure-preserving initial/noise source. These are actual L²
identities, not covariance or output-law compatibility assumptions.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace PBGSO.Methods

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  (Q : Measure Ω)

/-- The actual √2-scaled Brownian L² variable has its displayed coordinates. -/
theorem brownianLangevinNoise_coe
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q) (a t : ℝ) :
    ULA.brownianLangevinNoise Q W hW a t =ᵐ[Q]
      fun ω ↦ Real.sqrt 2 • (ULA.brownianCoordinates W (a + t).toNNReal ω -
        ULA.brownianCoordinates W a.toNNReal ω) := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt 2)
      (ULA.brownianCoordinatesRealLp Q W hW (a + t) - ULA.brownianCoordinatesRealLp Q W hW a),
    Lp.coeFn_sub (ULA.brownianCoordinatesRealLp Q W hW (a + t))
      (ULA.brownianCoordinatesRealLp Q W hW a),
    ULA.brownianCoordinatesLp_coe Q W hW (a + t).toNNReal,
    ULA.brownianCoordinatesLp_coe Q W hW a.toNNReal] with ω hs hd ht ha
  change (Real.sqrt 2 • (ULA.brownianCoordinatesRealLp Q W hW (a + t) -
    ULA.brownianCoordinatesRealLp Q W hW a)) ω = _
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hd]
  simp only [Pi.sub_apply, ULA.brownianCoordinatesRealLp]
  rw [ht, ha]

variable [IsProbabilityMeasure Q]

/-- The actual two half-grid innovations sum to the physical kinetic
Brownian increment, as equality of complete L² vectors. -/
theorem momentumHalfNoise_sum_brownian
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 < h) (k : ℕ) :
    Real.sqrt (γ * h) • (momentumHalfNoise Q W hW h (2 * k) +
      momentumHalfNoise Q W hW h (2 * k + 1)) =
      Real.sqrt γ • ULA.brownianLangevinNoise Q W hW ((k : ℝ) * h) h := by
  have ht0 : ((2 * k : ℕ) : ℝ≥0) * (h / 2).toNNReal = ((k : ℝ) * h).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ (by positivity : 0 ≤ h / 2),
      Real.coe_toNNReal _ (mul_nonneg (Nat.cast_nonneg k) hh.le)]
    push_cast
    ring
  have ht1 : ((2 * k + 2 : ℕ) : ℝ≥0) * (h / 2).toNNReal = ((k : ℝ) * h + h).toNNReal := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_natCast, Real.coe_toNNReal _ (by positivity : 0 ≤ h / 2),
      Real.coe_toNNReal _ (by positivity : 0 ≤ (k : ℝ) * h + h)]
    push_cast
    ring
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (Real.sqrt (γ * h))
      (momentumHalfNoise Q W hW h (2 * k) + momentumHalfNoise Q W hW h (2 * k + 1)),
    Lp.coeFn_add (momentumHalfNoise Q W hW h (2 * k)) (momentumHalfNoise Q W hW h (2 * k + 1)),
    Lp.coeFn_smul (Real.sqrt γ) (ULA.brownianLangevinNoise Q W hW ((k : ℝ) * h) h),
    brownianLangevinNoise_coe Q W hW ((k : ℝ) * h) h,
    ae_all_iff.mpr (fun i ↦ momentumHalfNoise_brownian_increment Q W hW γ h hγ hh k i)]
    with ω hs ha hr hb hcoord
  rw [hs, hr]
  simp only [Pi.smul_apply]
  rw [ha, hb]
  apply PiLp.ext
  intro i
  change Real.sqrt (γ * h) * (momentumHalfNoise Q W hW h (2 * k) ω i +
    momentumHalfNoise Q W hW h (2 * k + 1) ω i) =
    Real.sqrt γ * (Real.sqrt 2 * (W i (((k : ℝ) * h + h).toNNReal) ω -
      W i (((k : ℝ) * h).toNNReal) ω))
  rw [hcoord i, ht0, ht1, ← mul_assoc, ← Real.sqrt_mul hγ,
    mul_comm γ 2]

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
/-- The complete kinetic input has zero optimiser component and exactly
its actual physical sampler Brownian component. -/
theorem momentumGaussianIncrement_brownian
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 < h) (k : ℕ) :
    momentumGaussianIncrement (Θ := Θ) Q W hW γ h k =
      (0, Real.sqrt γ • ULA.brownianLangevinNoise Q W hW ((k : ℝ) * h) h) := by
  apply Prod.ext
  · change Real.sqrt (γ * h) • ((0 : Θ) + 0) = 0
    simp
  · exact momentumHalfNoise_sum_brownian Q W hW γ h hγ hh k

section HOL
variable [DecidableEq I]
  {f : Ω → ULA.CanonicalBrownian.VectorSample I}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability I))

/-- HOL's fourth innovation is exactly its physical Brownian increment on
the actual initial/noise source, with the same sample and scaling. -/
theorem higherOrderPullbackGaussianIncrement_brownian (α γ : ℝ) (hα : 0 ≤ α)
    (a h : ℝ≥0) :
    holPullbackVectorNoise I hf α γ a h 3 =
      Real.sqrt α • ULA.brownianLangevinNoise Q
        (canonicalPullbackCoordinate I hf) (canonicalPullbackCoordinate_isPreBrownian I hf)
        (a : ℝ) (h : ℝ) := by
  have hc : holVectorNoise I α γ a h 3 =ᵐ[ULA.CanonicalBrownian.vectorProbability I]
      fun ω ↦ Real.sqrt (2 * α) • WithLp.toLp 2 (fun i ↦
        ULA.CanonicalBrownian.coordinate i (a + h) ω - ULA.CanonicalBrownian.coordinate i a ω) := by
    rw [holVectorNoise_brownian]
    filter_upwards [Lp.coeFn_smul (Real.sqrt (2 * α))
        (KineticLangevin.BrownianConvolution.vectorBrownianIncrementLp I a h),
      KineticLangevin.BrownianConvolution.vectorBrownianIncrementLp_coe I a h] with ω hs hv
    rw [hs]
    simp only [Pi.smul_apply]
    rw [hv]
  have ht : ((a : ℝ) + (h : ℝ)).toNNReal = a + h := by
    apply NNReal.eq
    simp only [Real.coe_toNNReal _ (add_nonneg a.coe_nonneg h.coe_nonneg), NNReal.coe_add]
  have ha : (a : ℝ).toNNReal = a := by simp
  apply Lp.ext
  filter_upwards [lpPullback_coe hf (holVectorNoise I α γ a h 3),
    hf.quasiMeasurePreserving.ae_eq_comp hc,
    Lp.coeFn_smul (Real.sqrt α) (ULA.brownianLangevinNoise Q
      (canonicalPullbackCoordinate I hf) (canonicalPullbackCoordinate_isPreBrownian I hf) a h),
    brownianLangevinNoise_coe Q (canonicalPullbackCoordinate I hf)
      (canonicalPullbackCoordinate_isPreBrownian I hf) a h] with ω hp hc hs hb
  change (lpPullbackCLM hf (holVectorNoise I α γ a h 3)) ω = _
  simp only [Function.comp_apply] at hc
  rw [hp, hc, hs]
  simp only [Pi.smul_apply]
  rw [hb]
  apply PiLp.ext
  intro i
  change Real.sqrt (2 * α) *
      (ULA.CanonicalBrownian.coordinate i (a + h) (f ω) - ULA.CanonicalBrownian.coordinate i a (f ω)) =
    Real.sqrt α * (Real.sqrt 2 *
      (canonicalPullbackCoordinate I hf i (((a : ℝ) + (h : ℝ)).toNNReal) ω -
        canonicalPullbackCoordinate I hf i (a : ℝ).toNNReal ω))
  rw [ht, ha]
  change _ = Real.sqrt α * (Real.sqrt 2 *
    (ULA.CanonicalBrownian.coordinate i (a + h) (f ω) - ULA.CanonicalBrownian.coordinate i a (f ω)))
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  ring

end HOL

end PBGSO.Methods
