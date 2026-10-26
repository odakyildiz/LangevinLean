import PBGSO.MomentumRates
import UnadjustedLangevin.ProductBrownian
import UnadjustedLangevin.GaussianInnovationVectors

/-! # Actual Gaussian/Brownian coupling for M-MFPO

Normalised Brownian increments on the half-step grid give exactly the
independent standard Gaussian innovations used by the proposed implementation.
Their L² radii and the noise-matching error are derived, with explicit spatial
dimension. Independence of coordinate grid paths is a visible hypothesis for
the joint standard-Gaussian law; it is not inferred from marginal Brownianity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace PBGSO.Methods

variable {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- A genuine standard-Gaussian vector from each half Brownian interval. -/
def momentumHalfNoise (W : I → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) Q) (h : ℝ) (n : ℕ) :
    Lp (EuclideanSpace ℝ I) 2 Q :=
  ULA.Hilbert.brownianEulerNoise Q W hW (h / 2) n

/-- Every half-step innovation has the exact square-root-dimension L² norm. -/
theorem momentumHalfNoise_norm (W : I → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) Q) (h : ℝ) (hh : 0 < h) (n : ℕ) :
    ‖momentumHalfNoise Q W hW h n‖ = Real.sqrt (Fintype.card I : ℝ) := by
  simpa only [NNReal.coe_one, mul_one] using ULA.gaussian_coordinates_Lp_norm Q
    (momentumHalfNoise Q W hW h n) 1
    (fun i => ULA.Hilbert.sourceEulerNoise_coordinateLaw Q W hW (h / 2) (by positivity) n i)

/-- The entire innovation sequence has the iid standard multivariate
Gaussian law. In particular both halves and all iterations are independent. -/
theorem momentumHalfNoise_pathLaw (W : I → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) Q) (h : ℝ) (hh : 0 < h)
    (hpaths : iIndepFun
      (fun i ω (n : ℕ) => W i ((n : ℝ≥0) * (h / 2).toNNReal) ω) Q) :
    Q.map (fun ω n => momentumHalfNoise Q W hW h n ω) =
      Measure.infinitePi (fun _ : ℕ => stdGaussian (EuclideanSpace ℝ I)) := by
  exact ULA.gaussianInnovations_pathLaw Q
    (fun n ω => momentumHalfNoise Q W hW h n ω)
    (fun n => (Lp.aestronglyMeasurable _).aemeasurable)
    (fun n i => ULA.Hilbert.sourceEulerNoise_coordinateLaw Q W hW (h / 2) (by positivity) n i)
    (ULA.Hilbert.sourceEulerNoise_independent Q W hW (h / 2) (by positivity) hpaths)

/-- The implementation's net momentum innovation is coupled to the sum of
the two actual normalised Brownian half increments. The local discrepancy is
explicitly O(h sqrt(h)); no noise-error premise remains. -/
theorem momentumBrownian_noise_bound (W : I → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 < h) (n : ℕ) :
    ‖Real.sqrt (1 - Real.exp (-γ * h)) •
        (Real.exp (-γ * h / 2) • momentumHalfNoise Q W hW h (2 * n) +
          momentumHalfNoise Q W hW h (2 * n + 1)) -
      Real.sqrt (γ * h) • (momentumHalfNoise Q W hW h (2 * n) +
        momentumHalfNoise Q W hW h (2 * n + 1))‖ ≤
      ((3 / 2 : ℝ) * γ * Real.sqrt γ * Real.sqrt (Fintype.card I : ℝ)) *
        h * Real.sqrt h := by
  exact momentum_noise_coupling_bound γ h (Real.sqrt (Fintype.card I : ℝ))
    hγ hh.le (Real.sqrt_nonneg _) _ _
    (momentumHalfNoise_norm Q W hW h hh _).le
    (momentumHalfNoise_norm Q W hW h hh _).le

/-- The comparison increment is the actual scaled Brownian increment over
the two adjacent half intervals, coordinate by coordinate almost surely. -/
theorem momentumHalfNoise_brownian_increment (W : I → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 < h) (n : ℕ) (i : I) :
    ∀ᵐ ω ∂Q,
      Real.sqrt (γ * h) * (momentumHalfNoise Q W hW h (2 * n) ω i +
        momentumHalfNoise Q W hW h (2 * n + 1) ω i) =
      Real.sqrt (2 * γ) *
        (W i (((2 * n + 2 : ℕ) : ℝ≥0) * (h / 2).toNNReal) ω -
          W i (((2 * n : ℕ) : ℝ≥0) * (h / 2).toNNReal) ω) := by
  have hs : Real.sqrt (h / 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hscale : Real.sqrt (γ * h) / Real.sqrt (h / 2) = Real.sqrt (2 * γ) := by
    rw [show γ * h = (2 * γ) * (h / 2) by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * γ), mul_div_cancel_right₀ _ hs]
  filter_upwards
    [ULA.Hilbert.sourceEulerNoise_normalized_coordinate Q W hW (h / 2) (by positivity)
      (2 * n) i,
     ULA.Hilbert.sourceEulerNoise_normalized_coordinate Q W hW (h / 2) (by positivity)
      (2 * n + 1) i] with ω hfirst hsecond
  change momentumHalfNoise Q W hW h (2 * n) ω i = _ at hfirst
  change momentumHalfNoise Q W hW h (2 * n + 1) ω i = _ at hsecond
  rw [hfirst, hsecond]
  unfold ULA.normalizedBrownianIncrement
  rw [Real.coe_toNNReal _ (by positivity : 0 ≤ h / 2)]
  simp only [show 2 * n + 1 + 1 = 2 * n + 2 by omega]
  rw [show Real.sqrt (γ * h) *
      ((W i (↑(2 * n + 1) * (h / 2).toNNReal) ω -
          W i (↑(2 * n) * (h / 2).toNNReal) ω) / Real.sqrt (h / 2) +
        (W i (↑(2 * n + 2) * (h / 2).toNNReal) ω -
          W i (↑(2 * n + 1) * (h / 2).toNNReal) ω) / Real.sqrt (h / 2)) =
      (Real.sqrt (γ * h) / Real.sqrt (h / 2)) *
        (W i (↑(2 * n + 2) * (h / 2).toNNReal) ω -
          W i (↑(2 * n) * (h / 2).toNNReal) ω) by ring]
  rw [hscale]

end PBGSO.Methods
