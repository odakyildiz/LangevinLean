import IPLA.Dynamics
import IPLA.Foundations
import IPLA.Scaling
import IPLA.Transport
import IPLA.Concentration
import IPLA.ULAAdapter
import UnadjustedLangevin.GaussianULA
import IPLA.Generator
import IPLA.Degenerate
import UnadjustedLangevin.GeneratorDirichlet
import UnadjustedLangevin.FokkerPlanck

set_option linter.style.header false

/-! # Theorem 1 from the original joint-potential assumptions

The shared Gaussian ULA theorem is applied directly to the lifted IPLA chain.
ULA supplies the initial transport bound, constructs the Langevin reference,
and proves Gibbs stationarity; none of those proofs is repeated here.
The IPLA concentration theorem proves the sharp parameter-marginal bound.
Neither result is supplied as an additional hypothesis here.
The observation `y` is fixed. Both strong convexity and gradient smoothness
are assumptions on the same joint potential `U y`, whose coordinates are `(θ,x)`.
No separate convexity or smoothness of a coordinate block is assumed.
The complete standalone version is `IPLA/Standalone.lean`.
-/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace IPLA

/-- For fixed observations `y`, write `U y (pair θ x) = -log p_θ(x,y)`.
The general-dimension counterpart of equation (34), with independent
parameter dimension `dθ` and latent dimension `dx`, for the actual Gaussian
IPLA recursion and its defined Gibbs target. Every hypothesis
is displayed here or is one of the Gaussian-law and independence fields of
`GaussianInnovations`, whose definition is included in the standalone file.
Normalization, all finite transport moments, a stationary Langevin reference,
and the equilibrium parameter concentration are derived in the proof. -/
private theorem nonempty_dimension_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N dθ dx : ℕ) [Nonempty (Fin dθ ⊕ (Fin N × Fin dx))] (hN : 0 < N)
    {Data : Type*} (U : Data → Joint dθ dx → ℝ) (y : Data)
    (m γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ (U y)) (hsc : StrongConvexOn Set.univ m (U y))
    (hLip : LipschitzWith L (gradient (U y)))
    (hm : 0 < m)
    (hγ : 0 < γ) (hsmall : γ ≤ 2 / (m + (L : ℝ)))
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hMaximizer : IsMarginalMaximizer (U y) θStar)
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise)
    (k : ℕ) :
    Real.sqrt (∫ z, ‖parameterCLM z - θStar‖ ^ 2
      ∂(laws P (U y) γ L hdiff hLip initial noise k)) ≤
      Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m)) +
        (1 - m * γ) ^ k * ULA.wasserstein2Real (P.map initial) (gibbsTarget (U y)) +
        (33 / 20 : ℝ) * ((L : ℝ) / m) *
          Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have : IsProbabilityMeasure (@gibbsTarget N dθ dx (U y)) :=
    gibbsTarget_isProbability hN (U y) m hm hdiff hsc
  have hfinite := ULA.Hilbert.gaussianULA_initial_transport_finite P
    (@potential N dθ dx (U y)) ((N : ℝ) * m) (mul_pos hn hm)
    (potential_differentiable hdiff) (potential_strongConvex hsc) initial
  have hs : γ / (N : ℝ) ≤
      2 / ((N : ℝ) * m + (((N : ℝ≥0) * L : ℝ≥0) : ℝ)) := by
    simpa using (scaled_step_iff N hN m (L : ℝ) γ).mpr hsmall
  have htransport := ULA.Hilbert.dalalyan_of_gaussian_innovations P
    (@potential N dθ dx (U y))
    ((N : ℝ) * m) (γ / N) ((N : ℝ≥0) * L) (mul_pos hn hm)
    (potential_differentiable hdiff) (potential_strongConvex hsc)
    (potential_gradient_lipschitz hdiff hLip) (div_pos hγ hn) hs
    initial noise hGaussian.coordinateLaw hGaussian.independent
    hGaussian.independentInitial k
  change ULA.wasserstein2Real (laws P (U y) γ L hdiff hLip initial noise k)
    (ULA.gibbsMeasure (potential (U y))) ≤ _ at htransport
  have houtput := ULA.Hilbert.dalalyan_output_finite (@potential N dθ dx (U y))
    ((N : ℝ) * m) (γ / N) ((N : ℝ≥0) * L) (mul_pos hn hm)
    (potential_differentiable hdiff) (potential_strongConvex hsc)
    (potential_gradient_lipschitz hdiff hLip) (div_pos hγ hn)
    (P.map initial) hfinite k
  have hlaw := laws_eq_ulaLawStep P (U y) γ L hdiff hLip initial noise hGaussian k
  rw [← hlaw] at houtput
  rw [← gibbsTarget_eq_gibbsMeasure (U y)] at htransport houtput
  have hfactor : (N : ℝ) * m * (γ / N) = m * γ := by field_simp
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, NNReal.coe_mul,
    NNReal.coe_natCast, hfactor] at htransport
  rw [scaled_bias_eq N dθ dx hN m (L : ℝ) γ hγ.le] at htransport
  have hconcentration := gibbsTarget_parameter_concentration hN (U y) m hm hdiff hsc
    θStar hMaximizer
  have hprojected := projectedRMSReal_le_wasserstein2Real_add
    (@parameterCLM N dθ dx) norm_parameterCLM_le_one θStar
    (Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m))) (Real.sqrt_nonneg _)
    houtput hconcentration
  have hmoment := projectedRMS_ne_top (@parameterCLM N dθ dx) norm_parameterCLM_le_one
    θStar _ houtput hconcentration
  rw [projectedRMSReal_eq_sqrt_integral _ _ _ hmoment] at hprojected
  linarith


/-- Strongly convex IPLA for independent, arbitrary parameter and latent
dimensions. All stationary-reference and concentration inputs are derived.
The zero-dimensional cases are included without extra assumptions. -/
theorem theorem1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N dθ dx : ℕ) (hN : 0 < N)
    {Data : Type*} (U : Data → Joint dθ dx → ℝ) (y : Data)
    (m γ : ℝ) (L : ℝ≥0)
    (hdiff : Differentiable ℝ (U y)) (hsc : StrongConvexOn Set.univ m (U y))
    (hLip : LipschitzWith L (gradient (U y)))
    (hm : 0 < m)
    (hγ : 0 < γ) (hsmall : γ ≤ 2 / (m + (L : ℝ)))
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hMaximizer : IsMarginalMaximizer (U y) θStar)
    (initial : Lp (State N dθ dx) 2 P) (noise : ℕ → Lp (State N dθ dx) 2 P)
    (hGaussian : GaussianInnovations P initial noise)
    (k : ℕ) :
    Real.sqrt (∫ z, ‖parameterCLM z - θStar‖ ^ 2
      ∂(laws P (U y) γ L hdiff hLip initial noise k)) ≤
      Real.sqrt (2 * (dθ : ℝ) / ((N : ℝ) * m)) +
        (1 - m * γ) ^ k * ULA.wasserstein2Real (P.map initial) (gibbsTarget (U y)) +
        (33 / 20 : ℝ) * ((L : ℝ) / m) *
          Real.sqrt ((dx : ℝ) + (dθ : ℝ) / (N : ℝ)) * Real.sqrt γ := by
  classical
  by_cases hindex : Nonempty (Fin dθ ⊕ (Fin N × Fin dx))
  · let : Nonempty (Fin dθ ⊕ (Fin N × Fin dx)) := hindex
    exact nonempty_dimension_bound P N dθ dx hN U y m γ L hdiff hsc hLip hm
      hγ hsmall θStar hMaximizer initial noise hGaussian k
  · have hθ : dθ = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hindex ⟨Sum.inl ⟨0, hp⟩⟩)
    have hx : dx = 0 := Nat.eq_zero_of_not_pos
      (fun hp ↦ hindex ⟨Sum.inr (⟨0, hN⟩, ⟨0, hp⟩)⟩)
    subst dθ
    subst dx
    have : IsProbabilityMeasure (@gibbsTarget N 0 0 (U y)) :=
      gibbsTarget_isProbability hN (U y) m hm hdiff hsc
    simpa only [Nat.cast_zero] using zero_dimensions_bound (P.map initial) (gibbsTarget (U y))
      (laws P (U y) γ L hdiff hLip initial noise k) m γ L θStar k

end IPLA
