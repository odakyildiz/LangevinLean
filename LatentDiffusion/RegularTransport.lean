import LatentDiffusion.SourceResults
import PBGSO.ProductTransport
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Determinant
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false

/-!
# Regular displacement transport for the latent free energy

The extra hypotheses below are classical transport regularity data: a
pushforward by a measurable interpolation, positive densities, positive
eigenvalues of its Jacobian, the density/Jacobian change of variables formula,
and integrable logarithms and quadratic costs.  No convexity, first order
transport inequality, log Sobolev inequality, or Talagrand inequality is included
in these data.  The Jacobian may have arbitrary eigenvectors depending on the
latent variable, so this does not restrict to independent coordinates.

The transport distance used throughout is the infimum over actual probability
couplings defined in `ULA.Coupling`.  In particular, finite transport costs are
proved before converting any extended nonnegative real to a real number.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace LatentDiffusion.RegularTransport

/-- Determinant of `I + s (DT-I)` in a positive spectral representation of
the Jacobian of a smooth Brenier map.  Its eigenvectors need not be fixed. -/
def spectralJacobian {d : ℕ} (eigenvalue : Fin d → ℝ) (s : ℝ) : ℝ :=
  ∏ i, ((1 - s) + s * eigenvalue i)

theorem spectralJacobian_pos {d : ℕ} (eigenvalue : Fin d → ℝ)
    (hpos : ∀ i, 0 < eigenvalue i) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < spectralJacobian eigenvalue s := by
  apply Finset.prod_pos
  intro i _
  by_cases h : s = 0
  · simp [h]
  · have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm h)
    exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs.2) (mul_pos hsp (hpos i))

@[simp] theorem spectralJacobian_zero {d : ℕ} (eigenvalue : Fin d → ℝ) :
    spectralJacobian eigenvalue 0 = 1 := by simp [spectralJacobian]

@[simp] theorem spectralJacobian_one {d : ℕ} (eigenvalue : Fin d → ℝ) :
    spectralJacobian eigenvalue 1 = ∏ i, eigenvalue i := by simp [spectralJacobian]

/-- The full dimensional log determinant inequality follows by applying the
concavity of log separately to the positive eigenvalues and summing. -/
theorem log_spectralJacobian_ge {d : ℕ} (eigenvalue : Fin d → ℝ)
    (hpos : ∀ i, 0 < eigenvalue i) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    s * Real.log (spectralJacobian eigenvalue 1) ≤
      Real.log (spectralJacobian eigenvalue s) := by
  have he (i : Fin d) :
      s * Real.log (eigenvalue i) ≤ Real.log ((1 - s) + s * eigenvalue i) := by
    have h := (StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi).2
      (show (1 : ℝ) ∈ Ioi 0 by norm_num) (hpos i)
      (sub_nonneg.mpr hs.2) hs.1 (by ring : (1 - s) + s = 1)
    simpa [smul_eq_mul] using h
  rw [spectralJacobian_one, Real.log_prod (fun i _ ↦ (hpos i).ne')]
  unfold spectralJacobian
  rw [Real.log_prod (fun i _ ↦ ?_)]
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ he i
  · have h := spectralJacobian_pos (d := 1) (fun _ ↦ eigenvalue i) (fun _ ↦ hpos i) s hs
    simpa [spectralJacobian] using h.ne'

section Displacement

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

/-- The actual linear displacement of a latent variable. -/
def interpolate (T : Z → Z) (s : ℝ) (z : Z) : Z := (1 - s) • z + s • T z

@[simp] theorem interpolate_zero (T : Z → Z) : interpolate T 0 = id := by
  funext z
  simp [interpolate]

@[simp] theorem interpolate_one (T : Z → Z) : interpolate T 1 = T := by
  funext z
  simp [interpolate]

@[fun_prop] theorem interpolate_measurable (T : Z → Z) (hT : Measurable T) (s : ℝ) :
    Measurable (interpolate T s) := by unfold interpolate; fun_prop

/-- Regular change of variables for a smooth positive-Jacobian displacement.
`density_law` makes every density an actual probability density.  The final
field is the local mass conservation equation, rather than an entropy bound.
The eigenvalues describe the Jacobian of the endpoint map, without any
restriction on its eigenvectors. -/
structure RegularDisplacement (ν μ : Measure Z) (d : ℕ) where
  transport : Z → Z
  measurable_transport : Measurable transport
  density : ℝ → Z → ℝ
  measurable_density : ∀ s ∈ Icc (0 : ℝ) 1, Measurable (density s)
  positive_density : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, 0 < density s z
  density_law : ∀ s ∈ Icc (0 : ℝ) 1,
    μ.map (interpolate transport s) = ν.withDensity (fun z ↦ ENNReal.ofReal (density s z))
  eigenvalue : Z → Fin d → ℝ
  positive_eigenvalue : ∀ z i, 0 < eigenvalue z i
  jacobian : Z → Z →L[ℝ] Z
  derivative_transport : ∀ z, HasFDerivAt transport (jacobian z) z
  spectral_basis : Z → OrthonormalBasis (Fin d) ℝ Z
  jacobian_eigenvector : ∀ z i,
    jacobian z (spectral_basis z i) = eigenvalue z i • spectral_basis z i
  density_jacobian : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z,
    density s (interpolate transport s z) =
      density 0 z / spectralJacobian (eigenvalue z) s
  integrable_log : ∀ s ∈ Icc (0 : ℝ) 1,
    Integrable (fun z ↦ Real.log (density s (interpolate transport s z))) μ

namespace RegularDisplacement

variable {ν μ : Measure Z} {d : ℕ} (D : RegularDisplacement ν μ d)

/-- The spectral Jacobian in the change of variables data is the determinant
of the actual derivative. This checks the link between the certificate and DT. -/
theorem det_jacobian (z : Z) :
    (D.jacobian z).toLinearMap.det = spectralJacobian (D.eigenvalue z) 1 := by
  rw [← LinearMap.det_toMatrix (D.spectral_basis z).toBasis]
  have hmatrix : LinearMap.toMatrix (D.spectral_basis z).toBasis
      (D.spectral_basis z).toBasis (D.jacobian z).toLinearMap =
      Matrix.diagonal (D.eigenvalue z) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [ContinuousLinearMap.coe_coe, OrthonormalBasis.coe_toBasis,
      D.jacobian_eigenvector, map_smul]
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  rw [hmatrix, Matrix.det_diagonal, spectralJacobian_one]

/-- The trace of the actual derivative is the sum of its certified positive
eigenvalues. This allows ordinary divergence integration by parts. -/
theorem trace_jacobian (z : Z) :
    LinearMap.trace ℝ Z (D.jacobian z).toLinearMap = ∑ i, D.eigenvalue z i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (D.spectral_basis z).toBasis]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  simp [D.jacobian_eigenvector]

/-- Actual law of the displacement interpolation. -/
def law (s : ℝ) : Measure Z := μ.map (interpolate D.transport s)

@[simp] theorem law_zero : D.law 0 = μ := by simp [law]

@[simp] theorem law_one : D.law 1 = μ.map D.transport := by simp [law]

instance law_probability [IsProbabilityMeasure μ] (s : ℝ) :
    IsProbabilityMeasure (D.law s) :=
  (Measure.isProbabilityMeasure_map_iff
    (interpolate_measurable _ D.measurable_transport s).aemeasurable).mpr inferInstance

/-- Pointwise entropy comparison is derived from log determinant concavity
and the local change of variables formula. -/
theorem log_density_interpolate_le (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (z : Z) :
    Real.log (D.density s (interpolate D.transport s z)) ≤
      (1 - s) * Real.log (D.density 0 z) +
        s * Real.log (D.density 1 (D.transport z)) := by
  have hj := spectralJacobian_pos (D.eigenvalue z) (D.positive_eigenvalue z) s hs
  have hj1 := spectralJacobian_pos (D.eigenvalue z) (D.positive_eigenvalue z) 1
    (by constructor <;> norm_num)
  have h0 := D.positive_density 0 (by constructor <;> norm_num) z
  have hmass := D.density_jacobian s hs z
  have hmass1 := D.density_jacobian 1 (by constructor <;> norm_num) z
  simp only [interpolate_one] at hmass1
  rw [hmass, hmass1, Real.log_div h0.ne' hj.ne', Real.log_div h0.ne' hj1.ne']
  have hdet := log_spectralJacobian_ge (D.eigenvalue z) (D.positive_eigenvalue z) s hs
  nlinarith

/-- Boltzmann entropy of the actual density and actual interpolated law. -/
def entropy (s : ℝ) : ℝ := ∫ z, Real.log (D.density s z) ∂D.law s

theorem entropy_eq_pullback (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    D.entropy s = ∫ z, Real.log (D.density s (interpolate D.transport s z)) ∂μ := by
  exact integral_map (interpolate_measurable _ D.measurable_transport s).aemeasurable
    ((Real.measurable_log.comp (D.measurable_density s hs)).aestronglyMeasurable)

/-- Displacement convexity of actual entropy for an arbitrary latent dimension
and an arbitrary correlated initial density. -/
theorem entropy_displacement_convex (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    D.entropy s ≤ (1 - s) * D.entropy 0 + s * D.entropy 1 := by
  rw [D.entropy_eq_pullback s hs,
    D.entropy_eq_pullback 0 (by constructor <;> norm_num),
    D.entropy_eq_pullback 1 (by constructor <;> norm_num)]
  simp only [interpolate_zero, id_eq, interpolate_one]
  have h0 := D.integrable_log 0 (by constructor <;> norm_num)
  have h1 := D.integrable_log 1 (by constructor <;> norm_num)
  simp only [interpolate_zero, id_eq, interpolate_one] at h0 h1
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h0.const_mul _) (h1.const_mul _)]
  exact integral_mono (D.integrable_log s hs) ((h0.const_mul _).add (h1.const_mul _))
    (D.log_density_interpolate_le s hs)

end RegularDisplacement

end Displacement

section ProductEnergy

variable {P Z : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {ν μ : Measure Z} [IsProbabilityMeasure μ] {d : ℕ}

/-- Parameter interpolation uses the Euclidean part of the product metric. -/
def parameterInterpolate (p₀ p₁ : P) (s : ℝ) : P := (1 - s) • p₀ + s • p₁

/-- The actual density free energy of one datum. -/
def freeEnergy (D : RegularDisplacement ν μ d) (U : P → Z → ℝ)
    (p₀ p₁ : P) (s : ℝ) : ℝ :=
  D.entropy s + ∫ z, U (parameterInterpolate p₀ p₁ s) z ∂D.law s

/-- The elementary L² square identity with all finite-cost information retained. -/
theorem secondCost_sq_eq_integral {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Q : Measure Ω) (X : Ω → H) (hX : MemLp X 2 Q) :
    (eLpNorm X 2 Q).toReal ^ 2 = ∫ ω, ‖X ω‖ ^ 2 ∂Q := by
  have h := ProximalLangevin.lp_norm_sq_eq_integral Q (hX.toLp X)
  rw [Lp.norm_toLp] at h
  exact h.trans (integral_congr_ae (hX.coeFn_toLp.fun_comp fun v ↦ ‖v‖ ^ 2))

/-- Strong convexity of the actual potential expectation.  The norm of the
joint parameter/latent state is Euclidean, rather than the product max norm. -/
theorem potential_displacement_strongConvex
    (D : RegularDisplacement ν μ d) (U : P → Z → ℝ) (p₀ p₁ : P) (rho : ℝ)
    (hU : StrongConvexOn univ rho (fun w : PBGSO.ProductTransport.Joint P Z ↦ U w.fst w.snd))
    (hmeas : ∀ p, Measurable (U p))
    (hint : ∀ s ∈ Icc (0 : ℝ) 1,
      Integrable (fun z ↦ U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z)) μ)
    (hcost : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ z, U (parameterInterpolate p₀ p₁ s) z ∂D.law s) ≤
      (1 - s) * (∫ z, U p₀ z ∂μ) + s * (∫ z, U p₁ (D.transport z) ∂μ) -
        rho / 2 * s * (1 - s) *
          (‖p₀ - p₁‖ ^ 2 + (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal ^ 2) := by
  have hpoint (z : Z) :
      U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z) ≤
        (1 - s) * U p₀ z + s * U p₁ (D.transport z) -
          rho / 2 * s * (1 - s) * (‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2) := by
    have h := hU.2 (mem_univ (PBGSO.ProductTransport.embed p₀ z))
      (mem_univ (PBGSO.ProductTransport.embed p₁ (D.transport z)))
      (sub_nonneg.mpr hs.2) hs.1 (by ring : (1 - s) + s = 1)
    change U ((1 - s) • p₀ + s • p₁) ((1 - s) • z + s • D.transport z) ≤
      (1 - s) * U p₀ z + s * U p₁ (D.transport z) -
        (1 - s) * s * (rho / 2 *
          ‖PBGSO.ProductTransport.embed p₀ z -
            PBGSO.ProductTransport.embed p₁ (D.transport z)‖ ^ 2) at h
    rw [WithLp.prod_norm_sq_eq_of_L2] at h
    change U ((1 - s) • p₀ + s • p₁) ((1 - s) • z + s • D.transport z) ≤
      (1 - s) * U p₀ z + s * U p₁ (D.transport z) -
        (1 - s) * s * (rho / 2 * (‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2)) at h
    convert h using 1 <;> first | rfl | ring
  have h0 := hint 0 (by constructor <;> norm_num)
  have h1 := hint 1 (by constructor <;> norm_num)
  simp only [parameterInterpolate, sub_zero, one_smul, zero_smul, add_zero,
    interpolate_zero, id_eq, sub_self, zero_add, interpolate_one] at h0 h1
  have hc := hcost.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hsum : Integrable (fun z ↦ ‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2) μ :=
    (integrable_const _).add hc
  have hrhs : Integrable (fun z ↦ (1 - s) * U p₀ z + s * U p₁ (D.transport z) -
      rho / 2 * s * (1 - s) * (‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2)) μ :=
    ((h0.const_mul _).add (h1.const_mul _)).sub (hsum.const_mul _)
  have hbound := integral_mono (hint s hs) hrhs hpoint
  have hmap : (∫ z, U (parameterInterpolate p₀ p₁ s) z ∂D.law s) =
      ∫ z, U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z) ∂μ :=
    integral_map (interpolate_measurable _ D.measurable_transport s).aemeasurable
      (hmeas _).aestronglyMeasurable
  rw [hmap]
  convert hbound using 1
  symm
  change (∫ z, (((fun z : Z ↦ (1 - s) * U p₀ z) +
    (fun z : Z ↦ s * U p₁ (D.transport z)) -
    (fun z : Z ↦ rho / 2 * s * (1 - s) *
      (‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2))) : Z → ℝ) z ∂μ) = _
  rw [integral_sub' ((h0.const_mul (1 - s)).add (h1.const_mul s))
      (hsum.const_mul (rho / 2 * s * (1 - s))),
    integral_add' (h0.const_mul (1 - s)) (h1.const_mul s), integral_const_mul,
    integral_const_mul, integral_const_mul, integral_add (integrable_const _) hc,
    integral_const, ← secondCost_sq_eq_integral μ _ hcost]
  simp

/-- Strong displacement convexity is proved from the paper's strong convexity
and explicit change-of-variables regularity.  It is not a premise of the result. -/
theorem freeEnergy_displacement_strongConvex_cost
    (D : RegularDisplacement ν μ d) (U : P → Z → ℝ) (p₀ p₁ : P) (rho : ℝ)
    (hU : StrongConvexOn univ rho (fun w : PBGSO.ProductTransport.Joint P Z ↦ U w.fst w.snd))
    (hmeas : ∀ p, Measurable (U p))
    (hint : ∀ s ∈ Icc (0 : ℝ) 1,
      Integrable (fun z ↦ U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z)) μ)
    (hcost : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    freeEnergy D U p₀ p₁ s ≤
      (1 - s) * freeEnergy D U p₀ p₁ 0 + s * freeEnergy D U p₀ p₁ 1 -
        rho / 2 * s * (1 - s) *
          (‖p₀ - p₁‖ ^ 2 + (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal ^ 2) := by
  have he := D.entropy_displacement_convex s hs
  have hp := potential_displacement_strongConvex D U p₀ p₁ rho hU hmeas hint hcost s hs
  have hmap : (∫ z, U p₁ z ∂D.law 1) = ∫ z, U p₁ (D.transport z) ∂μ := by
    rw [D.law_one]
    exact integral_map D.measurable_transport.aemeasurable (hmeas p₁).aestronglyMeasurable
  simp only [freeEnergy, parameterInterpolate, sub_zero, one_smul, zero_smul, add_zero,
    sub_self, zero_add, D.law_zero, hmap]
  unfold parameterInterpolate at hp
  linarith

/-- The genuine latent W₂ cost is bounded by the chosen displacement cost. -/
theorem wasserstein_sq_le_displacement_cost
    (D : RegularDisplacement ν μ d) (hcost : MemLp (fun z ↦ z - D.transport z) 2 μ) :
    ULA.wasserstein2Real μ (D.law 1) ^ 2 ≤
      (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal ^ 2 := by
  have h := ULA.wasserstein2_le_random_cost_real μ id D.transport measurable_id
    D.measurable_transport hcost
  simp only [Measure.map_id, ← D.law_one] at h
  exact (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr h

/-- Strong convexity on the actual optimizer/Wasserstein product metric.  The
conclusion uses a genuine coupling infimum even when the supplied regular map
is not assumed optimal. -/
theorem freeEnergy_displacement_strongConvex
    (D : RegularDisplacement ν μ d) (U : P → Z → ℝ) (p₀ p₁ : P) (rho : ℝ)
    (hrho : 0 ≤ rho)
    (hU : StrongConvexOn univ rho (fun w : PBGSO.ProductTransport.Joint P Z ↦ U w.fst w.snd))
    (hmeas : ∀ p, Measurable (U p))
    (hint : ∀ s ∈ Icc (0 : ℝ) 1,
      Integrable (fun z ↦ U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z)) μ)
    (hcost : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    freeEnergy D U p₀ p₁ s ≤
      (1 - s) * freeEnergy D U p₀ p₁ 0 + s * freeEnergy D U p₀ p₁ 1 -
        rho / 2 * s * (1 - s) *
          (‖p₀ - p₁‖ ^ 2 + ULA.wasserstein2Real μ (D.law 1) ^ 2) := by
  apply (freeEnergy_displacement_strongConvex_cost D U p₀ p₁ rho hU hmeas hint hcost s hs).trans
  have h := wasserstein_sq_le_displacement_cost D hcost
  have hc : 0 ≤ rho / 2 * s * (1 - s) := by positivity [hs.1, sub_nonneg.mpr hs.2]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left (add_le_add_right h _) hc) _

/-- Talagrand's product distance bound is a consequence of the proved
displacement convexity and minimality, with no transport inequality assumed. -/
theorem talagrand_product
    (D : RegularDisplacement ν μ d) (U : P → Z → ℝ) (p₀ p₁ : P) (rho : ℝ)
    (hrho : 0 ≤ rho)
    (hU : StrongConvexOn univ rho (fun w : PBGSO.ProductTransport.Joint P Z ↦ U w.fst w.snd))
    (hmeas : ∀ p, Measurable (U p))
    (hint : ∀ s ∈ Icc (0 : ℝ) 1,
      Integrable (fun z ↦ U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z)) μ)
    (hcost : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1,
      freeEnergy D U p₀ p₁ 0 ≤ freeEnergy D U p₀ p₁ s) :
    rho / 2 * (‖p₀ - p₁‖ ^ 2 + ULA.wasserstein2Real μ (D.law 1) ^ 2) ≤
      freeEnergy D U p₀ p₁ 1 - freeEnergy D U p₀ p₁ 0 := by
  have hconv := freeEnergy_displacement_strongConvex D U p₀ p₁ rho hrho hU hmeas hint hcost
  have h := SourceResults.geodesic_quadratic_growth
    (freeEnergy D U p₀ p₁) (freeEnergy D U p₀ p₁ 1) rho
    (Real.sqrt (‖p₀ - p₁‖ ^ 2 + ULA.wasserstein2Real μ (D.law 1) ^ 2)) hmin
    (by simpa only [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] using hconv)
  simpa only [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] using h

end ProductEnergy

section Tangent

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The actual Fréchet differential, rather than a supplied first-order
inequality, gives the tangent bound of a strongly convex potential. -/
theorem strongConvex_tangent (U : H → ℝ) (rho : ℝ)
    (hU : StrongConvexOn univ rho U) (x y : H) (A : H →L[ℝ] ℝ)
    (hA : HasFDerivAt U A x) :
    U x + A (y - x) + rho / 2 * ‖x - y‖ ^ 2 ≤ U y := by
  let f : ℝ → ℝ := fun s ↦ U (x + s • (y - x))
  have hl : HasDerivAt (fun s : ℝ ↦ x + s • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hd : HasDerivAt f (A (y - x)) 0 := by
    have hA' : HasFDerivAt U A (x + (0 : ℝ) • (y - x)) := by simpa using hA
    convert hA'.comp_hasDerivAt (0 : ℝ) hl using 1
    rfl
  have hconv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      f s ≤ (1 - s) * f 0 + s * U y - rho / 2 * s * (1 - s) * ‖x - y‖ ^ 2 := by
    have h := hU.2 (mem_univ x) (mem_univ y) (sub_nonneg.mpr hs.2) hs.1
      (by ring : (1 - s) + s=1)
    have he : x + s • (y - x) = (1 - s) • x + s • y := by module
    simpa [f, he, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h
  have ht := SourceResults.geodesic_convexity_first_order f (U y) (A (y - x)) rho ‖x - y‖
    hd.hasDerivWithinAt hconv
  simp only [f, zero_smul, add_zero] at ht
  linarith

omit [NormedSpace ℝ H] in
/-- Cauchy–Schwarz for actual square-integrable vector fields. -/
theorem integral_inner_le_secondCost {Ω : Type*} [MeasurableSpace Ω]
    [InnerProductSpace ℝ H] (Q : Measure Ω) (A B : Ω → H)
    (hA : MemLp A 2 Q) (hB : MemLp B 2 Q) :
    (∫ ω, inner ℝ (A ω) (B ω) ∂Q) ≤
      (eLpNorm A 2 Q).toReal * (eLpNorm B 2 Q).toReal := by
  have h := real_inner_le_norm (hA.toLp A) (hB.toLp B)
  rw [L2.inner_def, Lp.norm_toLp, Lp.norm_toLp] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with ω hAω hBω
  rw [hAω, hBω]

end Tangent

section OptimalMaps

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

/-- An actual finite-cost optimal Monge map. Existence of such maps, with
smooth positive Jacobian when needed, is a transport regularity hypothesis.
Optimality compares its cost with every genuine coupling, not with a supplied
real-valued distance. -/
structure OptimalMap (μ ν : Measure Z) where
  transport : Z → Z
  measurable_transport : Measurable transport
  pushes : μ.map transport = ν
  finite_cost : MemLp (fun z ↦ z - transport z) 2 μ
  minimal : ∀ c : ULA.Coupling μ ν,
    eLpNorm (fun z ↦ z - transport z) 2 μ ≤ ULA.couplingCost c.joint

namespace OptimalMap

variable {μ ν η : Measure Z}

/-- Optimality really identifies the infimum over actual coupling costs. -/
theorem wasserstein_eq_cost (T : OptimalMap μ ν) :
    ULA.wasserstein2 μ ν = eLpNorm (fun z ↦ z - T.transport z) 2 μ := by
  apply le_antisymm
  · have h := ULA.wasserstein2_le_random_cost μ id T.transport measurable_id T.measurable_transport
    simpa [T.pushes] using h
  · exact le_iInf T.minimal

theorem wasserstein_ne_top (T : OptimalMap μ ν) : ULA.wasserstein2 μ ν ≠ ⊤ := by
  rw [T.wasserstein_eq_cost]
  exact T.finite_cost.eLpNorm_ne_top

/-- Gluing two actual Monge maps and applying Minkowski proves the triangle
inequality for the genuine Wasserstein infimum on this regular class. -/
theorem wasserstein_triangle (T : OptimalMap μ ν) (S : OptimalMap ν η) :
    ULA.wasserstein2 μ η ≤ ULA.wasserstein2 μ ν + ULA.wasserstein2 ν η := by
  have hm : μ.map (S.transport ∘ T.transport) = η := by
    rw [← Measure.map_map S.measurable_transport T.measurable_transport, T.pushes, S.pushes]
  have hb := ULA.wasserstein2_le_random_cost μ id (S.transport ∘ T.transport) measurable_id
    (S.measurable_transport.comp T.measurable_transport)
  simp only [Measure.map_id, hm] at hb
  apply hb.trans
  rw [T.wasserstein_eq_cost, S.wasserstein_eq_cost]
  calc
    eLpNorm (fun z ↦ z - (S.transport ∘ T.transport) z) 2 μ =
      eLpNorm ((fun z ↦ z - T.transport z) +
        (fun z ↦ T.transport z - S.transport (T.transport z))) 2 μ := by
      congr 1
      funext z
      simp
    _ ≤ eLpNorm (fun z ↦ z - T.transport z) 2 μ +
      eLpNorm (fun z ↦ T.transport z - S.transport (T.transport z)) 2 μ :=
      eLpNorm_add_le (by norm_num)
    _ = _ := by
      congr 1
      have hmap := eLpNorm_map_measure
        (μ := μ) (p := 2) (g := fun z ↦ z - S.transport z)
        ((measurable_id.sub S.measurable_transport).aestronglyMeasurable)
        T.measurable_transport.aemeasurable
      simpa only [T.pushes, Function.comp_def] using hmap.symm

/-- The triangle inequality in real arithmetic is justified by the finite
optimal-map costs, so no infinite cost can collapse to zero. -/
theorem wassersteinReal_triangle (T : OptimalMap μ ν) (S : OptimalMap ν η) :
    ULA.wasserstein2Real μ η ≤ ULA.wasserstein2Real μ ν + ULA.wasserstein2Real ν η := by
  have hfin := ENNReal.add_ne_top.mpr ⟨T.wasserstein_ne_top, S.wasserstein_ne_top⟩
  have h := ENNReal.toReal_mono hfin (T.wasserstein_triangle S)
  simpa only [ULA.wasserstein2Real, ENNReal.toReal_add T.wasserstein_ne_top S.wasserstein_ne_top]
    using h

end OptimalMap

end OptimalMaps

end LatentDiffusion.RegularTransport
