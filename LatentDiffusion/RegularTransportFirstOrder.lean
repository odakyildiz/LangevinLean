import LatentDiffusion.RegularTransport
import LatentDiffusion.RegularFlowCalculus
import Mathlib.Data.EReal.Operations

set_option linter.style.header false

/-! # First order entropy and free energy transport inequalities

The entropy tangent inequality is proved from the actual density Jacobian
formula, the elementary inequality `log λ ≤ λ-1`, and ordinary Lebesgue
integration by parts with explicit integrable tail products.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open Filter
open scoped BigOperators ENNReal NNReal
open scoped Topology

namespace LatentDiffusion.RegularTransport

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [CompleteSpace Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {μ : Measure Z} [IsProbabilityMeasure μ] {d : ℕ}

namespace RegularDisplacement

variable (D : RegularDisplacement (volume : Measure Z) μ d)

theorem initial_density_law : μ = volume.withDensity (fun z ↦ ENNReal.ofReal (D.density 0 z)) := by
  simpa using D.density_law 0 (by constructor <;> norm_num)

/-- The certified eigenvalues of DT compute the actual divergence of T-id. -/
theorem displacement_divergence (z : Z) :
    RegularFlowCalculus.fluxDivergence (fun z ↦ D.transport z - z) z =
      ∑ i, (D.eigenvalue z i - 1) := by
  change RegularFlowCalculus.fluxDivergence (D.transport - id) z = _
  rw [RegularFlowCalculus.fluxDivergence_eq_trace _
    (D.jacobian z - ContinuousLinearMap.id ℝ Z) z
    ((D.derivative_transport z).sub (hasFDerivAt_id z))]
  rw [LinearMap.trace_eq_matrix_trace ℝ (D.spectral_basis z).toBasis]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply]
  simp [D.jacobian_eigenvector]

/-- The entropy integrand lies above its tangent obtained from the actual DT
trace; this is the finite dimensional log determinant inequality. -/
theorem log_density_tangent (z : Z) :
    Real.log (D.density 0 z) - ∑ i, (D.eigenvalue z i - 1) ≤
      Real.log (D.density 1 (D.transport z)) := by
  have hmass := D.density_jacobian 1 (by constructor <;> norm_num) z
  simp only [interpolate_one] at hmass
  have h0 := D.positive_density 0 (by constructor <;> norm_num) z
  have hj := spectralJacobian_pos (D.eigenvalue z) (D.positive_eigenvalue z) 1
    (by constructor <;> norm_num)
  rw [hmass, Real.log_div h0.ne' hj.ne', spectralJacobian_one,
    Real.log_prod (fun i _ ↦ (D.positive_eigenvalue z i).ne')]
  have hlog : (∑ i, Real.log (D.eigenvalue z i)) ≤ ∑ i, (D.eigenvalue z i - 1) :=
    Finset.sum_le_sum fun i _ ↦ Real.log_le_sub_one_of_pos (D.positive_eigenvalue z i)
  linarith

/-- The actual entropy tangent lower bound. The final score pairing is a
conclusion, rather than a regularity assumption. -/
theorem entropy_tangent
    (hq : ContDiff ℝ 1 (D.density 0))
    (htail : RegularFlowCalculus.NoBoundaryFlux (fun z ↦ D.transport z - z) (D.density 0)) :
    (∫ z, inner ℝ (D.transport z - z) (gradient (fun z ↦ Real.log (D.density 0 z)) z) ∂μ) ≤
      D.entropy 1 - D.entropy 0 := by
  have hpos := D.positive_density 0 (by constructor <;> norm_num)
  have hIBP := RegularFlowCalculus.transport_score_pairing (D.density 0)
    (fun z ↦ D.transport z - z) hq hpos htail
  have hInt := RegularFlowCalculus.transport_score_integrable (D.density 0)
    (fun z ↦ D.transport z - z) hq hpos htail
  rw [← D.initial_density_law] at hIBP hInt
  simp_rw [D.displacement_divergence] at hIBP
  have htrace : Integrable (fun z ↦ ∑ i, (D.eigenvalue z i - 1)) μ :=
    hInt.1.congr (ae_of_all _ D.displacement_divergence)
  have h0 := D.integrable_log 0 (by constructor <;> norm_num)
  have h1 := D.integrable_log 1 (by constructor <;> norm_num)
  simp only [interpolate_zero, id_eq, interpolate_one] at h0 h1
  have hbound := integral_mono (h0.sub htrace) h1 D.log_density_tangent
  rw [integral_sub' h0 htrace, hIBP] at hbound
  rw [D.entropy_eq_pullback 0 (by constructor <;> norm_num),
    D.entropy_eq_pullback 1 (by constructor <;> norm_num)]
  simp only [interpolate_zero, id_eq, interpolate_one]
  linarith

/-- The entropy tangent controls every positive displacement time, so it also
controls the actual right lower directional derivative. -/
theorem entropy_tangent_at
    (hq : ContDiff ℝ 1 (D.density 0))
    (htail : RegularFlowCalculus.NoBoundaryFlux (fun z ↦ D.transport z - z) (D.density 0))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    s * (∫ z, inner ℝ (D.transport z - z)
      (gradient (fun z ↦ Real.log (D.density 0 z)) z) ∂μ) ≤ D.entropy s - D.entropy 0 := by
  have hpos := D.positive_density 0 (by constructor <;> norm_num)
  have hIBP := RegularFlowCalculus.transport_score_pairing (D.density 0)
    (fun z ↦ D.transport z - z) hq hpos htail
  have hInt := RegularFlowCalculus.transport_score_integrable (D.density 0)
    (fun z ↦ D.transport z - z) hq hpos htail
  rw [← D.initial_density_law] at hIBP hInt
  simp_rw [D.displacement_divergence] at hIBP
  have htrace : Integrable (fun z ↦ ∑ i, (D.eigenvalue z i - 1)) μ :=
    hInt.1.congr (ae_of_all _ D.displacement_divergence)
  have hpoint (z : Z) : Real.log (D.density 0 z) - s * (∑ i, (D.eigenvalue z i - 1)) ≤
      Real.log (D.density s (interpolate D.transport s z)) := by
    rw [D.density_jacobian s hs z, Real.log_div (hpos z).ne'
      (spectralJacobian_pos _ (D.positive_eigenvalue z) s hs).ne']
    have hlog : Real.log (spectralJacobian (D.eigenvalue z) s) ≤
        s * (∑ i, (D.eigenvalue z i - 1)) := by
      unfold spectralJacobian
      rw [Real.log_prod (fun i _ ↦ ?_)]
      · rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        have hi : 0 < (1 - s) + s * D.eigenvalue z i := by
          have hh := spectralJacobian_pos (d := 1) (fun _ ↦ D.eigenvalue z i)
            (fun _ ↦ D.positive_eigenvalue z i) s hs
          simpa [spectralJacobian] using hh
        have hh := Real.log_le_sub_one_of_pos hi
        nlinarith
      · have hh := spectralJacobian_pos (d := 1) (fun _ ↦ D.eigenvalue z i)
          (fun _ ↦ D.positive_eigenvalue z i) s hs
        simpa [spectralJacobian] using hh.ne'
    linarith
  have h0 := D.integrable_log 0 (by constructor <;> norm_num)
  simp only [interpolate_zero, id_eq] at h0
  have hbound := integral_mono (h0.sub (htrace.const_mul s)) (D.integrable_log s hs) hpoint
  rw [integral_sub' h0 (htrace.const_mul s), integral_const_mul, hIBP] at hbound
  rw [D.entropy_eq_pullback 0 (by constructor <;> norm_num), D.entropy_eq_pullback s hs]
  simp only [interpolate_zero, id_eq]
  linarith

end RegularDisplacement

section PotentialTangent

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]

abbrev Joint := PBGSO.ProductTransport.Joint P Z

/-- Actual joint displacement field of a regular transport. -/
def displacementField (D : RegularDisplacement (volume : Measure Z) μ d)
    (p₀ p₁ : P) (z : Z) : Joint (P := P) (Z := Z) :=
  PBGSO.ProductTransport.embed (p₁ - p₀) (D.transport z - z)

theorem displacementField_memLp
    (D : RegularDisplacement (volume : Measure Z) μ d) (p₀ p₁ : P)
    (hc : MemLp (fun z ↦ z - D.transport z) 2 μ) :
    MemLp (displacementField D p₀ p₁) 2 μ := by
  have h := ProximalLangevin.memLp_lipschitz_observable μ
    (PBGSO.ProductTransport.embed_lipschitz (p₁ - p₀)) hc.neg
  convert h using 1
  funext z
  simp [displacementField]

theorem integrable_inner_memLp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A B : Z → H) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) :
    Integrable (fun z ↦ inner ℝ (A z) (B z)) μ := by
  apply (L2.integrable_inner (hA.toLp A) (hB.toLp B)).congr
  filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with z hAz hBz
  rw [hAz, hBz]

/-- First order bound for the potential expectation from its actual
Fréchet gradient. All terms are actual law integrals. -/
theorem potential_tangent
    (D : RegularDisplacement (volume : Measure Z) μ d)
    (U : P → Z → ℝ) (p₀ p₁ : P) (rho : ℝ) (G : Z → Joint (P := P) (Z := Z))
    (hU : StrongConvexOn univ rho (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd))
    (hG : ∀ z, HasGradientAt (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd)
      (G z) (PBGSO.ProductTransport.embed p₀ z))
    (hG2 : MemLp G 2 μ) (hc : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (hU0 : Integrable (U p₀) μ)
    (hU1 : Integrable (fun z ↦ U p₁ (D.transport z)) μ) :
    (∫ z, inner ℝ (G z) (displacementField D p₀ p₁ z) ∂μ) +
      rho / 2 * (‖p₀ - p₁‖ ^ 2 + (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal ^ 2) ≤
      (∫ z, U p₁ (D.transport z) ∂μ) - ∫ z, U p₀ z ∂μ := by
  have hV := displacementField_memLp D p₀ p₁ hc
  have hip := integrable_inner_memLp G _ hG2 hV
  have hsq := hc.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have htot : Integrable (fun z ↦ ‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2) μ :=
    (integrable_const _).add hsq
  have hp (z : Z) :
      inner ℝ (G z) (displacementField D p₀ p₁ z) +
        rho / 2 * (‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2) ≤
      U p₁ (D.transport z) - U p₀ z := by
    have h := strongConvex_tangent
      (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd) rho hU
      (PBGSO.ProductTransport.embed p₀ z)
      (PBGSO.ProductTransport.embed p₁ (D.transport z)) _ (hG z).hasFDerivAt
    simp only [WithLp.prod_norm_sq_eq_of_L2] at h
    change U p₀ z + inner ℝ (G z) (displacementField D p₀ p₁ z) +
      rho / 2 * (‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2) ≤ U p₁ (D.transport z) at h
    linarith
  have hb := integral_mono (hip.add (htot.const_mul (rho / 2))) (hU1.sub hU0) hp
  rw [integral_add' hip (htot.const_mul (rho / 2)), integral_const_mul,
    integral_add (integrable_const _) hsq, integral_sub' hU1 hU0,
    integral_const, ← secondCost_sq_eq_integral μ _ hc] at hb
  simpa using hb

theorem potential_tangent_at
    (D : RegularDisplacement (volume : Measure Z) μ d)
    (U : P → Z → ℝ) (p₀ p₁ : P) (rho : ℝ) (G : Z → Joint (P := P) (Z := Z))
    (hU : StrongConvexOn univ rho (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd))
    (hG : ∀ z, HasGradientAt (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd)
      (G z) (PBGSO.ProductTransport.embed p₀ z))
    (hG2 : MemLp G 2 μ) (hc : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (hU0 : Integrable (U p₀) μ)
    (s : ℝ)
    (hUs : Integrable (fun z ↦ U (parameterInterpolate p₀ p₁ s)
      (interpolate D.transport s z)) μ) :
    s * (∫ z, inner ℝ (G z) (displacementField D p₀ p₁ z) ∂μ) +
      rho / 2 * s ^ 2 * (‖p₀ - p₁‖ ^ 2 + (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal ^ 2) ≤
      (∫ z, U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z) ∂μ)-
        ∫ z, U p₀ z ∂μ := by
  have hV := displacementField_memLp D p₀ p₁ hc
  have hip := integrable_inner_memLp G _ hG2 hV
  have hsq := hc.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have htot : Integrable (fun z ↦ ‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2) μ :=
    (integrable_const _).add hsq
  have hp (z : Z) : s * inner ℝ (G z) (displacementField D p₀ p₁ z)+
      (rho / 2 * s ^ 2) * (‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2) ≤
      U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z) - U p₀ z := by
    let x := PBGSO.ProductTransport.embed p₀ z
    let y := PBGSO.ProductTransport.embed (parameterInterpolate p₀ p₁ s)
      (interpolate D.transport s z)
    have hsub : y - x = s • displacementField D p₀ p₁ z := by
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · change ((1 - s) • p₀ + s • p₁) - p₀ = s • (p₁ - p₀)
        module
      · change ((1 - s) • z + s • D.transport z) - z = s • (D.transport z - z)
        module
    have hn : ‖x - y‖ ^ 2 = s ^ 2 * (‖p₀ - p₁‖ ^ 2 + ‖z - D.transport z‖ ^ 2) := by
      rw [norm_sub_rev, hsub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        WithLp.prod_norm_sq_eq_of_L2]
      change s ^ 2 * (‖p₁ - p₀‖ ^ 2 + ‖D.transport z - z‖ ^ 2) = _
      rw [norm_sub_rev p₁ p₀, norm_sub_rev (D.transport z) z]
    have h := strongConvex_tangent
      (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd) rho hU x y _ (hG z).hasFDerivAt
    change U p₀ z + inner ℝ (G z) (y - x) + rho / 2 * ‖x - y‖ ^ 2 ≤
      U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z) at h
    rw [hsub, inner_smul_right, hn] at h
    nlinarith
  have hb := integral_mono ((hip.const_mul s).add (htot.const_mul (rho / 2 * s ^ 2)))
    (hUs.sub hU0) hp
  rw [integral_add' (hip.const_mul s) (htot.const_mul (rho / 2 * s ^ 2)),
    integral_const_mul, integral_const_mul, integral_add (integrable_const _) hsq,
    integral_sub' hUs hU0, integral_const, ← secondCost_sq_eq_integral μ _ hc] at hb
  simpa using hb

/-- The genuine free energy lies above the sum of its potential and entropy
tangents; no first order transport inequality is an assumption. -/
theorem freeEnergy_tangent
    (D : RegularDisplacement (volume : Measure Z) μ d)
    (U : P → Z → ℝ) (p₀ p₁ : P) (rho : ℝ) (G : Z → Joint (P := P) (Z := Z))
    (hU : StrongConvexOn univ rho (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd))
    (hG : ∀ z, HasGradientAt (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd)
      (G z) (PBGSO.ProductTransport.embed p₀ z))
    (hG2 : MemLp G 2 μ) (hc : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (hUmeas : ∀ p, Measurable (U p))
    (hU0 : Integrable (U p₀) μ) (hU1 : Integrable (fun z ↦ U p₁ (D.transport z)) μ)
    (hq : ContDiff ℝ 1 (D.density 0))
    (htail : RegularFlowCalculus.NoBoundaryFlux (fun z ↦ D.transport z - z) (D.density 0)) :
    (∫ z, inner ℝ (G z) (displacementField D p₀ p₁ z) ∂μ) +
      (∫ z, inner ℝ (D.transport z - z) (gradient (fun z ↦ Real.log (D.density 0 z)) z) ∂μ) +
      rho / 2 * (‖p₀ - p₁‖ ^ 2 + (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal ^ 2) ≤
      freeEnergy D U p₀ p₁ 1 - freeEnergy D U p₀ p₁ 0 := by
  have hp := potential_tangent D U p₀ p₁ rho G hU hG hG2 hc hU0 hU1
  have he := D.entropy_tangent hq htail
  have hmap : (∫ z, U p₁ z ∂D.law 1) = ∫ z, U p₁ (D.transport z) ∂μ := by
    rw [D.law_one]
    exact integral_map D.measurable_transport.aemeasurable (hUmeas p₁).aestronglyMeasurable
  simp only [freeEnergy, parameterInterpolate, sub_self, zero_smul, one_smul, zero_add,
    sub_zero, add_zero, D.law_zero, hmap]
  linarith

theorem freeEnergy_tangent_at
    (D : RegularDisplacement (volume : Measure Z) μ d)
    (U : P → Z → ℝ) (p₀ p₁ : P) (rho : ℝ) (G : Z → Joint (P := P) (Z := Z))
    (hU : StrongConvexOn univ rho (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd))
    (hG : ∀ z, HasGradientAt (fun w : Joint (P := P) (Z := Z) ↦ U w.fst w.snd)
      (G z) (PBGSO.ProductTransport.embed p₀ z))
    (hG2 : MemLp G 2 μ) (hc : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (hUmeas : ∀ p, Measurable (U p)) (hU0 : Integrable (U p₀) μ)
    (hq : ContDiff ℝ 1 (D.density 0))
    (htail : RegularFlowCalculus.NoBoundaryFlux (fun z ↦ D.transport z - z) (D.density 0))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hUs : Integrable (fun z ↦ U (parameterInterpolate p₀ p₁ s)
      (interpolate D.transport s z)) μ) :
    s * ((∫ z, inner ℝ (G z) (displacementField D p₀ p₁ z) ∂μ) +
      ∫ z, inner ℝ (D.transport z - z) (gradient (fun z ↦ Real.log (D.density 0 z)) z) ∂μ) +
      rho / 2 * s ^ 2 * (‖p₀ - p₁‖ ^ 2 + (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal ^ 2) ≤
      freeEnergy D U p₀ p₁ s - freeEnergy D U p₀ p₁ 0 := by
  have hp := potential_tangent_at D U p₀ p₁ rho G hU hG hG2 hc hU0 s hUs
  have he := D.entropy_tangent_at hq htail s hs
  have hmap : (∫ z, U (parameterInterpolate p₀ p₁ s) z ∂D.law s) =
      ∫ z, U (parameterInterpolate p₀ p₁ s) (interpolate D.transport s z) ∂μ := by
    exact integral_map (interpolate_measurable _ D.measurable_transport s).aemeasurable
      (hUmeas _).aestronglyMeasurable
  simp only [freeEnergy, parameterInterpolate, sub_zero, one_smul, zero_smul,
    add_zero, D.law_zero] at *
  rw [hmap]
  linarith

end PotentialTangent

section FisherBound

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]

theorem joint_fst_memLp (G : Z → PBGSO.ProductTransport.Joint P Z) (hG : MemLp G 2 μ) :
    MemLp (fun z ↦ (G z).fst) 2 μ := by
  apply hG.mono
    ((WithLp.continuous_fst 2 P Z).comp_aestronglyMeasurable hG.aestronglyMeasurable)
  exact ae_of_all _ fun z ↦ WithLp.norm_fst_le (p := 2) P (G z)

theorem joint_snd_memLp (G : Z → PBGSO.ProductTransport.Joint P Z) (hG : MemLp G 2 μ) :
    MemLp (fun z ↦ (G z).snd) 2 μ := by
  apply hG.mono
    ((WithLp.continuous_snd 2 P Z).comp_aestronglyMeasurable hG.aestronglyMeasurable)
  exact ae_of_all _ fun z ↦ WithLp.norm_snd_le (p := 2) P (G z)

/-- Averaging the parameter gradient happens before taking its squared norm,
as required by the paper's optimizer/Wasserstein metric. -/
def fisherInformation
    (D : RegularDisplacement (volume : Measure Z) μ d)
    (G : Z → PBGSO.ProductTransport.Joint P Z) : ℝ :=
  ‖∫ z, (G z).fst ∂μ‖ ^ 2 +
    ∫ z, ‖(G z).snd + gradient (fun z ↦ Real.log (D.density 0 z)) z‖ ^ 2 ∂μ

theorem sqrt_cauchy_two (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a * c + b * d ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (c ^ 2 + d ^ 2) := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  nlinarith [sq_nonneg (a * d - b * c)]

/-- Exact first-order pairing before applying Cauchy–Schwarz. This is the
form that must be summed over data before squaring the parameter gradient. -/
theorem tangent_pairing_eq
    (D : RegularDisplacement (volume : Measure Z) μ d) (p₀ p₁ : P)
    (G : Z → PBGSO.ProductTransport.Joint P Z) (hG : MemLp G 2 μ)
    (hc : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (hs : MemLp (fun z ↦ gradient (fun z ↦ Real.log (D.density 0 z)) z) 2 μ) :
    (∫ z, inner ℝ (G z) (displacementField D p₀ p₁ z) ∂μ) +
      (∫ z, inner ℝ (D.transport z - z) (gradient (fun z ↦ Real.log (D.density 0 z)) z) ∂μ) =
    inner ℝ (∫ z, (G z).fst ∂μ) (p₁ - p₀) +
      ∫ z, inner ℝ ((G z).snd + gradient (fun z ↦ Real.log (D.density 0 z)) z)
        (D.transport z - z) ∂μ := by
  let v : Z → Z := fun z ↦ D.transport z - z
  let score : Z → Z := fun z ↦ gradient (fun z ↦ Real.log (D.density 0 z)) z
  have hv : MemLp v 2 μ := by
    convert hc.neg using 1
    funext z
    simp [v]
  have hfst := joint_fst_memLp G hG
  have hsnd := joint_snd_memLp G hG
  have hip := integrable_inner_memLp (fun z ↦ (G z).snd) v hsnd hv
  have his := integrable_inner_memLp score v hs hv
  have hpar := (hfst.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).inner_const
    (𝕜 := ℝ) (p₁ - p₀)
  have hparEq : (∫ z, inner ℝ (G z).fst (p₁ - p₀) ∂μ) =
      inner ℝ (∫ z, (G z).fst ∂μ) (p₁ - p₀) := by
    simpa only [real_inner_comm] using
      integral_inner (hfst.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) (p₁ - p₀)
  simp only [displacementField, WithLp.prod_inner_apply, PBGSO.ProductTransport.embed]
  change (∫ z, inner ℝ (G z).fst (p₁ - p₀) + inner ℝ (G z).snd (v z) ∂μ) +
    (∫ z, inner ℝ (v z) (score z) ∂μ) =
    inner ℝ (∫ z, (G z).fst ∂μ) (p₁ - p₀) + ∫ z, inner ℝ ((G z).snd + score z) (v z) ∂μ
  rw [integral_add hpar hip, hparEq]
  simp only [inner_add_left]
  rw [integral_add hip his]
  simp only [real_inner_comm (v _) (score _)]
  ring

/-- Normalized finite-data completion of the square. Parameter gradients are
summed first. Averaging separate one-datum LSIs would give the wrong Fisher
information and cannot establish this theorem. -/
theorem normalized_extendedLSI_of_tangents
    {M : ℕ} (hM : 0 < M) (rho : ℝ) (hrho : 0 < rho) (dp : P)
    (gap pair b c : Fin M → ℝ) (g : Fin M → P)
    (htangent : ∀ m, gap m + inner ℝ (g m) dp + pair m +
      rho / 2 * (‖dp‖ ^ 2 + c m ^ 2) ≤ 0)
    (hpair : ∀ m, -pair m ≤ b m * c m) :
    2 * rho * ((M : ℝ)⁻¹ * ∑ m, gap m) ≤
      ‖(M : ℝ)⁻¹ • ∑ m, g m‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m, b m ^ 2 := by
  let w : ℝ := (M : ℝ)⁻¹
  have hw : 0 ≤ w := by positivity
  have hcancel : w * (M : ℝ) = 1 := by
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hM.ne')
  have hpoint (m : Fin M) :
      2 * rho * gap m ≤ -2 * rho * inner ℝ (g m) dp - rho ^ 2 * ‖dp‖ ^ 2 + b m ^ 2 := by
    have h := htangent m
    have hp := hpair m
    have hsq := sq_nonneg (b m - rho * c m)
    nlinarith
  have hsum := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) ↦ hpoint m)) hw
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  simp only [← Finset.mul_sum] at hsum
  have hmean : inner ℝ (w • ∑ m, g m) dp = w * ∑ m, inner ℝ (g m) dp := by
    simp [inner_smul_left, sum_inner]
  have hquad := sq_nonneg ‖(w • ∑ m, g m) + rho • dp‖
  have hnorm : ‖rho • dp‖ ^ 2 = rho ^ 2 * ‖dp‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [norm_add_sq_real, hnorm, real_inner_smul_right] at hquad
  rw [hmean] at hquad
  have hconst : w * ((M : ℝ) * (rho ^ 2 * ‖dp‖ ^ 2)) = rho ^ 2 * ‖dp‖ ^ 2 := by
    rw [← mul_assoc, hcancel, one_mul]
  change 2 * rho * (w * ∑ m, gap m) ≤ ‖w • ∑ m, g m‖ ^ 2 + w * ∑ m, b m ^ 2
  nlinarith [hconst]

/-- The exact parameter-mean/latent-score pairing is bounded by the actual
Fisher information and the actual L² displacement. -/
theorem negative_tangent_pairing_le
    (D : RegularDisplacement (volume : Measure Z) μ d) (p₀ p₁ : P)
    (G : Z → PBGSO.ProductTransport.Joint P Z) (hG : MemLp G 2 μ)
    (hc : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (hs : MemLp (fun z ↦ gradient (fun z ↦ Real.log (D.density 0 z)) z) 2 μ) :
    -((∫ z, inner ℝ (G z) (displacementField D p₀ p₁ z) ∂μ) +
      ∫ z, inner ℝ (D.transport z - z) (gradient (fun z ↦ Real.log (D.density 0 z)) z) ∂μ) ≤
      Real.sqrt (fisherInformation D G) *
        Real.sqrt (‖p₀ - p₁‖ ^ 2 + (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal ^ 2) := by
  let v : Z → Z := fun z ↦ D.transport z - z
  let score : Z → Z := fun z ↦ gradient (fun z ↦ Real.log (D.density 0 z)) z
  let L : Z → Z := fun z ↦ (G z).snd + score z
  have hv : MemLp v 2 μ := by
    convert hc.neg using 1
    funext z
    simp [v]
  have hfst := joint_fst_memLp G hG
  have hsnd := joint_snd_memLp G hG
  have hL : MemLp L 2 μ := hsnd.add hs
  have hip := integrable_inner_memLp (fun z ↦ (G z).snd) v hsnd hv
  have his := integrable_inner_memLp score v hs hv
  have hpar := (hfst.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).inner_const
    (𝕜 := ℝ) (p₁ - p₀)
  have hparEq : (∫ z, inner ℝ (G z).fst (p₁ - p₀) ∂μ) =
      inner ℝ (∫ z, (G z).fst ∂μ) (p₁ - p₀) := by
    simpa only [real_inner_comm] using
      integral_inner (hfst.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) (p₁ - p₀)
  have hagg : (∫ z, inner ℝ (G z) (displacementField D p₀ p₁ z) ∂μ) +
      (∫ z, inner ℝ (v z) (score z) ∂μ) =
      inner ℝ (∫ z, (G z).fst ∂μ) (p₁ - p₀) + ∫ z, inner ℝ (L z) (v z) ∂μ := by
    simp only [displacementField, WithLp.prod_inner_apply, PBGSO.ProductTransport.embed]
    change (∫ z, inner ℝ (G z).fst (p₁ - p₀) + inner ℝ (G z).snd (v z) ∂μ) +
      (∫ z, inner ℝ (v z) (score z) ∂μ) = _
    rw [integral_add hpar hip, hparEq]
    simp only [L, inner_add_left]
    rw [integral_add hip his]
    simp only [real_inner_comm (v _) (score _)]
    ring
  have hparam : -inner ℝ (∫ z, (G z).fst ∂μ) (p₁ - p₀) ≤
      ‖∫ z, (G z).fst ∂μ‖ * ‖p₀ - p₁‖ := by
    simpa only [inner_neg_left, norm_neg, norm_sub_rev] using
      real_inner_le_norm (-(∫ z, (G z).fst ∂μ)) (p₁ - p₀)
  have hlatent : -(∫ z, inner ℝ (L z) (v z) ∂μ) ≤
      (eLpNorm L 2 μ).toReal * (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal := by
    have h := integral_inner_le_secondCost μ (-L) v hL.neg hv
    have hvnorm : eLpNorm v 2 μ = eLpNorm (fun z ↦ z - D.transport z) 2 μ := by
      calc
        eLpNorm v 2 μ = eLpNorm (-(fun z ↦ z - D.transport z)) 2 μ := by
          congr 1
          funext z
          simp [v]
        _ = _ := eLpNorm_neg _ _ _
    simpa only [Pi.neg_apply, inner_neg_left, integral_neg, eLpNorm_neg, hvnorm] using h
  have hI : fisherInformation D G =
      ‖∫ z, (G z).fst ∂μ‖ ^ 2 + (eLpNorm L 2 μ).toReal ^ 2 := by
    rw [fisherInformation, secondCost_sq_eq_integral μ L hL]
  have hCS := sqrt_cauchy_two ‖∫ z, (G z).fst ∂μ‖ (eLpNorm L 2 μ).toReal
    ‖p₀ - p₁‖ (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal
    (norm_nonneg _) ENNReal.toReal_nonneg (norm_nonneg _) ENNReal.toReal_nonneg
  change - ((∫ z, inner ℝ (G z) (displacementField D p₀ p₁ z) ∂μ) +
    ∫ z, inner ℝ (v z) (score z) ∂μ) ≤ _
  rw [hagg, hI]
  linarith

/-- The extended log Sobolev inequality is proved from strong joint
log-concavity, smooth density change of variables and integrable tail products.
Neither the first order transport bound nor LSI is one of the hypotheses. -/
theorem extendedLSI
    (D : RegularDisplacement (volume : Measure Z) μ d)
    (U : P → Z → ℝ) (p₀ p₁ : P) (rho : ℝ) (hrho : 0 < rho)
    (G : Z → PBGSO.ProductTransport.Joint P Z)
    (hU : StrongConvexOn univ rho
      (fun w : PBGSO.ProductTransport.Joint P Z ↦ U w.fst w.snd))
    (hG : ∀ z, HasGradientAt
      (fun w : PBGSO.ProductTransport.Joint P Z ↦ U w.fst w.snd)
      (G z) (PBGSO.ProductTransport.embed p₀ z))
    (hG2 : MemLp G 2 μ) (hc : MemLp (fun z ↦ z - D.transport z) 2 μ)
    (hs : MemLp (fun z ↦ gradient (fun z ↦ Real.log (D.density 0 z)) z) 2 μ)
    (hUmeas : ∀ p, Measurable (U p))
    (hU0 : Integrable (U p₀) μ) (hU1 : Integrable (fun z ↦ U p₁ (D.transport z)) μ)
    (hq : ContDiff ℝ 1 (D.density 0))
    (htail : RegularFlowCalculus.NoBoundaryFlux (fun z ↦ D.transport z - z) (D.density 0)) :
    2 * rho * (freeEnergy D U p₀ p₁ 0 - freeEnergy D U p₀ p₁ 1) ≤ fisherInformation D G := by
  have ht := freeEnergy_tangent D U p₀ p₁ rho G hU hG hG2 hc hUmeas hU0 hU1 hq htail
  have hp := negative_tangent_pairing_le D p₀ p₁ G hG2 hc hs
  have hI : 0 ≤ fisherInformation D G := by
    exact add_nonneg (sq_nonneg _) (integral_nonneg fun z ↦ sq_nonneg _)
  apply LatentDiffusion.extendedLSI_of_firstOrder hrho hI
    (r := Real.sqrt (‖p₀ - p₁‖ ^ 2 + (eLpNorm (fun z ↦ z - D.transport z) 2 μ).toReal ^ 2))
  rw [Real.sq_sqrt (by positivity)]
  linarith

end FisherBound

section Dataset

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [MeasurableSpace P] [BorelSpace P] [SecondCountableTopology P]

/-- Analytic regularity for the finite data-set theorem. These fields contain
only actual probability laws, density/Jacobian data, Fréchet gradients, L² and
L¹ integrability, and the tail products of ordinary integration by parts. -/
structure DatasetRegularity (M d : ℕ) (p₀ p₁ : P) (rho : ℝ) where
  law : Fin M → ProbabilityMeasure Z
  displacement : (m : Fin M) → RegularDisplacement volume (law m : Measure Z) d
  potential : Fin M → P → Z → ℝ
  potential_strong : ∀ m, StrongConvexOn univ rho
    (fun w : PBGSO.ProductTransport.Joint P Z ↦ potential m w.fst w.snd)
  potential_measurable : ∀ m p, Measurable (potential m p)
  potential_integrable_initial : ∀ m, Integrable (potential m p₀) (law m : Measure Z)
  potential_integrable_final : ∀ m,
    Integrable (fun z ↦ potential m p₁ ((displacement m).transport z)) (law m : Measure Z)
  potential_integrable_path : ∀ m s, s ∈ Icc (0 : ℝ) 1 →
    Integrable (fun z ↦ potential m (parameterInterpolate p₀ p₁ s)
      (interpolate (displacement m).transport s z)) (law m : Measure Z)
  potential_gradient : Fin M → Z → PBGSO.ProductTransport.Joint P Z
  potential_hasGradientAt : ∀ m z, HasGradientAt
    (fun w : PBGSO.ProductTransport.Joint P Z ↦ potential m w.fst w.snd)
    (potential_gradient m z) (PBGSO.ProductTransport.embed p₀ z)
  potential_gradient_memLp : ∀ m, MemLp (potential_gradient m) 2 (law m : Measure Z)
  displacement_memLp : ∀ m,
    MemLp (fun z ↦ z - (displacement m).transport z) 2 (law m : Measure Z)
  score_memLp : ∀ m,
    MemLp (fun z ↦ gradient (fun z ↦ Real.log ((displacement m).density 0 z)) z)
      2 (law m : Measure Z)
  density_C1 : ∀ m, ContDiff ℝ 1 ((displacement m).density 0)
  integrable_tails : ∀ m, RegularFlowCalculus.NoBoundaryFlux
    (fun z ↦ (displacement m).transport z - z) ((displacement m).density 0)

namespace DatasetRegularity

variable {M : ℕ} {p₀ p₁ : P} {rho : ℝ}
  (R : DatasetRegularity (Z := Z) M d p₀ p₁ rho)

def freeEnergy (s : ℝ) : ℝ := (M : ℝ)⁻¹ * ∑ m,
  RegularTransport.freeEnergy (R.displacement m) (R.potential m) p₀ p₁ s

def parameterForce : P := (M : ℝ)⁻¹ • ∑ m,
  ∫ z, (R.potential_gradient m z).fst ∂(R.law m : Measure Z)

def latentScore (m : Fin M) (z : Z) : Z :=
  (R.potential_gradient m z).snd +
    gradient (fun z ↦ Real.log ((R.displacement m).density 0 z)) z

def fisherInformation : ℝ := ‖R.parameterForce‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m,
  ∫ z, ‖R.latentScore m z‖ ^ 2 ∂(R.law m : Measure Z)

/-- Actual first variation pairing along the displayed displacement, before
taking its right lower derivative. -/
def directionalPairing : ℝ := (M : ℝ)⁻¹ * ∑ m,
  ((∫ z, inner ℝ (R.potential_gradient m z)
      (displacementField (R.displacement m) p₀ p₁ z) ∂(R.law m : Measure Z)) +
    ∫ z, inner ℝ ((R.displacement m).transport z - z)
      (gradient (fun z ↦ Real.log ((R.displacement m).density 0 z)) z)
        ∂(R.law m : Measure Z))

theorem latentScore_memLp (m : Fin M) : MemLp (R.latentScore m) 2 (R.law m : Measure Z) := by
  let _ := (R.law m).property
  exact (joint_snd_memLp (R.potential_gradient m) (R.potential_gradient_memLp m)).add
    (R.score_memLp m)

theorem directionalPairing_formula : R.directionalPairing =
    inner ℝ R.parameterForce (p₁ - p₀) + (M : ℝ)⁻¹ * ∑ m,
      ∫ z, inner ℝ (R.latentScore m z) ((R.displacement m).transport z - z)
        ∂(R.law m : Measure Z) := by
  have hpoint (m : Fin M) := tangent_pairing_eq (R.displacement m) p₀ p₁
    (R.potential_gradient m) (R.potential_gradient_memLp m)
    (R.displacement_memLp m) (R.score_memLp m)
  unfold directionalPairing
  simp_rw [hpoint]
  simp [parameterForce, latentScore, Finset.sum_add_distrib, mul_add,
    inner_smul_left, sum_inner]

/-- An actual difference quotient of the density free energy dominates its
score/parameter first variation. The proof does not postulate a derivative
formula for an integral. -/
theorem directionalPairing_le_slope (hrho : 0 ≤ rho)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    R.directionalPairing ≤ slope R.freeEnergy 0 s := by
  have hpoint (m : Fin M) : s * ((∫ z, inner ℝ (R.potential_gradient m z)
      (displacementField (R.displacement m) p₀ p₁ z) ∂(R.law m : Measure Z)) +
      ∫ z, inner ℝ ((R.displacement m).transport z - z)
        (gradient (fun z ↦ Real.log ((R.displacement m).density 0 z)) z)
          ∂(R.law m : Measure Z)) ≤
      RegularTransport.freeEnergy (R.displacement m) (R.potential m) p₀ p₁ s-
        RegularTransport.freeEnergy (R.displacement m) (R.potential m) p₀ p₁ 0 := by
    have h := freeEnergy_tangent_at (R.displacement m) (R.potential m) p₀ p₁ rho
      (R.potential_gradient m) (R.potential_strong m) (R.potential_hasGradientAt m)
      (R.potential_gradient_memLp m) (R.displacement_memLp m) (R.potential_measurable m)
      (R.potential_integrable_initial m) (R.density_C1 m) (R.integrable_tails m)
      s ⟨hs.1.le, hs.2⟩ (R.potential_integrable_path m s ⟨hs.1.le, hs.2⟩)
    have hn : 0 ≤ rho / 2 * s ^ 2 * (‖p₀ - p₁‖ ^ 2+
        (eLpNorm (fun z ↦ z - (R.displacement m).transport z) 2
          (R.law m : Measure Z)).toReal ^ 2) := by positivity
    linarith
  have hsum := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) ↦ hpoint m))
    (inv_nonneg.mpr (Nat.cast_nonneg M))
  have hscaled : s * R.directionalPairing ≤ R.freeEnergy s - R.freeEnergy 0 := by
    unfold directionalPairing freeEnergy
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    convert hsum using 1 <;> ring
  rw [slope_def_field]
  simp only [sub_zero]
  exact (le_div_iff₀ hs.1).mpr (by simpa only [mul_comm] using hscaled)

/-- The source lower directional derivative, expressed as the actual right
liminf in the extended reals. This remains meaningful before one proves that
the directional derivative is finite. -/
theorem lower_directional_liminf (hrho : 0 ≤ rho) :
    (R.directionalPairing : EReal) ≤
      Filter.liminf (fun s : ℝ ↦ (slope R.freeEnergy 0 s : EReal)) (𝓝[>] (0 : ℝ)) := by
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with s hs hs1
  exact_mod_cast R.directionalPairing_le_slope hrho s ⟨hs, hs1.le⟩

/-- Whenever the actual right derivative exists, its lower bound is the
computed score/parameter pairing. -/
theorem lower_directional_derivative (hrho : 0 ≤ rho) (derivative : ℝ)
    (hderiv : HasDerivWithinAt R.freeEnergy derivative (Ici 0) 0) :
    R.directionalPairing ≤ derivative := by
  have hlim : Tendsto (slope R.freeEnergy 0) (𝓝[>] 0) (𝓝 derivative) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp
      (hderiv.mono Ioi_subset_Ici_self)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with s hs hs1
  exact R.directionalPairing_le_slope hrho s ⟨hs, hs1.le⟩

/-- The source extended LSI with the exact normalized finite-data Fisher
information. The norm squares the averaged parameter force; it does not
average the squared parameter forces. -/
theorem extendedLSI (hM : 0 < M) (hrho : 0 < rho) :
    2 * rho * (R.freeEnergy 0 - R.freeEnergy 1) ≤ R.fisherInformation := by
  let g : Fin M → P := fun m ↦
    ∫ z, (R.potential_gradient m z).fst ∂(R.law m : Measure Z)
  let pair : Fin M → ℝ := fun m ↦
    ∫ z, inner ℝ (R.latentScore m z) ((R.displacement m).transport z - z)
      ∂(R.law m : Measure Z)
  let b : Fin M → ℝ := fun m ↦
    (eLpNorm (R.latentScore m) 2 (R.law m : Measure Z)).toReal
  let c : Fin M → ℝ := fun m ↦
    (eLpNorm (fun z ↦ z - (R.displacement m).transport z) 2 (R.law m : Measure Z)).toReal
  let gap : Fin M → ℝ := fun m ↦
    RegularTransport.freeEnergy (R.displacement m) (R.potential m) p₀ p₁ 0 -
      RegularTransport.freeEnergy (R.displacement m) (R.potential m) p₀ p₁ 1
  have htangent (m : Fin M) : gap m + inner ℝ (g m) (p₁ - p₀) + pair m+
      rho / 2 * (‖p₁ - p₀‖ ^ 2 + c m ^ 2) ≤ 0 := by
    let _ := (R.law m).property
    have ht := freeEnergy_tangent (R.displacement m) (R.potential m) p₀ p₁ rho
      (R.potential_gradient m) (R.potential_strong m) (R.potential_hasGradientAt m)
      (R.potential_gradient_memLp m) (R.displacement_memLp m) (R.potential_measurable m)
      (R.potential_integrable_initial m) (R.potential_integrable_final m)
      (R.density_C1 m) (R.integrable_tails m)
    have heq := tangent_pairing_eq (R.displacement m) p₀ p₁ (R.potential_gradient m)
      (R.potential_gradient_memLp m) (R.displacement_memLp m) (R.score_memLp m)
    rw [heq] at ht
    change inner ℝ (g m) (p₁ - p₀) + pair m+
      rho / 2 * (‖p₀ - p₁‖ ^ 2 + c m ^ 2) ≤ _ at ht
    rw [norm_sub_rev p₁ p₀]
    dsimp only [gap]
    linarith
  have hpair (m : Fin M) : -pair m ≤ b m * c m := by
    let _ := (R.law m).property
    let v : Z → Z := fun z ↦ (R.displacement m).transport z - z
    have hv : MemLp v 2 (R.law m : Measure Z) := by
      convert (R.displacement_memLp m).neg using 1
      funext z
      simp [v]
    have h := integral_inner_le_secondCost (R.law m : Measure Z)
      (-(R.latentScore m)) v (R.latentScore_memLp m).neg hv
    have hvnorm : eLpNorm v 2 (R.law m : Measure Z) =
        eLpNorm (fun z ↦ z - (R.displacement m).transport z) 2 (R.law m : Measure Z) := by
      calc
        eLpNorm v 2 (R.law m : Measure Z) =
            eLpNorm (-(fun z ↦ z - (R.displacement m).transport z)) 2
              (R.law m : Measure Z) := by
          congr 1
          funext z
          simp [v]
        _ = _ := eLpNorm_neg _ _ _
    simpa only [Pi.neg_apply, inner_neg_left, integral_neg, hvnorm, eLpNorm_neg] using h
  have h := normalized_extendedLSI_of_tangents hM rho hrho (p₁ - p₀) gap pair b c g
    htangent hpair
  have hsq (m : Fin M) : b m ^ 2 =
      ∫ z, ‖R.latentScore m z‖ ^ 2 ∂(R.law m : Measure Z) := by
    exact secondCost_sq_eq_integral _ _ (R.latentScore_memLp m)
  simp_rw [hsq] at h
  simpa only [freeEnergy, fisherInformation, parameterForce, gap, g,
    Finset.sum_sub_distrib, mul_sub] using h

/-- The paper's normalized optimizer/Wasserstein distance squared. Every
Wasserstein term is the infimum over actual couplings of actual laws. -/
def distanceSq : ℝ := ‖p₀ - p₁‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m,
  ULA.wasserstein2Real (R.law m : Measure Z) ((R.displacement m).law 1) ^ 2

theorem distanceSq_nonneg : 0 ≤ R.distanceSq := by
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by positivity)
    (Finset.sum_nonneg fun m _ ↦ sq_nonneg _))

/-- Full finite-data displacement strong convexity on the actual normalized
Euclidean/Wasserstein product. -/
theorem displacement_strongConvex (hM : 0 < M) (hrho : 0 ≤ rho)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    R.freeEnergy s ≤ (1 - s) * R.freeEnergy 0 + s * R.freeEnergy 1-
      rho / 2 * s * (1 - s) * R.distanceSq := by
  have hm : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hpoint (m : Fin M) := freeEnergy_displacement_strongConvex
    (R.displacement m) (R.potential m) p₀ p₁ rho hrho (R.potential_strong m)
    (R.potential_measurable m) (R.potential_integrable_path m)
    (R.displacement_memLp m) s hs
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun m (_ : m ∈ Finset.univ) ↦ hpoint m))
    (inv_nonneg.mpr (Nat.cast_nonneg M))
  change R.freeEnergy s ≤ _ at h
  apply h.trans_eq
  simp only [freeEnergy, distanceSq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The finite-data Talagrand bound at a free-energy minimizer is obtained
from the proved strong convexity. -/
theorem talagrand (hM : 0 < M) (hrho : 0 ≤ rho)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, R.freeEnergy 0 ≤ R.freeEnergy s) :
    rho / 2 * R.distanceSq ≤ R.freeEnergy 1 - R.freeEnergy 0 := by
  have h := SourceResults.geodesic_quadratic_growth R.freeEnergy (R.freeEnergy 1)
    rho (Real.sqrt R.distanceSq) hmin
    (by simpa only [Real.sq_sqrt R.distanceSq_nonneg] using
      R.displacement_strongConvex hM hrho)
  simpa only [Real.sq_sqrt R.distanceSq_nonneg] using h

/-- Talagrand with the endpoint law as optimizer, matching a flow-to-optimum
application of the first order and log Sobolev inequalities. -/
theorem talagrand_final (hM : 0 < M) (hrho : 0 ≤ rho)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, R.freeEnergy 1 ≤ R.freeEnergy s) :
    rho / 2 * R.distanceSq ≤ R.freeEnergy 0 - R.freeEnergy 1 := by
  have hmin' : ∀ s ∈ Icc (0 : ℝ) 1,
      (fun s ↦ R.freeEnergy (1 - s)) 0 ≤ (fun s ↦ R.freeEnergy (1 - s)) s := by
    intro s hs
    simpa using hmin (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hconv : ∀ s ∈ Icc (0 : ℝ) 1,
      R.freeEnergy (1 - s) ≤ (1 - s) * R.freeEnergy (1 - 0) + s * R.freeEnergy 0-
        rho / 2 * s * (1 - s) * (Real.sqrt R.distanceSq) ^ 2 := by
    intro s hs
    have h := R.displacement_strongConvex hM hrho (1 - s)
      ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rw [Real.sq_sqrt R.distanceSq_nonneg]
    simp only [sub_zero]
    convert h using 1
    ring
  have h := SourceResults.geodesic_quadratic_growth
    (fun s ↦ R.freeEnergy (1 - s)) (R.freeEnergy 0) rho
    (Real.sqrt R.distanceSq) hmin' hconv
  simpa only [Real.sq_sqrt R.distanceSq_nonneg, sub_zero] using h

end DatasetRegularity

end Dataset

end LatentDiffusion.RegularTransport
