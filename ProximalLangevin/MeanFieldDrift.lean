import ProximalLangevin.MYIPLA
import UnadjustedLangevin.TransportMoments
import UnadjustedLangevin.InitialExtension
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # The actual averaged parameter drift and quadratic transport

This is a corrected Wasserstein-2 version of Lemma C.1. The drift is the
actual Bochner integral of the parameter gradient. Finite second moments
justify every integral, and the transport bound is proved by taking the
infimum over all couplings. For split smoothing the constant is
`L₁ + 1/eta`, rather than the full-envelope constant `1/eta`.
-/

set_option linter.style.header false

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace ProximalLangevin

section ObservableTransport
variable {Ω E F : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F] in
/-- A Lipschitz observable with a nonzero offset still preserves finite
second moments on a probability space. -/
theorem memLp_lipschitz_observable (P : Measure Ω) [IsProbabilityMeasure P]
    {φ : E → F} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    {X : Ω → E} (hX : MemLp X 2 P) : MemLp (fun ω => φ (X ω)) 2 P := by
  have hcenter : LipschitzWith K (fun x => φ x - φ 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_eq_norm_sub, sub_sub_sub_cancel_right] using hφ.dist_le_mul x y
  have hc := hcenter.comp_memLp (by simp) hX
  convert hc.add (memLp_const (φ 0)) using 1
  funext ω
  simp only [Function.comp_def, Pi.add_apply, sub_add_cancel]

omit [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] in
/-- Actual expectations of a Lipschitz observable are Lipschitz in W₂.
Both input probability laws have finite second moment; infinity is never
removed by an unguarded real conversion. -/
theorem integral_lipschitz_wasserstein2
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : E => x) 2 μ) (hν : MemLp (fun x : E => x) 2 ν)
    {φ : E → F} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ‖(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν‖ ≤
      (K : ℝ) * ULA.wasserstein2Real μ ν := by
  have hfinite := ULA.wasserstein2_ne_top_of_memLp μ ν hμ hν
  have hfamily (c : ULA.Coupling μ ν) :
      ENNReal.ofReal ‖(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν‖ ≤
        (K : ℝ≥0∞) * ULA.couplingCost c.joint := by
    have : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
    have hfst : MemLp (fun p : E × E => p.1) 2 c.joint := by
      have hh : MemLp (fun x : E => x) 2 (c.joint.map Prod.fst) := by
        rw [c.fst]
        exact hμ
      exact hh.comp_of_map measurable_fst.aemeasurable
    have hsnd : MemLp (fun p : E × E => p.2) 2 c.joint := by
      have hh : MemLp (fun x : E => x) 2 (c.joint.map Prod.snd) := by
        rw [c.snd]
        exact hν
      exact hh.comp_of_map measurable_snd.aemeasurable
    have hφfst := memLp_lipschitz_observable c.joint hφ hfst
    have hφsnd := memLp_lipschitz_observable c.joint hφ hsnd
    have hD : MemLp (fun p : E × E => φ p.1 - φ p.2) 2 c.joint := hφfst.sub hφsnd
    have hiF := hφfst.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hiS := hφsnd.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hiD := hD.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hid : (∫ x, φ x ∂μ) - ∫ x, φ x ∂ν =
        ∫ p, φ p.1 - φ p.2 ∂c.joint := by
      have hf := integral_map (μ := c.joint) (φ := Prod.fst)
        measurable_fst.aemeasurable hφ.continuous.aestronglyMeasurable
      have hs := integral_map (μ := c.joint) (φ := Prod.snd)
        measurable_snd.aemeasurable hφ.continuous.aestronglyMeasurable
      rw [c.fst] at hf
      rw [c.snd] at hs
      rw [hf, hs, integral_sub hiF hiS]
    rw [hid]
    calc
      _ ≤ ENNReal.ofReal (∫ p, ‖φ p.1 - φ p.2‖ ∂c.joint) :=
        ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
      _ = eLpNorm (fun p : E × E => φ p.1 - φ p.2) 1 c.joint := by
        rw [ofReal_integral_norm_eq_lintegral_enorm hiD,
          eLpNorm_one_eq_lintegral_enorm hD.aestronglyMeasurable]
      _ ≤ eLpNorm (fun p : E × E => φ p.1 - φ p.2) 2 c.joint :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      _ ≤ (K : ℝ≥0∞) * ULA.couplingCost c.joint := by
        simpa only [ENNReal.smul_def, smul_eq_mul, ULA.couplingCost] using
          eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hD.aestronglyMeasurable
            (ae_of_all _ fun p => by exact_mod_cast hφ.norm_sub_le p.1 p.2) 2
  have hbound : ENNReal.ofReal ‖(∫ x, φ x ∂μ) - ∫ x, φ x ∂ν‖ ≤
      (K : ℝ≥0∞) * ULA.wasserstein2 μ ν := by
    obtain ⟨c₀, _⟩ := ULA.exists_finiteCost_coupling μ ν hfinite
    have : Nonempty (ULA.Coupling μ ν) := ⟨c₀⟩
    unfold ULA.wasserstein2
    rw [ENNReal.mul_iInf (fun h => (ENNReal.coe_ne_top h).elim)]
    exact le_iInf hfamily
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinite) hbound
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_mul,
    ENNReal.coe_toReal, ULA.wasserstein2Real] using hr

end ObservableTransport

/-- The parameter block of a parameter/latent joint vector. -/
def jointParameterCLM {dθ dx : ℕ} :
    IPLA.Joint dθ dx →L[ℝ] EuclideanSpace ℝ (Fin dθ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 (fun j => z (Sum.inl j))
      map_add' := by intro x y; ext j; rfl
      map_smul' := by intro a x; ext j; rfl }

@[simp] theorem jointParameterCLM_apply {dθ dx : ℕ} (z : IPLA.Joint dθ dx)
    (j : Fin dθ) : jointParameterCLM z j = z (Sum.inl j) := rfl

theorem norm_jointParameterCLM_apply_le {dθ dx : ℕ} (z : IPLA.Joint dθ dx) :
    ‖jointParameterCLM z‖ ≤ ‖z‖ := by
  have hs : ‖jointParameterCLM z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, jointParameterCLM_apply,
      Fintype.sum_sum_type]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)
  nlinarith [norm_nonneg (jointParameterCLM z), norm_nonneg z]

/-- The parameter component of the actual joint gradient. -/
def parameterGradient {dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ)
    (θ : EuclideanSpace ℝ (Fin dθ)) (x : EuclideanSpace ℝ (Fin dx)) :
    EuclideanSpace ℝ (Fin dθ) := jointParameterCLM (gradient U (IPLA.pair θ x))

/-- The actual averaged parameter drift, as a Bochner integral. -/
def meanFieldDrift {dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ)
    (θ : EuclideanSpace ℝ (Fin dθ)) (ν : Measure (EuclideanSpace ℝ (Fin dx))) :
    EuclideanSpace ℝ (Fin dθ) := ∫ x, parameterGradient U θ x ∂ν

theorem pair_norm_sub_le {dθ dx : ℕ}
    (θ θ' : EuclideanSpace ℝ (Fin dθ)) (x x' : EuclideanSpace ℝ (Fin dx)) :
    ‖IPLA.pair θ x - IPLA.pair θ' x'‖ ≤ ‖θ - θ'‖ + ‖x - x'‖ := by
  have hid : IPLA.pair θ x - IPLA.pair θ' x' = IPLA.pair (θ - θ') (x - x') := by
    ext a
    cases a <;> rfl
  rw [hid]
  have hs := IPLA.norm_pair_sq (θ - θ') (x - x')
  nlinarith [norm_nonneg (IPLA.pair (θ - θ') (x - x')),
    norm_nonneg (θ - θ'), norm_nonneg (x - x'),
    mul_nonneg (norm_nonneg (θ - θ')) (norm_nonneg (x - x'))]

theorem parameterGradient_difference_le {dθ dx : ℕ}
    {U : IPLA.Joint dθ dx → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L (gradient U))
    (θ θ' : EuclideanSpace ℝ (Fin dθ)) (x x' : EuclideanSpace ℝ (Fin dx)) :
    ‖parameterGradient U θ x - parameterGradient U θ' x'‖ ≤
      (L : ℝ) * (‖θ - θ'‖ + ‖x - x'‖) := by
  calc
    _ = ‖jointParameterCLM (gradient U (IPLA.pair θ x) - gradient U (IPLA.pair θ' x'))‖ := by
      simp only [map_sub, parameterGradient]
    _ ≤ ‖gradient U (IPLA.pair θ x) - gradient U (IPLA.pair θ' x')‖ :=
      norm_jointParameterCLM_apply_le _
    _ ≤ (L : ℝ) * ‖IPLA.pair θ x - IPLA.pair θ' x'‖ := hLip.norm_sub_le _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (pair_norm_sub_le θ θ' x x') L.coe_nonneg

theorem parameterGradient_latent_lipschitz {dθ dx : ℕ}
    {U : IPLA.Joint dθ dx → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L (gradient U))
    (θ : EuclideanSpace ℝ (Fin dθ)) : LipschitzWith L (parameterGradient U θ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm_sub, sub_self, norm_zero, zero_add] using
    parameterGradient_difference_le hLip θ θ x y

/-- Corrected W₂ version of Lemma C.1 for an actual gradient-Lipschitz
joint potential and actual finite-second-moment latent probability laws. -/
theorem meanFieldDrift_lipschitz_wasserstein2 {dθ dx : ℕ}
    {U : IPLA.Joint dθ dx → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L (gradient U))
    (θ θ' : EuclideanSpace ℝ (Fin dθ))
    (μ ν : Measure (EuclideanSpace ℝ (Fin dx)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x => x) 2 μ) (hν : MemLp (fun x => x) 2 ν) :
    ‖meanFieldDrift U θ μ - meanFieldDrift U θ' ν‖ ≤
      (L : ℝ) * (‖θ - θ'‖ + ULA.wasserstein2Real μ ν) := by
  have hφ := parameterGradient_latent_lipschitz hLip θ
  have hφ' := parameterGradient_latent_lipschitz hLip θ'
  have hi := (memLp_lipschitz_observable μ hφ hμ).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi' := (memLp_lipschitz_observable μ hφ' hμ).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hθ : ‖meanFieldDrift U θ μ - meanFieldDrift U θ' μ‖ ≤ (L : ℝ) * ‖θ - θ'‖ := by
    unfold meanFieldDrift
    rw [← integral_sub hi hi']
    have hh := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => parameterGradient U θ x - parameterGradient U θ' x)
      (C := (L : ℝ) * ‖θ - θ'‖) (ae_of_all _ fun x => by
        simpa only [sub_self, norm_zero, add_zero] using
          parameterGradient_difference_le hLip θ θ' x x)
    simpa using hh
  have hν := integral_lipschitz_wasserstein2 μ ν hμ hν hφ'
  calc
    _ ≤ ‖meanFieldDrift U θ μ - meanFieldDrift U θ' μ‖ +
        ‖meanFieldDrift U θ' μ - meanFieldDrift U θ' ν‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (meanFieldDrift U θ μ) (meanFieldDrift U θ' μ) (meanFieldDrift U θ' ν)
    _ ≤ (L : ℝ) * ‖θ - θ'‖ + (L : ℝ) * ULA.wasserstein2Real μ ν := add_le_add hθ hν
    _ = _ := by ring

/-- For split Moreau smoothing, the actual averaged drift has coefficient
`L₁+1/eta`; the finite moments and all integral guards remain explicit. -/
theorem moreau_meanFieldDrift_lipschitz_wasserstein2 {dθ dx : ℕ}
    {g₁ g₂ : IPLA.Joint dθ dx → ℝ} {L₁ : ℝ≥0} {eta : ℝ}
    (hg₁ : Differentiable ℝ g₁) (hLip₁ : LipschitzWith L₁ (gradient g₁))
    (hg₂ : ConvexOn ℝ univ g₂) (hb : ∃ b, ∀ z, b ≤ g₂ z) (heta : 0 < eta)
    (θ θ' : EuclideanSpace ℝ (Fin dθ))
    (μ ν : Measure (EuclideanSpace ℝ (Fin dx)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x => x) 2 μ) (hν : MemLp (fun x => x) 2 ν) :
    ‖meanFieldDrift (smoothedPotential g₁ g₂ eta) θ μ -
      meanFieldDrift (smoothedPotential g₁ g₂ eta) θ' ν‖ ≤
      ((L₁ : ℝ) + eta⁻¹) * (‖θ - θ'‖ + ULA.wasserstein2Real μ ν) := by
  have he := moreau_differentiable hg₂ hb heta
  have hg : gradient (moreau g₂ eta) = residual g₂ eta := funext (gradient_moreau hg₂ hb heta)
  have hLipe : LipschitzWith eta.toNNReal⁻¹ (gradient (moreau g₂ eta)) := by
    rw [hg]
    simpa only [Real.toNNReal_inv] using residual_lipschitz hg₂ hb heta
  have h := meanFieldDrift_lipschitz_wasserstein2
    (smoothed_gradient_lipschitz hg₁ he hLip₁ hLipe) θ θ' μ ν hμ hν
  change ‖meanFieldDrift (smoothedPotential g₁ g₂ eta) θ μ -
    meanFieldDrift (smoothedPotential g₁ g₂ eta) θ' ν‖ ≤
    (smoothingLipschitz L₁ eta : ℝ) * (‖θ - θ'‖ + ULA.wasserstein2Real μ ν) at h
  rw [smoothingLipschitz_coe L₁ heta] at h
  exact h

end ProximalLangevin
