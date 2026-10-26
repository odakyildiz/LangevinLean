import LatentDiffusion.RegularFlowCalculus
import LatentDiffusion.RegularTransport
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-! # Actual first directional variation without a convexity assumption

Local dominated differentiation and the actual continuity equation compute the
free-energy derivative of a regular displacement path. No strong-convexity,
geodesic-convexity, first-order inequality or prescribed energy derivative is
assumed. The right-liminf bound follows from the computed actual derivative.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace LatentDiffusion.RegularDirectional

open RegularFlowCalculus RegularTransport

variable {A Z : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [CompleteSpace A] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [CompleteSpace Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]
  [BorelSpace Z] [SecondCountableTopology Z] {M d : ℕ}
  (μ : Fin M → Measure Z) [∀ i, IsProbabilityMeasure (μ i)]

theorem parameter_affine_hasDerivAt (a b : A) (s : ℝ) :
    HasDerivAt (parameterInterpolate a b) (b-a) s := by
  have h := (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).smul_const a).add
    ((hasDerivAt_id s).smul_const b)
  convert h using 1
  · funext t
    simp [parameterInterpolate, sub_eq_add_neg, add_comm]
  · simp [sub_eq_add_neg, add_comm]

/-- Primitive regularity of an actual displacement density path. The only
equation involving its derivative is the continuity equation at the initial
time; no scalar energy derivative or lower bound is an assumption. -/
structure DirectionalRegularity
    (D : (i : Fin M) → RegularDisplacement volume (μ i) d)
    (U : Fin M → A → Z → ℝ) (a b : A) where
  densityDerivative : Fin M → ℝ → Z → ℝ
  domination : ∀ i, LocalEnergyDomination volume (D i).density (densityDerivative i)
    (fun s ↦ U i (parameterInterpolate a b s))
    (fun s z ↦ fderiv ℝ (fun p ↦ U i p z) (parameterInterpolate a b s) (b-a)) 0
  parameter_differentiable : ∀ i z p, DifferentiableAt ℝ (fun v ↦ U i v z) p
  density_C1 : ∀ i, ContDiff ℝ 1 ((D i).density 0)
  potential_C1 : ∀ i, ContDiff ℝ 1 (U i a)
  parameter_gradient_integrable : ∀ i, Integrable
    (fun z ↦ (D i).density 0 z • gradient (fun p ↦ U i p z) a) volume
  continuity : ∀ i, ∀ᵐ z ∂volume, densityDerivative i 0 z =
    -fluxDivergence (fun w ↦ (D i).density 0 w • ((D i).transport w-w)) z
  integrable_tails : ∀ i, NoBoundaryFlux
    (fun z ↦ (D i).density 0 z • ((D i).transport z-z))
    (fun z ↦ chemicalPotential ((D i).density 0) (U i a) z + 1)
  potential_integrable : ∀ i s, s ∈ Icc (0 : ℝ) 1 →
    Integrable (U i (parameterInterpolate a b s)) ((D i).law s)

variable {μ} {D : (i : Fin M) → RegularDisplacement volume (μ i) d}
  {U : Fin M → A → Z → ℝ} {a b : A} (R : DirectionalRegularity μ D U a b)

def densityEnergy (s : ℝ) : ℝ :=
  normalizedDensityEnergy volume (fun i ↦ (D i).density s) U (parameterInterpolate a b s)

def lawEnergy (s : ℝ) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i, RegularTransport.freeEnergy (D i) (U i) a b s

def pairing : ℝ := normalizedProductGradientPairing volume
  (fun i ↦ (D i).density 0) U a (b-a) (fun i z ↦ (D i).transport z-z)

/-- The same source pairing written with actual initial probability laws. -/
def lawPairing : ℝ :=
  inner ℝ (b-a) ((M : ℝ)⁻¹ • ∑ i,
    ∫ z, gradient (fun p ↦ U i p z) a ∂μ i) +
  (M : ℝ)⁻¹ * ∑ i, ∫ z, inner ℝ ((D i).transport z-z)
    (gradient (chemicalPotential ((D i).density 0) (U i a)) z) ∂μ i

theorem initial_law_integral {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (i : Fin M) (f : Z → H) :
    (∫ z, f z ∂μ i) = ∫ z, (D i).density 0 z • f z ∂volume := by
  have hs : (0 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have hlaw := (D i).density_law 0 hs
  simp only [interpolate_zero, Measure.map_id] at hlaw
  calc
    _ = ∫ z, f z ∂volume.withDensity (fun z ↦ ENNReal.ofReal ((D i).density 0 z)) :=
      congrArg (fun ν : Measure Z ↦ ∫ z, f z ∂ν) hlaw
    _ = _ := by
      rw [integral_withDensity_eq_integral_toReal_smul
        ((D i).measurable_density 0 hs).ennreal_ofReal
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal ((D i).positive_density 0 hs _).le]

theorem pairing_eq_lawPairing : pairing (D := D) (U := U) (a := a) (b := b) =
    lawPairing (D := D) (U := U) (a := a) (b := b) := by
  unfold pairing lawPairing normalizedProductGradientPairing averagedParameterForce parameterForce
  simp_rw [initial_law_integral (D := D), smul_eq_mul]

include R

/-- The actual normalized density energy has the source gradient pairing as
its computed derivative. This stronger equality requires no A3 assumption. -/
theorem densityEnergy_hasDerivAt : HasDerivAt (densityEnergy (D := D) (U := U) (a := a) (b := b))
    (pairing (D := D) (U := U) (a := a) (b := b)) 0 := by
  have h := normalized_product_gradient_representation
    (fun i ↦ (D i).density) R.densityDerivative U (parameterInterpolate a b)
    (fun _ ↦ b-a) 0 (fun i z ↦ (D i).transport z-z) R.domination
    (parameter_affine_hasDerivAt a b) R.parameter_differentiable
    (fun i ↦ (D i).positive_density 0 (by constructor <;> norm_num))
    R.density_C1
    (by simpa only [parameterInterpolate, sub_zero, one_smul, zero_smul, add_zero] using
      R.potential_C1)
    (by simpa only [parameterInterpolate, sub_zero, one_smul, zero_smul, add_zero] using
      R.parameter_gradient_integrable)
    R.continuity
    (by simpa only [parameterInterpolate, sub_zero, one_smul, zero_smul, add_zero] using
      R.integrable_tails)
  change HasDerivAt (fun s ↦ normalizedDensityEnergy volume (fun i ↦ (D i).density s)
    U (parameterInterpolate a b s)) _ 0
  simpa only [pairing, parameterInterpolate, sub_zero,
    one_smul, zero_smul, add_zero] using h

theorem lawEnergy_eq_densityEnergy (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    lawEnergy (D := D) (U := U) (a := a) (b := b) s =
      densityEnergy (D := D) (U := U) (a := a) (b := b) s := by
  unfold lawEnergy densityEnergy normalizedDensityEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hlog : Integrable (fun z ↦ Real.log ((D i).density s z)) ((D i).law s) := by
    apply (integrable_map_measure
      ((Real.measurable_log.comp ((D i).measurable_density s hs)).aestronglyMeasurable)
      (interpolate_measurable _ (D i).measurable_transport s).aemeasurable).mpr
    simpa only [Function.comp_def] using (D i).integrable_log s hs
  unfold RegularTransport.freeEnergy RegularDisplacement.entropy SourceCalculus.densityFreeEnergy
  rw [← integral_add hlog (R.potential_integrable i s hs)]
  change (∫ z, Real.log ((D i).density s z) + U i (parameterInterpolate a b s) z
    ∂(μ i).map (interpolate (D i).transport s)) = _
  rw [(D i).density_law s hs]
  rw [integral_withDensity_eq_integral_toReal_smul
    ((D i).measurable_density s hs).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal ((D i).positive_density s hs _).le, smul_eq_mul]

/-- The actual probability-law displacement energy has the computed right
derivative, obtained from its proved identity with the literal density integral. -/
theorem lawEnergy_hasDerivWithinAt :
    HasDerivWithinAt (lawEnergy (D := D) (U := U) (a := a) (b := b))
      (pairing (D := D) (U := U) (a := a) (b := b)) (Ici 0) 0 := by
  have hnear : lawEnergy (D := D) (U := U) (a := a) (b := b) =ᶠ[𝓝[Ici 0] 0]
      densityEnergy (D := D) (U := U) (a := a) (b := b) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with s hs hs1
    exact lawEnergy_eq_densityEnergy R s ⟨hs, hs1.le⟩
  exact (densityEnergy_hasDerivAt R).hasDerivWithinAt.congr_of_eventuallyEq hnear
    (lawEnergy_eq_densityEnergy R 0 (by constructor <;> norm_num))

/-- The source lower right-liminf bound for the actual normalized law energy,
with no joint-convexity assumption. In this dominated regular class the liminf
actually equals the computed first variation. -/
theorem lower_directional_liminf :
    (pairing (D := D) (U := U) (a := a) (b := b) : EReal) ≤
      Filter.liminf (fun s : ℝ ↦
        (slope (lawEnergy (D := D) (U := U) (a := a) (b := b)) 0 s : EReal)) (𝓝[>] 0) := by
  have hlim : Tendsto (slope (lawEnergy (D := D) (U := U) (a := a) (b := b)) 0)
      (𝓝[>] 0) (𝓝 (pairing (D := D) (U := U) (a := a) (b := b))) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp
      ((lawEnergy_hasDerivWithinAt R).mono Ioi_subset_Ici_self)
  have h := (continuous_coe_real_ereal.tendsto _ |>.comp hlim).liminf_eq
  exact h.symm.le

/-- Literal source form: actual law free energy and actual law-integrated
parameter/score pairing, without any strong-convexity assumption. -/
theorem lower_directional_liminf_law_pairing :
    (lawPairing (D := D) (U := U) (a := a) (b := b) : EReal) ≤
      Filter.liminf (fun s : ℝ ↦
        (slope (lawEnergy (D := D) (U := U) (a := a) (b := b)) 0 s : EReal)) (𝓝[>] 0) := by
  rw [← pairing_eq_lawPairing]
  exact lower_directional_liminf R

end LatentDiffusion.RegularDirectional
