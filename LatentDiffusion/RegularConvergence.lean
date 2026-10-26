import LatentDiffusion.RegularTransportFirstOrder
import LatentDiffusion.RegularModel
import Mathlib.Analysis.ODE.Gronwall

/-! # Convergence from the classical equations and regular transport

The fields of `ClassicalFlow` are density, differentiability, domination,
transport and boundary integrability data. Energy dissipation and extended
LSI are proved below from those data; neither is a field of the structure.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal

namespace LatentDiffusion.RegularConvergence

variable {A Z : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [FiniteDimensional ℝ Z] {M d : ℕ}

open RegularTransport RegularFlowCalculus

theorem integral_density {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (q : Z → ℝ) (hq : Measurable q) (hpos : ∀ z, 0 ≤ q z) (f : Z → H) :
    (∫ z, f z ∂(volume.withDensity (fun z ↦ ENNReal.ofReal (q z)))) =
      ∫ z, q z • f z := by
  rw [integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hpos _)]

/-- Gibbs variational lower bound for every positive regular density law.
The proof integrates `log x ≤ x-1`; no KL identity is a premise. -/
theorem gibbs_variational_lower_bound (Q : ProbabilityMeasure Z) (q V : Z → ℝ)
    (hq : Measurable q) (hpos : ∀ z, 0 < q z)
    (hlaw : (Q : Measure Z) = volume.withDensity (fun z ↦ ENNReal.ofReal (q z)))
    (hweight : Integrable (fun z ↦ Real.exp (-V z)) volume)
    (hZ : 0 < ∫ z, Real.exp (-V z))
    (hlog : Integrable (fun z ↦ Real.log (q z)) (Q : Measure Z))
    (hV : Integrable V (Q : Measure Z)) :
    -(Real.log (∫ z, Real.exp (-V z))) ≤
      (∫ z, Real.log (q z) ∂(Q : Measure Z)) + ∫ z, V z ∂(Q : Measure Z) := by
  let Z0 := ∫ z, Real.exp (-V z)
  let r : Z → ℝ := fun z ↦ (Real.exp (-V z)/Z0)/q z
  have hprod : (fun z ↦ q z * r z) = fun z ↦ Real.exp (-V z)/Z0 := by
    funext z
    dsimp only [r]
    field_simp [(hpos z).ne']
  have hr : Integrable r (Q : Measure Z) := by
    rw [hlaw, integrable_withDensity_iff_integrable_smul' hq.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul, hprod] using
      hweight.div_const Z0
  have hrint : (∫ z, r z ∂(Q : Measure Z)) = 1 := by
    rw [hlaw, integral_density q hq (fun z ↦ (hpos z).le)]
    simp only [smul_eq_mul, hprod]
    rw [integral_div]
    exact div_self hZ.ne'
  have hpoint (z : Z) : 1-r z ≤ Real.log (q z)+V z+Real.log Z0 := by
    have hz : 0 < Real.exp (-V z)/Z0 := div_pos (Real.exp_pos _) hZ
    have hh := Real.log_le_sub_one_of_pos (div_pos hz (hpos z))
    rw [Real.log_div hz.ne' (hpos z).ne', Real.log_div (Real.exp_ne_zero _) hZ.ne',
      Real.log_exp] at hh
    dsimp only [r]
    linarith
  have hbound := integral_mono ((integrable_const (1 : ℝ)).sub hr)
    ((hlog.add hV).add (integrable_const (Real.log Z0))) hpoint
  have ha := integral_add' (hlog.add hV) (integrable_const (Real.log Z0))
  have hb := integral_add' hlog hV
  simp only [Pi.add_apply] at ha hb
  simp only [Pi.sub_apply, Pi.add_apply] at hbound
  rw [integral_sub (integrable_const (1 : ℝ)) hr, hrint,
    ha, hb] at hbound
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hbound
  dsimp only [Z0] at hbound
  linarith

namespace RegularDataset

variable {rho : ℝ} {a b : A} (R : DatasetRegularity (Z := Z) M d a b rho)

theorem log_integrable (i : Fin M) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z ↦ Real.log ((R.displacement i).density s z))
      ((R.displacement i).law s) := by
  let D := R.displacement i
  apply (integrable_map_measure
    ((Real.measurable_log.comp (D.measurable_density s hs)).aestronglyMeasurable)
    (interpolate_measurable _ D.measurable_transport s).aemeasurable).mpr
  simpa only [Function.comp_def] using D.integrable_log s hs

theorem potential_integrable (i : Fin M) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    Integrable (R.potential i (parameterInterpolate a b s)) ((R.displacement i).law s) := by
  apply (integrable_map_measure
    (R.potential_measurable i _).aestronglyMeasurable
    (interpolate_measurable _ (R.displacement i).measurable_transport s).aemeasurable).mpr
  simpa only [Function.comp_def] using R.potential_integrable_path i s hs

def evidence (p : A) : ℝ := (M : ℝ)⁻¹ * ∑ i,
  Real.log (∫ z, Real.exp (-R.potential i p z))

theorem energy_lower_bound
    (hweight : ∀ i p, Integrable (fun z ↦ Real.exp (-R.potential i p z)) volume)
    (hZ : ∀ i p, 0 < ∫ z, Real.exp (-R.potential i p z))
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    -evidence R (parameterInterpolate a b s) ≤ R.freeEnergy s := by
  have hi (i : Fin M) :
      -(Real.log (∫ z, Real.exp (-R.potential i (parameterInterpolate a b s) z))) ≤
        RegularTransport.freeEnergy (R.displacement i) (R.potential i) a b s := by
    let _ := (R.law i).property
    let Q : ProbabilityMeasure Z := ⟨(R.displacement i).law s, inferInstance⟩
    exact gibbs_variational_lower_bound Q ((R.displacement i).density s)
      (R.potential i (parameterInterpolate a b s))
      ((R.displacement i).measurable_density s hs)
      ((R.displacement i).positive_density s hs)
      ((R.displacement i).density_law s hs) (hweight i _) (hZ i _)
      (log_integrable R i s hs) (potential_integrable R i s hs)
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hi i)
    (inv_nonneg.mpr (Nat.cast_nonneg M))
  simpa only [evidence, DatasetRegularity.freeEnergy, Finset.sum_neg_distrib, mul_neg] using hh

theorem posterior_energy
    (hZ : ∀ i, 0 < ∫ z, Real.exp (-R.potential i b z))
    (hpost : ∀ i z, (R.displacement i).density 1 z =
      Real.exp (-R.potential i b z)/(∫ w, Real.exp (-R.potential i b w))) :
    R.freeEnergy 1 = -evidence R b := by
  have hi (i : Fin M) :
      RegularTransport.freeEnergy (R.displacement i) (R.potential i) a b 1 =
        -Real.log (∫ z, Real.exp (-R.potential i b z)) := by
    let _ := (R.law i).property
    have hs : (1 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
    have hlog := log_integrable R i 1 hs
    have hpot := potential_integrable R i 1 hs
    simp only [parameterInterpolate, sub_self, zero_smul, one_smul, zero_add] at hpot
    unfold RegularTransport.freeEnergy RegularDisplacement.entropy
    simp only [parameterInterpolate, sub_self, zero_smul, one_smul, zero_add]
    rw [← integral_add hlog hpot]
    have hp : (fun z ↦ Real.log ((R.displacement i).density 1 z)+R.potential i b z) =
        fun _ ↦ -Real.log (∫ z, Real.exp (-R.potential i b z)) := by
      funext z
      rw [hpost, Real.log_div (Real.exp_ne_zero _) (hZ i).ne', Real.log_exp]
      ring
    rw [hp]
    simp
  simp only [DatasetRegularity.freeEnergy, hi, evidence, Finset.sum_neg_distrib, mul_neg]

theorem posterior_minimal
    (hweight : ∀ i p, Integrable (fun z ↦ Real.exp (-R.potential i p z)) volume)
    (hZ : ∀ i p, 0 < ∫ z, Real.exp (-R.potential i p z))
    (hmax : ∀ p, evidence R p ≤ evidence R b)
    (hpost : ∀ i z, (R.displacement i).density 1 z =
      Real.exp (-R.potential i b z)/(∫ w, Real.exp (-R.potential i b w))) :
    ∀ s ∈ Icc (0 : ℝ) 1, R.freeEnergy 1 ≤ R.freeEnergy s := by
  intro s hs
  rw [posterior_energy R (fun i ↦ hZ i b) hpost]
  exact (neg_le_neg (hmax _)).trans (energy_lower_bound R hweight hZ s hs)

end RegularDataset

/-- A regular classical solution of the actual normalized parameter ODE and
Fokker–Planck PDE, together with regular transports to the fixed comparison
state. The potential gradients are actual Fréchet gradients, not inequalities.
-/
structure ClassicalFlow (M d : ℕ) (rho : ℝ) (astar : A)
    (U : Fin M → A → Z → ℝ) where
  parameter : ℝ → A
  parameterDerivative : ℝ → A
  density : Fin M → ℝ → Z → ℝ
  densityDerivative : Fin M → ℝ → Z → ℝ
  targetDensity : Fin M → Z → ℝ
  transport : (t : ℝ) → DatasetRegularity (Z := Z) M d (parameter t) astar rho
  potential_eq : ∀ t, (transport t).potential = U
  density_eq : ∀ t i, ((transport t).displacement i).density 0 = density i t
  target_density_eq : ∀ t i, ((transport t).displacement i).density 1 = targetDensity i
  parameter_differentiable : ∀ t, HasDerivAt parameter (parameterDerivative t) t
  potential_parameter_differentiable : ∀ i z a, DifferentiableAt ℝ (fun b ↦ U i b z) a
  positive : ∀ i t z, 0 < density i t z
  density_C1 : ∀ i t, ContDiff ℝ 1 (density i t)
  potential_C1 : ∀ i t, ContDiff ℝ 1 (U i (parameter t))
  parameter_gradient : ∀ t i z, HasGradientAt (fun a ↦ U i a z)
    (((transport t).potential_gradient i z).fst) (parameter t)
  latent_gradient : ∀ t i z, HasGradientAt (U i (parameter t))
    (((transport t).potential_gradient i z).snd) z
  parameter_gradient_integrable : ∀ t i,
    Integrable (fun z ↦ density i t z • gradient (fun a ↦ U i a z) (parameter t)) volume
  domination : ∀ t i, LocalEnergyDomination volume (density i) (densityDerivative i)
    (fun u ↦ U i (parameter u))
    (fun u z ↦ fderiv ℝ (fun a ↦ U i a z) (parameter u) (parameterDerivative u)) t
  parameter_equation : ∀ t, 0 ≤ t → parameterDerivative t =
    -averagedParameterForce volume (fun i ↦ density i t) U (parameter t)
  density_equation : ∀ t, 0 ≤ t → ∀ i, ∀ᵐ z ∂volume, densityDerivative i t z =
    fluxDivergence (fokkerPlanckFlux (density i t) (U i (parameter t))) z
  integrable_tails : ∀ t i, NoBoundaryFlux
    (fokkerPlanckFlux (density i t) (U i (parameter t)))
    (fun z ↦ chemicalPotential (density i t) (U i (parameter t)) z + 1)

namespace ClassicalFlow

variable {rho : ℝ} {astar : A} {U : Fin M → A → Z → ℝ}
  (S : ClassicalFlow M d rho astar U)

def energy (t : ℝ) : ℝ :=
  normalizedDensityEnergy volume (fun i ↦ S.density i t) U (S.parameter t)

def fisher (t : ℝ) : ℝ :=
  normalizedSlopeSquared volume (fun i ↦ S.density i t) U (S.parameter t)

def targetEnergy : ℝ := normalizedDensityEnergy volume S.targetDensity U astar

def evidence (_S : ClassicalFlow M d rho astar U) (a : A) : ℝ := (M : ℝ)⁻¹ * ∑ i,
  Real.log (∫ z, Real.exp (-U i a z))

theorem initial_energy (t : ℝ) : (S.transport t).freeEnergy 0 = S.energy t := by
  unfold DatasetRegularity.freeEnergy energy normalizedDensityEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let D := (S.transport t).displacement i
  have hden := D.initial_density_law
  rw [S.density_eq t i] at hden
  have hq := (S.density_C1 i t).continuous.measurable
  have hpos := fun z ↦ (S.positive i t z).le
  have hlog : Integrable (fun z ↦ Real.log (S.density i t z))
      ((S.transport t).law i : Measure Z) := by
    simpa only [D, interpolate_zero, id_eq, S.density_eq t i] using
      D.integrable_log 0 (by constructor <;> norm_num)
  have hU : Integrable (U i (S.parameter t)) ((S.transport t).law i : Measure Z) := by
    simpa only [S.potential_eq t] using (S.transport t).potential_integrable_initial i
  unfold RegularTransport.freeEnergy RegularDisplacement.entropy
  simp only [RegularDisplacement.law_zero, parameterInterpolate, sub_zero, one_smul,
    zero_smul, add_zero,
    S.potential_eq t, S.density_eq t i]
  rw [← integral_add hlog hU, hden, integral_density _ hq hpos]
  rfl

theorem terminal_energy (t : ℝ) : (S.transport t).freeEnergy 1 = S.targetEnergy := by
  borelize Z
  unfold DatasetRegularity.freeEnergy targetEnergy normalizedDensityEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let D := (S.transport t).displacement i
  have hs : (1 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
  have hlaw : D.law 1 = volume.withDensity (fun z ↦ ENNReal.ofReal (S.targetDensity i z)) := by
    simpa only [D, RegularDisplacement.law, S.target_density_eq t i] using D.density_law 1 hs
  have hq : Measurable (S.targetDensity i) := by
    simpa only [D, S.target_density_eq t i] using D.measurable_density 1 hs
  have hpos : ∀ z, 0 ≤ S.targetDensity i z := by
    intro z
    simpa only [D, S.target_density_eq t i] using (D.positive_density 1 hs z).le
  have hlog : Integrable (fun z ↦ Real.log (S.targetDensity i z)) (D.law 1) := by
    have hm : AEStronglyMeasurable (fun z ↦ Real.log (S.targetDensity i z)) (D.law 1) :=
      (Real.measurable_log.comp hq).aestronglyMeasurable
    apply (integrable_map_measure hm (interpolate_measurable _ D.measurable_transport 1).aemeasurable).mpr
    simpa only [D, interpolate_one, Function.comp_def, S.target_density_eq t i,
      measureSpaceOfInnerProductSpace] using D.integrable_log 1 hs
  have hU : Integrable (U i astar) (D.law 1) := by
    apply (integrable_map_measure
      (by simpa only [S.potential_eq t] using ((S.transport t).potential_measurable i astar).aestronglyMeasurable)
      (interpolate_measurable _ D.measurable_transport 1).aemeasurable).mpr
    simpa only [D, interpolate_one, Function.comp_def, S.potential_eq t,
      measureSpaceOfInnerProductSpace] using (S.transport t).potential_integrable_final i
  unfold RegularTransport.freeEnergy RegularDisplacement.entropy
  simp only [parameterInterpolate, sub_self, zero_smul, one_smul, zero_add,
    S.potential_eq t, S.target_density_eq t i]
  rw [← integral_add hlog hU, hlaw, integral_density _ hq hpos]
  rfl

theorem terminal_law (t : ℝ) (i : Fin M) :
    ((S.transport t).displacement i).law 1 =
      volume.withDensity (fun z ↦ ENNReal.ofReal (S.targetDensity i z)) := by
  simpa only [RegularDisplacement.law, S.target_density_eq t i] using
    ((S.transport t).displacement i).density_law 1 (by constructor <;> norm_num)

/-- The terminal coupling law is the actual normalized model posterior;
the Wasserstein target is therefore independent of time. -/
theorem terminal_posterior
    (hpost : ∀ i z, S.targetDensity i z =
      Real.exp (-U i astar z) / (∫ w, Real.exp (-U i astar w))) (t : ℝ) (i : Fin M) :
    ((S.transport t).displacement i).law 1 =
      Density.posteriorMeasure volume (fun z ↦ Real.exp (-U i astar z))
        (∫ w, Real.exp (-U i astar w)) := by
  rw [S.terminal_law]
  simp only [hpost, Density.posteriorMeasure, Density.densityMeasure]

theorem distanceSq_eq_posterior
    (hpost : ∀ i z, S.targetDensity i z =
      Real.exp (-U i astar z) / (∫ w, Real.exp (-U i astar w))) (t : ℝ) :
    (S.transport t).distanceSq = ‖S.parameter t-astar‖ ^ 2 + (M : ℝ)⁻¹ * ∑ i,
      ULA.wasserstein2Real ((S.transport t).law i : Measure Z)
        (Density.posteriorMeasure volume (fun z ↦ Real.exp (-U i astar z))
          (∫ w, Real.exp (-U i astar w))) ^ 2 := by
  simp only [DatasetRegularity.distanceSq, S.terminal_posterior hpost]

theorem parameterForce_eq (t : ℝ) : (S.transport t).parameterForce =
    averagedParameterForce volume (fun i ↦ S.density i t) U (S.parameter t) := by
  unfold DatasetRegularity.parameterForce averagedParameterForce
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hg : (fun z ↦ ((S.transport t).potential_gradient i z).fst) =
      fun z ↦ gradient (fun a ↦ U i a z) (S.parameter t) := by
    funext z
    exact (S.parameter_gradient t i z).unique
      (S.potential_parameter_differentiable i z (S.parameter t)).hasGradientAt
  rw [hg, ((S.transport t).displacement i).initial_density_law,
    S.density_eq t i, integral_density _ (S.density_C1 i t).continuous.measurable
      (fun z ↦ (S.positive i t z).le)]
  rfl

theorem latentScore_eq (t : ℝ) (i : Fin M) (z : Z) :
    (S.transport t).latentScore i z =
      gradient (chemicalPotential (S.density i t) (U i (S.parameter t))) z := by
  have hg := (S.latent_gradient t i z).unique
    ((S.potential_C1 i t).differentiable (by norm_num) z).hasGradientAt
  have hlog : DifferentiableAt ℝ (fun y ↦ Real.log (S.density i t y)) z :=
    ((S.density_C1 i t).differentiable (by norm_num) z).log (S.positive i t z).ne'
  simp only [DatasetRegularity.latentScore, S.density_eq t i, hg]
  have hder := hlog.hasFDerivAt.add
    ((S.potential_C1 i t).differentiable (by norm_num) z).hasFDerivAt
  change _ = (InnerProductSpace.toDual ℝ Z).symm
    (fderiv ℝ (fun x ↦ Real.log (S.density i t x) + U i (S.parameter t) x) z)
  change _ = (InnerProductSpace.toDual ℝ Z).symm
    (fderiv ℝ ((fun x ↦ Real.log (S.density i t x)) + U i (S.parameter t)) z)
  rw [hder.fderiv, map_add]
  exact add_comm _ _

theorem fisher_eq (t : ℝ) : (S.transport t).fisherInformation = S.fisher t := by
  unfold DatasetRegularity.fisherInformation fisher normalizedSlopeSquared
  rw [S.parameterForce_eq]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [S.latentScore_eq]
  rw [((S.transport t).displacement i).initial_density_law, S.density_eq t i,
    integral_density _ (S.density_C1 i t).continuous.measurable
      (fun z ↦ (S.positive i t z).le)]
  rfl

/-- Dissipation is a conclusion of the actual differential equations and
dominated differentiation/spatial integration by parts. -/
theorem deBruijn (t : ℝ) (ht : 0 ≤ t) : HasDerivAt S.energy (-S.fisher t) t :=
  (normalized_product_deBruijn S.density S.densityDerivative U S.parameter
    S.parameterDerivative t (S.domination t) S.parameter_differentiable
    S.potential_parameter_differentiable (fun i ↦ S.positive i t)
    (fun i ↦ S.density_C1 i t) (fun i ↦ S.potential_C1 i t)
    (S.parameter_gradient_integrable t) (S.parameter_equation t ht)
    (S.density_equation t ht) (S.integrable_tails t)).2

/-- Extended LSI is a conclusion of regular transport and joint strong
convexity, with exactly the source normalized Fisher information. -/
theorem extendedLSI (hM : 0 < M) (hrho : 0 < rho) (t : ℝ) :
    2*rho*(S.energy t-(S.transport t).freeEnergy 1) ≤ S.fisher t := by
  simpa only [S.initial_energy, S.fisher_eq] using
    (S.transport t).extendedLSI hM hrho

/-- Exponential decay of the actual density integral, derived from the
classical equations and joint strong convexity. The endpoint identity only
identifies the fixed comparison density's energy; it is not a dissipation or
first-order inequality hypothesis. -/
theorem energy_decay (hM : 0 < M) (hrho : 0 < rho) (T : ℝ)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    S.energy t-S.targetEnergy ≤ (S.energy 0-S.targetEnergy)*Real.exp (-2*rho*t) := by
  have hd (u : ℝ) (hu : 0 ≤ u) := (S.deBruijn u hu).sub_const S.targetEnergy
  have hc : ContinuousOn (fun u ↦ S.energy u-S.targetEnergy) (Icc 0 T) :=
    fun u hu ↦ (hd u hu.1).continuousAt.continuousWithinAt
  have hg := le_gronwallBound_of_liminf_deriv_right_le (K := -2*rho) (ε := 0) hc
    (fun u hu c hc ↦ (hd u hu.1).hasDerivWithinAt.liminf_right_slope_le hc)
    (le_refl (S.energy 0-S.targetEnergy))
    (fun u hu ↦ by
      have hi := S.extendedLSI hM hrho u
      rw [S.terminal_energy u] at hi
      linarith) t ht
  simpa only [gronwallBound_ε0, sub_zero] using hg

/-- The terminal law is the actual normalized Gibbs posterior and `astar`
maximizes its actual integrated evidence. These are the optimizer conclusions
constructed from the original potentials in `RegularModel`. -/
theorem target_minimal
    (hweight : ∀ i a, Integrable (fun z ↦ Real.exp (-U i a z)) volume)
    (hZ : ∀ i a, 0 < ∫ z, Real.exp (-U i a z))
    (hmax : ∀ a, S.evidence a ≤ S.evidence astar)
    (hpost : ∀ i z, S.targetDensity i z =
      Real.exp (-U i astar z)/(∫ w, Real.exp (-U i astar w))) (t : ℝ) :
    ∀ s ∈ Icc (0 : ℝ) 1, (S.transport t).freeEnergy 1 ≤ (S.transport t).freeEnergy s := by
  apply RegularDataset.posterior_minimal (S.transport t)
  · simpa only [S.potential_eq t] using hweight
  · simpa only [S.potential_eq t] using hZ
  · simpa only [RegularDataset.evidence, evidence, S.potential_eq t] using hmax
  · simpa only [S.target_density_eq t, S.potential_eq t] using hpost

/-- Full normalized product Wasserstein quadratic bound, with the fixed
posterior/evidence optimizer identified from its actual density. -/
theorem distance_control (hM : 0 < M) (hrho : 0 < rho)
    (hweight : ∀ i a, Integrable (fun z ↦ Real.exp (-U i a z)) volume)
    (hZ : ∀ i a, 0 < ∫ z, Real.exp (-U i a z))
    (hmax : ∀ a, S.evidence a ≤ S.evidence astar)
    (hpost : ∀ i z, S.targetDensity i z =
      Real.exp (-U i astar z)/(∫ w, Real.exp (-U i astar w))) (t : ℝ) :
    rho/2*(S.transport t).distanceSq ≤ S.energy t-S.targetEnergy := by
  have h := (S.transport t).talagrand_final hM hrho.le
    (S.target_minimal hweight hZ hmax hpost t)
  simpa only [S.initial_energy, S.terminal_energy] using h

/-- Both displayed inequalities in the paper's full continuous-time theorem.
The squared distance uses actual W₂ coupling infima. Dissipation, LSI and
quadratic growth are proved from the classical equations and regularity data.
-/
theorem full_product_exponential_convergence (hM : 0 < M) (hrho : 0 < rho)
    (hweight : ∀ i a, Integrable (fun z ↦ Real.exp (-U i a z)) volume)
    (hZ : ∀ i a, 0 < ∫ z, Real.exp (-U i a z))
    (hmax : ∀ a, S.evidence a ≤ S.evidence astar)
    (hpost : ∀ i z, S.targetDensity i z =
      Real.exp (-U i astar z)/(∫ w, Real.exp (-U i astar w)))
    (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt (S.transport t).distanceSq ≤ Real.sqrt (2*(S.energy t-S.targetEnergy)/rho) ∧
    Real.sqrt (2*(S.energy t-S.targetEnergy)/rho) ≤
      Real.sqrt (2*(S.energy 0-S.targetEnergy)/rho)*Real.exp (-rho*t) := by
  have hctrl := S.distance_control hM hrho hweight hZ hmax hpost t
  have hgap : 0 ≤ S.energy t-S.targetEnergy :=
    (mul_nonneg (by positivity) (S.transport t).distanceSq_nonneg).trans hctrl
  have hgap0 : 0 ≤ S.energy 0-S.targetEnergy :=
    (mul_nonneg (by positivity) (S.transport 0).distanceSq_nonneg).trans
      (S.distance_control hM hrho hweight hZ hmax hpost 0)
  constructor
  · apply Real.sqrt_le_sqrt
    apply (le_div_iff₀ hrho).mpr
    nlinarith
  · have hd := S.energy_decay hM hrho t t ⟨ht, le_rfl⟩
    have hx : 0 ≤ 2*(S.energy 0-S.targetEnergy)/rho := by positivity
    have hy : 0 ≤ 2*(S.energy t-S.targetEnergy)/rho := by positivity
    have hsquare : (Real.sqrt (2*(S.energy 0-S.targetEnergy)/rho)*Real.exp (-rho*t))^2 =
        (2*(S.energy 0-S.targetEnergy)/rho)*Real.exp (-2*rho*t) := by
      rw [mul_pow, Real.sq_sqrt hx, pow_two, ← Real.exp_add]
      congr 2
      ring
    have hdec := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2/rho by positivity)
    have hdec' : 2*(S.energy t-S.targetEnergy)/rho ≤
        (2*(S.energy 0-S.targetEnergy)/rho)*Real.exp (-2*rho*t) := by
      convert hdec using 1 <;> ring
    have hn : 0 ≤ Real.sqrt (2*(S.energy 0-S.targetEnergy)/rho)*Real.exp (-rho*t) := by
      positivity
    nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg (2*(S.energy t-S.targetEnergy)/rho)]

/-- The main-text parameter estimate is the parameter component of the
proved full product estimate. -/
theorem parameter_exponential_convergence (hM : 0 < M) (hrho : 0 < rho)
    (hweight : ∀ i a, Integrable (fun z ↦ Real.exp (-U i a z)) volume)
    (hZ : ∀ i a, 0 < ∫ z, Real.exp (-U i a z))
    (hmax : ∀ a, S.evidence a ≤ S.evidence astar)
    (hpost : ∀ i z, S.targetDensity i z =
      Real.exp (-U i astar z)/(∫ w, Real.exp (-U i astar w)))
    (t : ℝ) (ht : 0 ≤ t) :
    ‖S.parameter t-astar‖ ≤
      Real.sqrt (2*(S.energy 0-S.targetEnergy)/rho)*Real.exp (-rho*t) := by
  have hp : ‖S.parameter t-astar‖ ≤ Real.sqrt (S.transport t).distanceSq := by
    apply (Real.le_sqrt (norm_nonneg _) (S.transport t).distanceSq_nonneg).mpr
    unfold DatasetRegularity.distanceSq
    exact le_add_of_nonneg_right (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg _))
  have hd := S.full_product_exponential_convergence hM hrho hweight hZ hmax hpost t ht
  exact hp.trans (hd.1.trans hd.2)

end ClassicalFlow

/-- The main paper theorem with its optimizer and normalizers constructed
from the original heterogeneous potentials. Added assumptions are exactly
the primitive classical-flow/transport regularity in `ClassicalFlow`.
There is no independently chosen reference optimizer, dissipation identity,
first-order inequality, or log-Sobolev premise. -/
theorem existsUnique_optimizer_and_flow_convergence {dθ dz : ℕ}
    (U : Fin M → IPLA.Joint dθ dz → ℝ) (hM : 0 < M)
    (rho : ℝ) (hrho : 0 < rho)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ rho (U i)) :
    let V := fun i a z ↦ U i (IPLA.pair a z)
    let ell := fun a ↦ (M : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp (-V i a z))
    ∃! astar : EuclideanSpace ℝ (Fin dθ),
      (∀ a, ell a ≤ ell astar) ∧
      ∀ S : ClassicalFlow M dz rho astar V,
        (∀ i z, S.targetDensity i z = Real.exp (-V i astar z)/
          (∫ w, Real.exp (-V i astar w))) →
        ∀ t, 0 ≤ t → ‖S.parameter t-astar‖ ≤
          Real.sqrt (2*(S.energy 0-S.targetEnergy)/rho)*Real.exp (-rho*t) := by
  dsimp only
  let V := fun i a z ↦ U i (IPLA.pair a z)
  let ell := fun a ↦ (M : ℝ)⁻¹ * ∑ i, Real.log (∫ z, Real.exp (-V i a z))
  have he (a : EuclideanSpace ℝ (Fin dθ)) : ell a = -averageMarginalPotential U a := by
    simpa only [ell, V, RegularVariational.DensityModel.family,
      RegularVariational.DensityModel.mass, RegularModel.densityModel] using
      RegularModel.densityModel_logEvidence U rho hrho hdiff hsc a
  obtain ⟨astar, ha, hu⟩ :=
    existsUnique_averageMarginalMinimizer U hM rho hrho hdiff hsc
  have hmax : ∀ a, ell a ≤ ell astar := by
    intro a
    rw [he, he]
    exact neg_le_neg (ha a)
  refine ⟨astar, ⟨hmax, ?_⟩, ?_⟩
  · intro S hpost t ht
    exact S.parameter_exponential_convergence hM hrho
      (fun i a ↦ IPLA.integrable_marginal_weight (U i) rho hrho (hdiff i) (hsc i) a)
      (fun i a ↦ IPLA.marginalIntegral_pos (U i) rho hrho (hdiff i) (hsc i) a)
      hmax hpost t ht
  · intro b hb
    apply hu b
    intro a
    have h := hb.1 a
    change ell a ≤ ell b at h
    rw [he, he] at h
    linarith

end LatentDiffusion.RegularConvergence
