import LatentDiffusion.RegularDensityDomain
import LatentDiffusion.RegularFlowCalculus
import LatentDiffusion.RegularProductMetricFlow
import LatentDiffusion.RegularTalagrand

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-! # Extended LSI implies actual density-flow Talagrand control

This connected source endpoint contains no assumed entropy derivative or
metric-speed inequality. The bare density dynamics have only the actual
parameter/Fokker–Planck equations and analytic regularity. Their dissipation
is proved. Actual square-integrable characteristics and optimal coupling
anchors prove speed in the chart's actual normalized transport metric.
Extended LSI is the sole functional-inequality premise; no strong-convexity
or geodesic-convexity hypothesis is used by this implication.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace LatentDiffusion.RegularFlowTalagrand

open RegularFlowCalculus RegularDensityDomain

variable {A Z : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [CompleteSpace A] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [CompleteSpace Z] [FiniteDimensional ℝ Z] [MeasurableSpace Z]
  [BorelSpace Z] [SecondCountableTopology Z] {M : ℕ}

/-- The actual density gradient dynamics with local domination and spatial
tail integrability. There are no transport inequalities, strong-convexity
assumptions, energy derivatives or convergence estimates among these fields. -/
structure RegularDensityDynamics (M : ℕ) (U : Fin M → A → Z → ℝ) where
  parameter : ℝ → A
  parameterDerivative : ℝ → A
  density : Fin M → ℝ → Z → ℝ
  densityDerivative : Fin M → ℝ → Z → ℝ
  parameter_differentiable : ∀ t, HasDerivAt parameter (parameterDerivative t) t
  potential_parameter_differentiable : ∀ i z a, DifferentiableAt ℝ (fun b ↦ U i b z) a
  positive : ∀ i t z, 0 < density i t z
  density_C1 : ∀ i t, ContDiff ℝ 1 (density i t)
  potential_C1 : ∀ i t, ContDiff ℝ 1 (U i (parameter t))
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

namespace RegularDensityDynamics

variable {U : Fin M → A → Z → ℝ} (S : RegularDensityDynamics M U)

def energy (t : ℝ) : ℝ :=
  normalizedDensityEnergy volume (fun i ↦ S.density i t) U (S.parameter t)

def fisher (t : ℝ) : ℝ :=
  normalizedSlopeSquared volume (fun i ↦ S.density i t) U (S.parameter t)

def score (t : ℝ) (i : Fin M) : Z → Z :=
  gradient (chemicalPotential (S.density i t) (U i (S.parameter t)))

/-- Actual density dissipation is proved from the ODE/PDE and integrability;
extended LSI and convexity play no role in this identity. -/
theorem deBruijn (t : ℝ) (ht : 0 ≤ t) : HasDerivAt S.energy (-S.fisher t) t :=
  (normalized_product_deBruijn S.density S.densityDerivative U S.parameter
    S.parameterDerivative t (S.domination t) S.parameter_differentiable
    S.potential_parameter_differentiable (fun i ↦ S.positive i t)
    (fun i ↦ S.density_C1 i t) (fun i ↦ S.potential_C1 i t)
    (S.parameter_gradient_integrable t) (S.parameter_equation t ht)
    (S.density_equation t ht) (S.integrable_tails t)).2

/-- The actual score-square density integrands are absolutely integrable at
every nonnegative time. The Fisher quantity in the connected theorem is
therefore the genuine finite integral. -/
theorem fisher_integrable (t : ℝ) (ht : 0 ≤ t) (i : Fin M) :
    Integrable (fun z ↦ S.density i t z * ‖S.score t i z‖ ^ 2) volume :=
  (normalized_product_deBruijn S.density S.densityDerivative U S.parameter
    S.parameterDerivative t (S.domination t) S.parameter_differentiable
    S.potential_parameter_differentiable (fun i ↦ S.positive i t)
    (fun i ↦ S.density_C1 i t) (fun i ↦ S.potential_C1 i t)
    (S.parameter_gradient_integrable t) (S.parameter_equation t ht)
    (S.density_equation t ht) (S.integrable_tails t)).1 i

theorem fisher_nonneg (t : ℝ) : 0 ≤ S.fisher t :=
  normalizedSlopeSquared_nonneg volume (fun i ↦ S.density i t) U (S.parameter t)
    (fun i z ↦ (S.positive i t z).le)

theorem score_measurable (t : ℝ) (i : Fin M) : Measurable (S.score t i) := by
  have hW : ContDiff ℝ 1 (chemicalPotential (S.density i t) (U i (S.parameter t))) :=
    ((S.density_C1 i t).log (fun z ↦ (S.positive i t z).ne')).add (S.potential_C1 i t)
  exact ((InnerProductSpace.toDual ℝ Z).symm.continuous.comp
    (hW.continuous_fderiv (by norm_num))).measurable

end RegularDensityDynamics

variable {X : Type*} [MetricSpace X] {U : Fin M → A → Z → ℝ}
  {Ω : Fin M → Type*} [∀ i, MeasurableSpace (Ω i)]
  (Q : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (Q i)]

/-- A primitive characteristic realization of the actual density dynamics in
the actual complete density domain. Matching identities concern parameters,
densities and probability laws. Optimal anchors compare genuine couplings;
no metric-speed or entropy-dissipation estimate is a field. -/
structure CharacteristicRealization
    (D : ProductDensityChart X A Z M U) (S : RegularDensityDynamics M U) where
  state : ℝ → X
  state_continuous : ContinuousOn state (Ici 0)
  parameter_eq : ∀ t, D.parameter (state t) = S.parameter t
  density_eq : ∀ t i, (D.chart i).density (state t) = S.density i t
  characteristic : ℝ → ∀ i, Lp Z 2 (Q i)
  velocity : ℝ → ∀ i, Lp Z 2 (Q i)
  law_eq : ∀ t i, (Q i).map (characteristic t i) = (D.law (state t) i : Measure Z)
  derivative : ∀ t i, HasDerivAt (fun u ↦ characteristic u i) (velocity t i) t
  velocity_eq : ∀ t i, (velocity t i : Ω i → Z) =ᵐ[Q i]
    (fun ω ↦ -(S.score t i (characteristic t i ω)))
  anchor : ∀ s t i, RegularMetricFlow.OptimalAnchor (Q i) (characteristic t i)
    (D.law (state s) i : Measure Z)

namespace CharacteristicRealization

variable {D : ProductDensityChart X A Z M U} {S : RegularDensityDynamics M U}
  (R : CharacteristicRealization Q D S)

theorem energy_eq (t : ℝ) : D.energy (R.state t) = S.energy t := by
  unfold ProductDensityChart.energy RegularDensityDynamics.energy normalizedDensityEnergy
  simp_rw [R.parameter_eq, R.density_eq]

theorem domain_fisher_eq (t : ℝ) :
    normalizedSlopeSquared volume (fun i ↦ (D.chart i).density (R.state t)) U
      (D.parameter (R.state t)) = S.fisher t := by
  simp_rw [R.parameter_eq, R.density_eq]
  rfl

/-- Actual characteristic kinetic energy equals the actual density Fisher
information by change of density, rather than by an assumed speed identity. -/
theorem kinetic_energy_eq_fisher (t : ℝ) (ht : 0 ≤ t) :
    ‖S.parameterDerivative t‖ ^ 2 + (M : ℝ)⁻¹ * ∑ i, ‖R.velocity t i‖ ^ 2 =
      S.fisher t := by
  rw [RegularProductMetricFlow.kinetic_energy_eq_fisher Q
    (R.characteristic t) (R.velocity t) (S.score t)
    (averagedParameterForce volume (fun i ↦ S.density i t) U (S.parameter t))
    (S.parameterDerivative t) (S.parameter_equation t ht)
    (S.score_measurable t) (R.velocity_eq t)]
  unfold RegularDensityDynamics.fisher normalizedSlopeSquared
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  rw [R.law_eq t i, D.density_law, R.density_eq]
  rw [integral_withDensity_eq_integral_toReal_smul
    (S.density_C1 i t).continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (S.positive i t _).le, smul_eq_mul]
  rfl

theorem product_distance_eq (s t : ℝ) :
    RegularProductMetricFlow.distance Q S.parameter R.characteristic
      (D.parameter (R.state s)) (fun i ↦ (D.law (R.state s) i : Measure Z)) t =
      dist (R.state s) (R.state t) := by
  unfold RegularProductMetricFlow.distance
  simp_rw [R.law_eq, ← R.parameter_eq]
  rw [← D.metric_eq, Real.sqrt_sq dist_nonneg, dist_comm]

/-- The corrected source speed bound is derived from physical characteristic
derivatives and actual optimal coupling anchors. -/
theorem distance_right_slope (s t : ℝ) (ht : 0 ≤ t) (r : ℝ)
    (hr : Real.sqrt (S.fisher t) < r) :
    ∀ᶠ u in 𝓝[>] t, slope (fun v ↦ dist (R.state s) (R.state v)) t u < r := by
  have hh := RegularProductMetricFlow.distance_right_slope Q S.parameter R.characteristic
    (D.parameter (R.state s)) (fun i ↦ (D.law (R.state s) i : Measure Z))
    (R.anchor s) t (S.parameterDerivative t) (R.velocity t)
    (S.parameter_differentiable t) (R.derivative t) r
    (by rwa [kinetic_energy_eq_fisher Q R t ht])
  have heq : RegularProductMetricFlow.distance Q S.parameter R.characteristic
      (D.parameter (R.state s)) (fun i ↦ (D.law (R.state s) i : Measure Z)) =
      (fun v ↦ dist (R.state s) (R.state v)) := funext (product_distance_eq Q R s)
  rwa [heq] at hh

/-- The connected source xLSI-to-Talagrand theorem. Dissipation, metric speed,
kinetic/Fisher identification and energy lower semicontinuity are all proved
from the displayed primitive density/characteristic/domain data. Extended LSI
is the only functional-inequality premise, as in the source theorem.

The minimizing limit is constructed. There is no pre-existing minimizer,
strong-convexity premise, assumed entropy identity or assumed speed inequality.
-/
theorem exists_minimizer_talagrand [CompleteSpace X]
    (Fstar rho : ℝ) (hrho : 0 < rho) (hstar : ∀ x, Fstar ≤ D.energy x)
    (hxLSI : ∀ x, 2 * rho * (D.energy x-Fstar) ≤
      normalizedSlopeSquared volume (fun i ↦ (D.chart i).density x) U (D.parameter x)) :
    ∃ xstar, Tendsto (fun n : ℕ ↦ R.state n) atTop (𝓝 xstar) ∧
      D.energy xstar = Fstar ∧ (∀ x, D.energy xstar ≤ D.energy x) ∧
      ∀ t, 0 ≤ t → rho * dist (R.state t) xstar ^ 2 ≤
        2 * (D.energy (R.state t)-Fstar) := by
  apply RegularTalagrand.metric_flow_talagrand D.energy Fstar R.state S.fisher rho hrho
    D.lowerSemicontinuous_energy hstar R.state_continuous
  · exact (D.continuous_energy.comp_continuousOn R.state_continuous).sub continuousOn_const
  · intro t ht
    convert ((S.deBruijn t ht).sub_const Fstar).hasDerivWithinAt using 1
    funext u
    rw [energy_eq Q R u]
  · intro t ht
    exact S.fisher_nonneg t
  · intro t ht
    have h := hxLSI (R.state t)
    rwa [domain_fisher_eq Q R t] at h
  · intro s t hs ht r hr
    exact distance_right_slope Q R s t ht r hr

end CharacteristicRealization

end LatentDiffusion.RegularFlowTalagrand
