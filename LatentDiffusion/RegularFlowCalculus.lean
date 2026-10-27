import LatentDiffusion.SourceCalculus
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false

/-!
# Density free-energy differentiation and the Fokker–Planck equation

The density energy is the actual integral `∫ q (log q + U)`. Its time
derivative follows from pointwise time derivatives and local domination.
The weak Fokker–Planck equation is tested against the chemical potential;
the free-energy dissipation identity is a theorem, never a regularity field.

The classical version below derives the weak identity from the pointwise PDE
and ordinary Lebesgue integration by parts. Its tail assumptions are absolute
integrability of the three products in that integration-by-parts theorem.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace LatentDiffusion.RegularFlowCalculus

/-- Pointwise differentiation of the density energy when both its density and
its potential depend on time. -/
theorem energy_integrand_hasDerivAt
    {q U : ℝ → ℝ} {qd Ud t : ℝ}
    (hq : HasDerivAt q qd t) (hU : HasDerivAt U Ud t) (hpos : 0 < q t) :
    HasDerivAt (fun s ↦ q s * (Real.log (q s) + U s))
      (qd * (Real.log (q t) + U t + 1) + q t * Ud) t := by
  have hc : q t * (qd / q t) = qd := by
    rw [mul_comm, div_mul_cancel₀ _ hpos.ne']
  convert hq.mul ((hq.log hpos.ne').add hU) using 1
  simp only [Pi.add_apply, mul_add, mul_one, hc]
  ring

/-- Sufficient local analytic hypotheses for differentiation of the actual
density free energy. These are domination, positivity and pointwise regularity,
and contain no assertion about the derivative of an integral. -/
structure LocalEnergyDomination {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (q qdot U Udot : ℝ → X → ℝ) (t : ℝ) where
  neighborhood : Set ℝ
  neighborhood_mem : neighborhood ∈ 𝓝 t
  bound : X → ℝ
  measurable : ∀ᶠ u in 𝓝 t,
    AEStronglyMeasurable (fun x ↦ q u x * (Real.log (q u x) + U u x)) ν
  integrable : Integrable (fun x ↦ q t x * (Real.log (q t x) + U t x)) ν
  derivative_measurable : AEStronglyMeasurable
    (fun x ↦ qdot t x * (Real.log (q t x) + U t x + 1) + q t x * Udot t x) ν
  derivative_bound : ∀ᵐ x ∂ν, ∀ u ∈ neighborhood,
    ‖qdot u x * (Real.log (q u x) + U u x + 1) + q u x * Udot u x‖ ≤ bound x
  bound_integrable : Integrable bound ν
  positive : ∀ᵐ x ∂ν, ∀ u ∈ neighborhood, 0 < q u x
  density_derivative : ∀ᵐ x ∂ν, ∀ u ∈ neighborhood,
    HasDerivAt (fun v ↦ q v x) (qdot u x) u

/-- Domination together with the pointwise potential derivative. The
parameter-path constructor below derives this final field by the chain rule. -/
structure LocalEnergyRegularity {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (q qdot U Udot : ℝ → X → ℝ) (t : ℝ)
    extends LocalEnergyDomination ν q qdot U Udot t where
  potential_derivative : ∀ᵐ x ∂ν, ∀ u ∈ neighborhood,
    HasDerivAt (fun v ↦ U v x) (Udot u x) u

/-- Dominated differentiation computes the density free-energy derivative. -/
theorem LocalEnergyRegularity.hasDerivAt_energy
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {q qdot U Udot : ℝ → X → ℝ} {t : ℝ}
    (data : LocalEnergyRegularity ν q qdot U Udot t) :
    Integrable
      (fun x ↦ qdot t x * (Real.log (q t x) + U t x + 1) + q t x * Udot t x) ν ∧
    HasDerivAt (fun u ↦ SourceCalculus.densityFreeEnergy ν (q u) (U u))
      (∫ x, qdot t x * (Real.log (q t x) + U t x + 1) + q t x * Udot t x ∂ν) t := by
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le data.neighborhood_mem
    data.measurable data.integrable data.derivative_measurable
    data.derivative_bound data.bound_integrable
  filter_upwards [data.positive, data.density_derivative, data.potential_derivative]
    with x hx hq hU u hu
  exact energy_integrand_hasDerivAt (hq u hu) (hU u hu) (hx u hu)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E]

/-- The chemical potential, which is the density first variation up to an
irrelevant constant on probability-preserving directions. -/
def chemicalPotential (q U : E → ℝ) : E → ℝ := fun x ↦ Real.log (q x) + U x

/-- Admissible-test weak Fokker–Planck equation `qdot = div(q ∇(log q+U))`.
All C¹ tests for which both displayed integrands are integrable are allowed.
This is a solution equation, independent of any free-energy calculation. -/
def WeakFokkerPlanck (ν : Measure E) (q qdot U : E → ℝ) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ 1 ψ →
    Integrable (fun x ↦ qdot x * ψ x) ν →
    Integrable (fun x ↦ q x * inner ℝ (gradient (chemicalPotential q U) x)
      (gradient ψ x)) ν →
    (∫ x, qdot x * ψ x ∂ν) =
      -(∫ x, q x * inner ℝ (gradient (chemicalPotential q U) x)
        (gradient ψ x) ∂ν)

omit [MeasurableSpace E] in
theorem gradient_add_one (f : E → ℝ) (x : E) :
    gradient (fun y ↦ f y + 1) x = gradient f x := by
  simp [gradient, fderiv_add_const]

/-- The de Bruijn identity for a regular solution of the weak density equation.
Only pointwise derivatives, domination and the weak PDE are inputs. In
particular, neither an energy derivative nor an energy inequality is assumed. -/
theorem deBruijn_of_regular_weak_equation
    (ν : Measure E) (q qdot U Udot : ℝ → E → ℝ) (t : ℝ)
    (data : LocalEnergyRegularity ν q qdot U Udot t)
    (hpos : ∀ x, 0 < q t x) (hq : ContDiff ℝ 1 (q t))
    (hU : ContDiff ℝ 1 (U t))
    (hpotential : Integrable (fun x ↦ q t x * Udot t x) ν)
    (hfisher : Integrable
      (fun x ↦ q t x * ‖gradient (chemicalPotential (q t) (U t)) x‖ ^ 2) ν)
    (hweak : WeakFokkerPlanck ν (q t) (qdot t) (U t)) :
    HasDerivAt (fun u ↦ SourceCalculus.densityFreeEnergy ν (q u) (U u))
      (-(∫ x, q t x * ‖gradient (chemicalPotential (q t) (U t)) x‖ ^ 2 ∂ν) +
        ∫ x, q t x * Udot t x ∂ν) t := by
  have hW : ContDiff ℝ 1 (chemicalPotential (q t) (U t)) :=
    (hq.log (fun x ↦ (hpos x).ne')).add hU
  let ψ : E → ℝ := fun x ↦ chemicalPotential (q t) (U t) x + 1
  have hψ : ContDiff ℝ 1 ψ := hW.add contDiff_const
  have hd := data.hasDerivAt_energy
  have hint : Integrable (fun x ↦ qdot t x * ψ x) ν := by
    convert hd.1.sub hpotential using 1
    ext x
    simp [ψ, chemicalPotential]
  have hgrad : ∀ x, gradient ψ x = gradient (chemicalPotential (q t) (U t)) x :=
    gradient_add_one _
  have hflux : Integrable
      (fun x ↦ q t x * inner ℝ (gradient (chemicalPotential (q t) (U t)) x)
        (gradient ψ x)) ν := by
    simpa only [hgrad, real_inner_self_eq_norm_sq] using hfisher
  have hw := hweak ψ hψ hint hflux
  simp only [hgrad, real_inner_self_eq_norm_sq] at hw
  have hsplit : (∫ x, qdot t x * (Real.log (q t x) + U t x + 1) +
      q t x * Udot t x ∂ν) =
      -(∫ x, q t x * ‖gradient (chemicalPotential (q t) (U t)) x‖ ^ 2 ∂ν) +
        ∫ x, q t x * Udot t x ∂ν := by
    change (∫ x, qdot t x * ψ x + q t x * Udot t x ∂ν) = _
    rw [integral_add hint hpotential]
    exact congrArg (fun v : ℝ ↦ v + ∫ x, q t x * Udot t x ∂ν) hw
  rw [hsplit] at hd
  exact hd.2

section ClassicalEquation

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- A component of a vector flux in the standard orthonormal basis. -/
def fluxComponent (V : E → E) (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun x ↦ inner ℝ (V x) (stdOrthonormalBasis ℝ E i)

/-- Classical divergence written in an orthonormal basis. -/
def fluxDivergence (V : E → E) (x : E) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    fderiv ℝ (fluxComponent V i) x (stdOrthonormalBasis ℝ E i)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem fluxComponent_neg (V : E → E) (i : Fin (Module.finrank ℝ E)) :
    fluxComponent (fun y ↦ -V y) i = -fluxComponent V i := by
  funext x
  exact inner_neg_left (V x) (stdOrthonormalBasis ℝ E i)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem fluxDivergence_neg (V : E → E) (x : E) :
    fluxDivergence (fun y ↦ -V y) x = -fluxDivergence V x := by
  simp only [fluxDivergence, fluxComponent_neg, fderiv_neg, neg_apply,
    Finset.sum_neg_distrib]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The orthonormal-coordinate divergence is the trace of the actual spatial
Fréchet derivative. No trace/divergence identification is assumed. -/
theorem fluxDivergence_eq_trace (V : E → E) (A : E →L[ℝ] E) (x : E)
    (hV : HasFDerivAt V A x) :
    fluxDivergence V x = LinearMap.trace ℝ E A.toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner A.toLinearMap (stdOrthonormalBasis ℝ E)]
  unfold fluxDivergence
  apply Finset.sum_congr rfl
  intro i hi
  have hd : HasFDerivAt (fluxComponent V i)
      ((innerSL ℝ (stdOrthonormalBasis ℝ E i)).comp A) x := by
    convert (innerSL ℝ (stdOrthonormalBasis ℝ E i)).hasFDerivAt.comp x hV using 1
    funext y
    exact real_inner_comm _ _
  rw [hd.fderiv]
  rfl

/-- Explicit decay conditions sufficient for spatial integration by parts.
The three products are exactly those in the ordinary Lebesgue theorem;
no integral identity is one of the fields. Schwartz fluxes and tests with
polynomial growth are a standard class satisfying these hypotheses. -/
structure NoBoundaryFlux (V : E → E) (ψ : E → ℝ) : Prop where
  flux_differentiable : ∀ i, Differentiable ℝ (fluxComponent V i)
  derivative_flux_integrable : ∀ i, Integrable
    (fun x ↦ fderiv ℝ (fluxComponent V i) x (stdOrthonormalBasis ℝ E i) * ψ x)
    volume
  derivative_test_integrable : ∀ i, Integrable
    (fun x ↦ fluxComponent V i x * fderiv ℝ ψ x (stdOrthonormalBasis ℝ E i))
    volume
  product_integrable : ∀ i, Integrable (fun x ↦ fluxComponent V i x * ψ x) volume

omit [CompleteSpace E] in
theorem NoBoundaryFlux.neg {V : E → E} {ψ : E → ℝ}
    (htail : NoBoundaryFlux V ψ) : NoBoundaryFlux (fun y ↦ -V y) ψ where
  flux_differentiable i := by
    simpa only [fluxComponent_neg] using (htail.flux_differentiable i).neg
  derivative_flux_integrable i := by
    convert (htail.derivative_flux_integrable i).neg using 1
    ext x
    simp only [fluxComponent_neg, fderiv_neg, neg_apply, Pi.neg_apply, neg_mul]
  derivative_test_integrable i := by
    convert (htail.derivative_test_integrable i).neg using 1
    ext x
    simp only [fluxComponent_neg, Pi.neg_apply, neg_mul]
  product_integrable i := by
    convert (htail.product_integrable i).neg using 1
    ext x
    simp only [fluxComponent_neg, Pi.neg_apply, neg_mul]

/-- Absolute integrability of the vector flux pairing follows from the
componentwise integration-by-parts hypotheses. -/
theorem NoBoundaryFlux.integrable_flux_gradient
    {V : E → E} {ψ : E → ℝ} (htail : NoBoundaryFlux V ψ) :
    Integrable (fun x ↦ inner ℝ (V x) (gradient ψ x)) volume := by
  have hpoint (x : E) :
      inner ℝ (V x) (gradient ψ x) =
      ∑ i : Fin (Module.finrank ℝ E),
        fluxComponent V i x * fderiv ℝ ψ x (stdOrthonormalBasis ℝ E i) := by
    simpa only [fluxComponent, ← inner_gradient_left,
      real_inner_comm (gradient ψ x)] using
      ((stdOrthonormalBasis ℝ E).sum_inner_mul_inner (V x) (gradient ψ x)).symm
  simp_rw [hpoint]
  exact integrable_finsetSum Finset.univ (fun i _ ↦ htail.derivative_test_integrable i)

omit [CompleteSpace E] in
theorem NoBoundaryFlux.integrable_divergence_mul
    {V : E → E} {ψ : E → ℝ} (htail : NoBoundaryFlux V ψ) :
    Integrable (fun x ↦ fluxDivergence V x * ψ x) volume := by
  simp_rw [fluxDivergence, Finset.sum_mul]
  exact integrable_finsetSum Finset.univ (fun i _ ↦ htail.derivative_flux_integrable i)

/-- Lebesgue integration by parts gives the divergence weak equation from
classical spatial derivatives and explicit tail integrability. -/
theorem integral_divergence_mul
    (V : E → E) (ψ : E → ℝ) (hψ : Differentiable ℝ ψ)
    (htail : NoBoundaryFlux V ψ) :
    (∫ x, fluxDivergence V x * ψ x ∂volume) =
      -(∫ x, inner ℝ (V x) (gradient ψ x) ∂volume) := by
  have hpoint (x : E) :
      inner ℝ (V x) (gradient ψ x) =
      ∑ i : Fin (Module.finrank ℝ E),
        fluxComponent V i x * fderiv ℝ ψ x (stdOrthonormalBasis ℝ E i) := by
    simpa only [fluxComponent, ← inner_gradient_left,
      real_inner_comm (gradient ψ x)] using
      ((stdOrthonormalBasis ℝ E).sum_inner_mul_inner (V x) (gradient ψ x)).symm
  simp_rw [fluxDivergence, Finset.sum_mul, hpoint]
  rw [integral_finsetSum Finset.univ (fun i _ ↦ htail.derivative_flux_integrable i),
    integral_finsetSum Finset.univ (fun i _ ↦ htail.derivative_test_integrable i),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hip := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (htail.derivative_flux_integrable i) (htail.derivative_test_integrable i)
    (htail.product_integrable i) (fun x _ ↦ htail.flux_differentiable i x)
    (fun x _ ↦ hψ x)
  linarith

/-- The transport integration-by-parts identity under the actual density law.
It is derived from Lebesgue integration by parts and the pointwise derivative
of `log q`. This is the entropy-score pairing used by displacement calculus. -/
theorem transport_score_pairing
    (q : E → ℝ) (V : E → E) (hq : ContDiff ℝ 1 q) (hpos : ∀ x, 0 < q x)
    (htail : NoBoundaryFlux V q) :
    (∫ x, fluxDivergence V x ∂(volume.withDensity (fun x ↦ ENNReal.ofReal (q x)))) =
      -(∫ x, inner ℝ (V x) (gradient (fun y ↦ Real.log (q y)) x)
        ∂(volume.withDensity (fun x ↦ ENNReal.ofReal (q x)))) := by
  have hconvert (f : E → ℝ) :
      (∫ x, f x ∂(volume.withDensity (fun x ↦ ENNReal.ofReal (q x)))) =
      ∫ x, q x * f x ∂volume := by
    rw [integral_withDensity_eq_integral_toReal_smul hq.continuous.measurable.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul]
  have hpoint (x : E) : q x * inner ℝ (V x)
      (gradient (fun y ↦ Real.log (q y)) x) = inner ℝ (V x) (gradient q x) := by
    have hscore : gradient (fun y ↦ Real.log (q y)) x = (q x)⁻¹ • gradient q x := by
      simp only [gradient, fderiv.log (hq.differentiable (by norm_num) x) (hpos x).ne',
        map_smul]
    rw [hscore, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (hpos x).ne', one_mul]
  rw [hconvert, hconvert]
  simp_rw [hpoint, mul_comm (q _)]
  exact integral_divergence_mul V q (hq.differentiable (by norm_num)) htail

/-- Both actual law integrals in the transport score identity are absolutely
integrable; the identity does not exploit the total integral's default value. -/
theorem transport_score_integrable
    (q : E → ℝ) (V : E → E) (hq : ContDiff ℝ 1 q) (hpos : ∀ x, 0 < q x)
    (htail : NoBoundaryFlux V q) :
    Integrable (fluxDivergence V) (volume.withDensity (fun x ↦ ENNReal.ofReal (q x))) ∧
    Integrable (fun x ↦ inner ℝ (V x) (gradient (fun y ↦ Real.log (q y)) x))
      (volume.withDensity (fun x ↦ ENNReal.ofReal (q x))) := by
  have hconvert (f : E → ℝ) :
      Integrable f (volume.withDensity (fun x ↦ ENNReal.ofReal (q x))) ↔
      Integrable (fun x ↦ q x * f x) volume := by
    rw [integrable_withDensity_iff_integrable_smul'
      hq.continuous.measurable.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hpos _).le, smul_eq_mul]
  constructor
  · rw [hconvert]
    simpa only [mul_comm (q _)] using htail.integrable_divergence_mul
  · rw [hconvert]
    convert htail.integrable_flux_gradient using 1
    ext x
    have hscore : gradient (fun y ↦ Real.log (q y)) x = (q x)⁻¹ • gradient q x := by
      simp only [gradient, fderiv.log (hq.differentiable (by norm_num) x) (hpos x).ne',
        map_smul]
    rw [hscore, inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (hpos x).ne', one_mul]

/-- Classical Fokker–Planck flux. Its negative divided by `q` is the
continuity-equation velocity `-∇(log q+U)`. -/
def fokkerPlanckFlux (q U : E → ℝ) : E → E :=
  fun x ↦ q x • gradient (chemicalPotential q U) x

/-- A pointwise Fokker–Planck equation has its expected weak identity whenever
the ordinary integration-by-parts products are integrable. -/
theorem classical_fokkerPlanck_test
    (q qdot U ψ : E → ℝ) (hψ : Differentiable ℝ ψ)
    (hpde : ∀ᵐ x ∂volume, qdot x = fluxDivergence (fokkerPlanckFlux q U) x)
    (htail : NoBoundaryFlux (fokkerPlanckFlux q U) ψ) :
    (∫ x, qdot x * ψ x ∂volume) =
      -(∫ x, q x * inner ℝ (gradient (chemicalPotential q U) x)
        (gradient ψ x) ∂volume) := by
  calc
    _ = ∫ x, fluxDivergence (fokkerPlanckFlux q U) x * ψ x ∂volume := by
      apply integral_congr_ae
      filter_upwards [hpde] with x hx
      rw [hx]
    _ = _ := by
      simpa only [fokkerPlanckFlux, inner_smul_left, RCLike.conj_to_real] using
        integral_divergence_mul (fokkerPlanckFlux q U) ψ hψ htail

/-- The first variation in a genuine continuity-equation direction. The
velocity field is arbitrary; its pairing with the score is a conclusion of
integration by parts, rather than an assumed Wasserstein derivative. -/
theorem continuity_density_variation
    (q qdot U : E → ℝ) (v : E → E)
    (hW : Differentiable ℝ (chemicalPotential q U))
    (hcontinuity : ∀ᵐ x ∂volume,
      qdot x = -fluxDivergence (fun y ↦ q y • v y) x)
    (htail : NoBoundaryFlux (fun y ↦ q y • v y)
      (fun x ↦ chemicalPotential q U x + 1)) :
    (∫ x, qdot x * (chemicalPotential q U x + 1) ∂volume) =
      ∫ x, q x * inner ℝ (v x) (gradient (chemicalPotential q U) x) ∂volume := by
  have hgrad : ∀ x, gradient (fun y ↦ chemicalPotential q U y + 1) x =
      gradient (chemicalPotential q U) x := gradient_add_one _
  have hip := integral_divergence_mul (fun y ↦ q y • v y)
    (fun x ↦ chemicalPotential q U x + 1) (hW.add_const 1) htail
  simp only [hgrad, inner_smul_left, RCLike.conj_to_real] at hip
  calc
    _ = -(∫ x, fluxDivergence (fun y ↦ q y • v y) x *
        (chemicalPotential q U x + 1) ∂volume) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [hcontinuity] with x hx
      simp [hx]
    _ = _ := by rw [hip, neg_neg]

/-- Actual energy differentiation in any classical continuity-equation
direction. This is the integral first-variation formula needed to represent
the source gradient on its normalized product tangent space. -/
theorem energy_derivative_of_regular_continuity
    (q qdot U Udot : ℝ → E → ℝ) (t : ℝ) (v : E → E)
    (data : LocalEnergyRegularity volume q qdot U Udot t)
    (hpos : ∀ x, 0 < q t x) (hq : ContDiff ℝ 1 (q t))
    (hU : ContDiff ℝ 1 (U t))
    (hpotential : Integrable (fun x ↦ q t x * Udot t x) volume)
    (hcontinuity : ∀ᵐ x ∂volume,
      qdot t x = -fluxDivergence (fun y ↦ q t y • v y) x)
    (htail : NoBoundaryFlux (fun y ↦ q t y • v y)
      (fun x ↦ chemicalPotential (q t) (U t) x + 1)) :
    HasDerivAt (fun u ↦ SourceCalculus.densityFreeEnergy volume (q u) (U u))
      ((∫ x, q t x * inner ℝ (v x)
        (gradient (chemicalPotential (q t) (U t)) x) ∂volume) +
        ∫ x, q t x * Udot t x ∂volume) t := by
  have hW : ContDiff ℝ 1 (chemicalPotential (q t) (U t)) :=
    (hq.log (fun x ↦ (hpos x).ne')).add hU
  have hv := continuity_density_variation (q t) (qdot t) (U t) v
    (hW.differentiable (by norm_num)) hcontinuity htail
  have hd := data.hasDerivAt_energy
  have hint : Integrable
      (fun x ↦ qdot t x * (Real.log (q t x) + U t x + 1)) volume := by
    convert hd.1.sub hpotential using 1
    ext x
    simp
  have heq : (∫ x, qdot t x * (Real.log (q t x) + U t x + 1) +
      q t x * Udot t x ∂volume) =
      (∫ x, q t x * inner ℝ (v x)
        (gradient (chemicalPotential (q t) (U t)) x) ∂volume) +
        ∫ x, q t x * Udot t x ∂volume := by
    rw [integral_add hint hpotential]
    exact congrArg (fun r : ℝ ↦ r + ∫ x, q t x * Udot t x ∂volume) hv
  rw [heq] at hd
  exact hd.2

/-- The full density de Bruijn identity is proved from the classical PDE.
All added assumptions are local differentiability/domination, spatial C¹
regularity, absolute integrability and the pointwise solution equation. -/
theorem deBruijn_of_regular_classical_equation
    (q qdot U Udot : ℝ → E → ℝ) (t : ℝ)
    (data : LocalEnergyRegularity volume q qdot U Udot t)
    (hpos : ∀ x, 0 < q t x) (hq : ContDiff ℝ 1 (q t))
    (hU : ContDiff ℝ 1 (U t))
    (hpotential : Integrable (fun x ↦ q t x * Udot t x) volume)
    (hpde : ∀ᵐ x ∂volume, qdot t x =
      fluxDivergence (fokkerPlanckFlux (q t) (U t)) x)
    (htail : NoBoundaryFlux (fokkerPlanckFlux (q t) (U t))
      (fun x ↦ chemicalPotential (q t) (U t) x + 1)) :
    HasDerivAt (fun u ↦ SourceCalculus.densityFreeEnergy volume (q u) (U u))
      (-(∫ x, q t x * ‖gradient (chemicalPotential (q t) (U t)) x‖ ^ 2 ∂volume) +
        ∫ x, q t x * Udot t x ∂volume) t := by
  have hW : ContDiff ℝ 1 (chemicalPotential (q t) (U t)) :=
    (hq.log (fun x ↦ (hpos x).ne')).add hU
  let ψ : E → ℝ := fun x ↦ chemicalPotential (q t) (U t) x + 1
  have hψ : ContDiff ℝ 1 ψ := hW.add contDiff_const
  have hgrad : ∀ x, gradient ψ x = gradient (chemicalPotential (q t) (U t)) x :=
    gradient_add_one _
  have hw := classical_fokkerPlanck_test (q t) (qdot t) (U t) ψ
    (hψ.differentiable (by norm_num)) hpde htail
  simp only [hgrad, real_inner_self_eq_norm_sq] at hw
  have hd := data.hasDerivAt_energy
  have hint : Integrable (fun x ↦ qdot t x * ψ x) volume := by
    convert hd.1.sub hpotential using 1
    ext x
    simp [ψ, chemicalPotential]
  have hsplit : (∫ x, qdot t x * (Real.log (q t x) + U t x + 1) +
      q t x * Udot t x ∂volume) =
      -(∫ x, q t x * ‖gradient (chemicalPotential (q t) (U t)) x‖ ^ 2 ∂volume) +
        ∫ x, q t x * Udot t x ∂volume := by
    change (∫ x, qdot t x * ψ x + q t x * Udot t x ∂volume) = _
    rw [integral_add hint hpotential]
    exact congrArg (fun v : ℝ ↦ v + ∫ x, q t x * Udot t x ∂volume) hw
  rw [hsplit] at hd
  exact hd.2

end ClassicalEquation

section ParameterCalculus

variable {A X : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [CompleteSpace A] [MeasurableSpace X]

/-- The actual integral of the parameter gradient under a density. -/
def parameterForce (ν : Measure X) (q : X → ℝ) (U : A → X → ℝ) (a : A) : A :=
  ∫ x, q x • gradient (fun b ↦ U b x) a ∂ν

/-- The weighted parameter directional derivative is integrable, and equals
the inner product against the actual integral parameter gradient. -/
theorem parameter_rate_integral
    (ν : Measure X) (q : X → ℝ) (U : A → X → ℝ) (a v : A)
    (hgrad : Integrable (fun x ↦ q x • gradient (fun b ↦ U b x) a) ν) :
    Integrable (fun x ↦ q x * fderiv ℝ (fun b ↦ U b x) a v) ν ∧
    (∫ x, q x * fderiv ℝ (fun b ↦ U b x) a v ∂ν) =
      inner ℝ v (parameterForce ν q U a) := by
  have hpoint (x : X) : q x * fderiv ℝ (fun b ↦ U b x) a v =
      inner ℝ v (q x • gradient (fun b ↦ U b x) a) := by
    simp only [inner_smul_right, inner_gradient_right, RCLike.conj_to_real]
  simp_rw [hpoint]
  exact ⟨hgrad.const_inner v, integral_inner hgrad v⟩

/-- Parameter time derivatives used in the energy integral are derived by the
ordinary chain rule. This is also the constructor for the full analytic data;
the domination data themselves need no potential time-derivative assertion. -/
def LocalEnergyDomination.along_parameter_path
    (ν : Measure X) (q qdot : ℝ → X → ℝ) (U : A → X → ℝ)
    (p pdot : ℝ → A) (t : ℝ)
    (data : LocalEnergyDomination ν q qdot (fun u ↦ U (p u))
      (fun u x ↦ fderiv ℝ (fun a ↦ U a x) (p u) (pdot u)) t)
    (hp : ∀ u ∈ data.neighborhood, HasDerivAt p (pdot u) u)
    (hU : ∀ x u, u ∈ data.neighborhood → DifferentiableAt ℝ (fun a ↦ U a x) (p u)) :
    LocalEnergyRegularity ν q qdot (fun u ↦ U (p u))
      (fun u x ↦ fderiv ℝ (fun a ↦ U a x) (p u) (pdot u)) t where
  toLocalEnergyDomination := data
  potential_derivative := ae_of_all _ fun x u hu ↦
    (hU x u hu).hasFDerivAt.comp_hasDerivAt u (hp u hu)

/-- Along parameter gradient descent, the parameter contribution is exactly
minus the squared norm of the actual averaged gradient. -/
theorem parameter_descent_rate
    (ν : Measure X) (q : X → ℝ) (U : A → X → ℝ) (a : A)
    (hgrad : Integrable (fun x ↦ q x • gradient (fun b ↦ U b x) a) ν) :
    (∫ x, q x * fderiv ℝ (fun b ↦ U b x) a (-parameterForce ν q U a) ∂ν) =
      -‖parameterForce ν q U a‖ ^ 2 := by
  rw [(parameter_rate_integral ν q U a _ hgrad).2]
  simp only [inner_neg_left, real_inner_self_eq_norm_sq]

end ParameterCalculus

section NormalizedProduct

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [CompleteSpace A] [FiniteDimensional ℝ E] [BorelSpace E] {M : ℕ}

/-- Parameter component of the source's gradient: the average of the actual
integral parameter gradients. -/
def averagedParameterForce (ν : Measure E) (q : Fin M → E → ℝ)
    (U : Fin M → A → E → ℝ) (a : A) : A :=
  (M : ℝ)⁻¹ • ∑ i, parameterForce ν (q i) (U i) a

/-- The actual source density free energy, normalized by the number of data. -/
def normalizedDensityEnergy (ν : Measure E) (q : Fin M → E → ℝ)
    (U : Fin M → A → E → ℝ) (a : A) : ℝ :=
  (M : ℝ)⁻¹ * ∑ i, SourceCalculus.densityFreeEnergy ν (q i) (U i a)

/-- Riesz pairing with the source's normalized product gradient. There is no
`1/M` in an individual law-gradient component; it occurs in the tangent metric
itself. -/
def normalizedProductGradientPairing (ν : Measure E) (q : Fin M → E → ℝ)
    (U : Fin M → A → E → ℝ) (a da : A) (v : Fin M → E → E) : ℝ :=
  inner ℝ da (averagedParameterForce ν q U a) +
    (M : ℝ)⁻¹ * ∑ i, ∫ x, q i x * inner ℝ (v i x)
      (gradient (chemicalPotential (q i) (U i a)) x) ∂ν

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [BorelSpace E] in
theorem averaged_parameter_rate
    (ν : Measure E) (q : Fin M → E → ℝ) (U : Fin M → A → E → ℝ)
    (a da : A)
    (hgrad : ∀ i, Integrable (fun x ↦ q i x • gradient (fun b ↦ U i b x) a) ν) :
    (M : ℝ)⁻¹ * ∑ i, (∫ x, q i x * fderiv ℝ (fun b ↦ U i b x) a da ∂ν) =
      inner ℝ da (averagedParameterForce ν q U a) := by
  simp_rw [(parameter_rate_integral ν _ _ a da (hgrad _)).2]
  simp [averagedParameterForce, inner_smul_right, inner_sum]

/-- Source gradient representation for the actual density energy and every
admissible parameter/transport tangent. Parameter differentiation comes from
the chain rule and integration; law differentiation comes from the actual
continuity equation and proved spatial integration by parts.

This simultaneously fixes the normalization: the parameter gradient is the
average force, while each law gradient is `∇(log q_i + U_i)`. -/
theorem normalized_product_gradient_representation
    (q qdot : Fin M → ℝ → E → ℝ) (U : Fin M → A → E → ℝ)
    (p pdot : ℝ → A) (t : ℝ) (v : Fin M → E → E)
    (data : ∀ i, LocalEnergyDomination volume (q i) (qdot i) (fun u ↦ U i (p u))
      (fun u x ↦ fderiv ℝ (fun a ↦ U i a x) (p u) (pdot u)) t)
    (hp : ∀ u, HasDerivAt p (pdot u) u)
    (hparam : ∀ i x a, DifferentiableAt ℝ (fun b ↦ U i b x) a)
    (hpos : ∀ i x, 0 < q i t x) (hq : ∀ i, ContDiff ℝ 1 (q i t))
    (hU : ∀ i, ContDiff ℝ 1 (U i (p t)))
    (hgrad : ∀ i, Integrable
      (fun x ↦ q i t x • gradient (fun b ↦ U i b x) (p t)) volume)
    (hcontinuity : ∀ i, ∀ᵐ x ∂volume,
      qdot i t x = -fluxDivergence (fun y ↦ q i t y • v i y) x)
    (htail : ∀ i, NoBoundaryFlux (fun y ↦ q i t y • v i y)
      (fun x ↦ chemicalPotential (q i t) (U i (p t)) x + 1)) :
    HasDerivAt (fun u ↦ normalizedDensityEnergy volume (fun i ↦ q i u) U (p u))
      (normalizedProductGradientPairing volume (fun i ↦ q i t) U (p t) (pdot t) v) t := by
  have heach : ∀ i, HasDerivAt
      (fun u ↦ SourceCalculus.densityFreeEnergy volume (q i u) (U i (p u)))
      ((∫ x, q i t x * inner ℝ (v i x)
        (gradient (chemicalPotential (q i t) (U i (p t))) x) ∂volume) +
        ∫ x, q i t x * fderiv ℝ (fun a ↦ U i a x) (p t) (pdot t) ∂volume) t := by
    intro i
    let d := LocalEnergyDomination.along_parameter_path volume (q i) (qdot i)
      (U i) p pdot t (data i) (fun u _ ↦ hp u) (fun x u _ ↦ hparam i x (p u))
    exact energy_derivative_of_regular_continuity (q i) (qdot i)
      (fun u ↦ U i (p u))
      (fun u x ↦ fderiv ℝ (fun a ↦ U i a x) (p u) (pdot u)) t (v i) d
      (hpos i) (hq i) (hU i)
      (parameter_rate_integral volume _ _ (p t) (pdot t) (hgrad i)).1
      (hcontinuity i) (htail i)
  have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ heach i)).const_mul
    ((M : ℝ)⁻¹)
  have hrate : (M : ℝ)⁻¹ * ∑ i,
      ((∫ x, q i t x * inner ℝ (v i x)
        (gradient (chemicalPotential (q i t) (U i (p t))) x) ∂volume) +
        ∫ x, q i t x * fderiv ℝ (fun a ↦ U i a x) (p t) (pdot t) ∂volume) =
      normalizedProductGradientPairing volume (fun i ↦ q i t) U (p t) (pdot t) v := by
    rw [Finset.sum_add_distrib, mul_add,
      averaged_parameter_rate volume (fun i ↦ q i t) U (p t) (pdot t) hgrad]
    exact add_comm _ _
  rw [hrate] at hd
  exact hd

/-- The squared norm of the source gradient in its normalized product metric,
written using the actual density integrals. -/
def normalizedSlopeSquared (ν : Measure E) (q : Fin M → E → ℝ)
    (U : Fin M → A → E → ℝ) (a : A) : ℝ :=
  ‖averagedParameterForce ν q U a‖ ^ 2 + (M : ℝ)⁻¹ * ∑ i,
    ∫ x, q i x * ‖gradient (chemicalPotential (q i) (U i a)) x‖ ^ 2 ∂ν

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The actual normalized product-gradient norm is nonnegative. -/
theorem normalizedSlopeSquared_nonneg (ν : Measure E) (q : Fin M → E → ℝ)
    (U : Fin M → A → E → ℝ) (a : A) (hq : ∀ i x, 0 ≤ q i x) :
    0 ≤ normalizedSlopeSquared ν q U a := by
  exact add_nonneg (sq_nonneg _) (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ ↦ integral_nonneg fun x ↦ mul_nonneg (hq i x) (sq_nonneg _)))

/-- Source de Bruijn identity for the full normalized parameter/law system.
The parameter ODE is `pdot=-average ∫q∇_parameter U`; each law satisfies its
classical Fokker–Planck PDE. Integrability of the Fisher integrands is proved
from the spatial tail conditions, alongside the energy derivative.

No entropy derivative, entropy dissipation or convergence bound is assumed. -/
theorem normalized_product_deBruijn
    (q qdot : Fin M → ℝ → E → ℝ) (U : Fin M → A → E → ℝ)
    (p pdot : ℝ → A) (t : ℝ)
    (data : ∀ i, LocalEnergyDomination volume (q i) (qdot i) (fun u ↦ U i (p u))
      (fun u x ↦ fderiv ℝ (fun a ↦ U i a x) (p u) (pdot u)) t)
    (hp : ∀ u, HasDerivAt p (pdot u) u)
    (hparam : ∀ i x a, DifferentiableAt ℝ (fun b ↦ U i b x) a)
    (hpos : ∀ i x, 0 < q i t x) (hq : ∀ i, ContDiff ℝ 1 (q i t))
    (hU : ∀ i, ContDiff ℝ 1 (U i (p t)))
    (hgrad : ∀ i, Integrable
      (fun x ↦ q i t x • gradient (fun b ↦ U i b x) (p t)) volume)
    (hode : pdot t = -averagedParameterForce volume (fun i ↦ q i t) U (p t))
    (hpde : ∀ i, ∀ᵐ x ∂volume, qdot i t x =
      fluxDivergence (fokkerPlanckFlux (q i t) (U i (p t))) x)
    (htail : ∀ i, NoBoundaryFlux (fokkerPlanckFlux (q i t) (U i (p t)))
      (fun x ↦ chemicalPotential (q i t) (U i (p t)) x + 1)) :
    (∀ i, Integrable
      (fun x ↦ q i t x * ‖gradient (chemicalPotential (q i t) (U i (p t))) x‖ ^ 2)
      volume) ∧
    HasDerivAt (fun u ↦ normalizedDensityEnergy volume (fun i ↦ q i u) U (p u))
      (-normalizedSlopeSquared volume (fun i ↦ q i t) U (p t)) t := by
  let v : Fin M → E → E := fun i x ↦
    -gradient (chemicalPotential (q i t) (U i (p t))) x
  have hvel (i : Fin M) : (fun y ↦ q i t y • v i y) =
      (fun y ↦ -fokkerPlanckFlux (q i t) (U i (p t)) y) := by
    funext y
    simp only [v, fokkerPlanckFlux, smul_neg]
  have hcont : ∀ i, ∀ᵐ x ∂volume,
      qdot i t x = -fluxDivergence (fun y ↦ q i t y • v i y) x := by
    intro i
    filter_upwards [hpde i] with x hx
    rw [hvel i, fluxDivergence_neg, neg_neg, hx]
  have htailv : ∀ i, NoBoundaryFlux (fun y ↦ q i t y • v i y)
      (fun x ↦ chemicalPotential (q i t) (U i (p t)) x + 1) := by
    intro i
    rw [hvel i]
    exact (htail i).neg
  have hd := normalized_product_gradient_representation q qdot U p pdot t v
    data hp hparam hpos hq hU hgrad hcont htailv
  have hrate : normalizedProductGradientPairing volume (fun i ↦ q i t) U
      (p t) (pdot t) v = -normalizedSlopeSquared volume (fun i ↦ q i t) U (p t) := by
    simp only [normalizedProductGradientPairing, normalizedSlopeSquared, hode, v,
      inner_neg_left, real_inner_self_eq_norm_sq, mul_neg, integral_neg,
      Finset.sum_neg_distrib, mul_neg, neg_add_rev]
    ring
  rw [hrate] at hd
  refine ⟨?_, hd⟩
  intro i
  have h := (htail i).integrable_flux_gradient
  simpa only [fokkerPlanckFlux, gradient_add_one, inner_smul_left,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq] using h

end NormalizedProduct

end LatentDiffusion.RegularFlowCalculus
