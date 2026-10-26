import PBGSO.QuadraticMartingale
import PBGSO.AdditiveWeakRealization

/-! # General diffusion quadratic weak realization from martingale structure

The source drift and diffusion are realized by actual L² processes, with
arbitrary parameter and sampler-state dependence. The optimiser satisfies
its original ODE. The sampler drift residual is an actual martingale.
Only its synchronous increment isometry is an explicit stochastic-integral
interface; the quadratic forward equation is derived.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace Topology
namespace PBGSO.GeneralMartingaleRealization
open PBGSO.QuadraticMartingale

variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- Actual drift/martingale trajectory data. No sampler quadratic forward
identity is a field, and no additive-noise restriction is imposed. -/
structure ModelL2Trajectory (M : Model S Θ Z X I) where
  optimizer : ℝ → S
  sampler : ℝ → Lp Z 2 Q
  drift : ℝ → Lp Z 2 Q
  diffusion : ℝ → I → Lp Z 2 Q
  noise : ℝ → Ω → Z
  sampler_continuous : Continuous sampler
  drift_continuous : Continuous drift
  diffusion_continuous : ∀ i, Continuous (fun t => diffusion t i)
  drift_realizes : ∀ t, 0 ≤ t → drift t =ᵐ[Q]
    fun ω => M.drift (M.parameter (optimizer t)) (sampler t ω)
  diffusion_realizes : ∀ t, 0 ≤ t → ∀ i, diffusion t i =ᵐ[Q]
    fun ω => M.diffusion (M.parameter (optimizer t)) (sampler t ω) i
  martingale : Martingale noise ℱ Q
  noise_realizes : ∀ t, noise t =ᵐ[Q] martingaleResidual Q sampler drift t
  adapted : ∀ t, AEStronglyMeasurable[ℱ t] (sampler t) Q
  observation_integrable : ∀ t, 0 ≤ t → Integrable
    (fun z => M.observation (M.parameter (optimizer t)) (M.position z)) (Q.map (sampler t))
  optimizer_ode : ∀ t, 0 ≤ t → HasDerivWithinAt optimizer
    (M.optimizerField t (optimizer t) (Q.map (sampler t))) (Ici 0) t

variable {Q ℱ} {M : Model S Θ Z X I}

/-- Actual sampler marginals realize the empty marginal test domain from
the optimiser equation and true L² moment bounds. -/
theorem ModelL2Trajectory.isWeakSolution_empty (U : ModelL2Trajectory Q ℱ M) :
    M.IsWeakSolution ∅ U.optimizer (fun t => Q.map (U.sampler t)) where
  probability := fun t _ => (Measure.isProbabilityMeasure_map_iff
    (Lp.aestronglyMeasurable (U.sampler t)).aemeasurable).mpr inferInstance
  second_moment := fun t _ => lp_law_second_moment Q (U.sampler t)
  gradient_integrable := U.observation_integrable
  optimizer_ode := U.optimizer_ode
  test_integrable := by simp
  generator_integrable := by simp
  forward_equation := by simp

/-- Drift subtraction commutes with the actual residual construction. -/
theorem residual_sub (U V b c : ℝ → Lp Z 2 Q) (hb : Continuous b) (hc : Continuous c) (t : ℝ) :
    martingaleResidual Q (fun r => U r - V r) (fun r => b r - c r) t =
      martingaleResidual Q U b t - martingaleResidual Q V c t := by
  dsimp [martingaleResidual]
  rw [intervalIntegral.integral_sub (hb.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  abel

/-- The actual sampler work is the pullback of weighted drift and diffusion
pairings of the realized L² columns. -/
theorem work_pullback_ae (D : TwistedGeometry S Z) (U V : ModelL2Trajectory Q ℱ M)
    (t : ℝ) (ht : 0 ≤ t) :
    (fun ω => samplerCouplingWork M D (U.optimizer t) (V.optimizer t)
      (U.sampler t ω, V.sampler t ω)) =ᵐ[Q]
    fun ω => ⟪(U.sampler t - V.sampler t) ω,
      D.samplerWeight ((U.drift t - V.drift t) ω)⟫_ℝ +
      (1 / 2 : ℝ) * ∑ i, ⟪(U.diffusion t i - V.diffusion t i) ω,
        D.samplerWeight ((U.diffusion t i - V.diffusion t i) ω)⟫_ℝ := by
  have hσ : ∀ᵐ ω ∂Q, ∀ i,
      (U.diffusion t i - V.diffusion t i) ω =
        M.diffusion (M.parameter (U.optimizer t)) (U.sampler t ω) i -
        M.diffusion (M.parameter (V.optimizer t)) (V.sampler t ω) i := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_sub (U.diffusion t i) (V.diffusion t i),
      U.diffusion_realizes t ht i, V.diffusion_realizes t ht i] with ω hs hu hv
    simp only [hs, Pi.sub_apply, hu, hv]
  filter_upwards [Lp.coeFn_sub (U.sampler t) (V.sampler t),
    Lp.coeFn_sub (U.drift t) (V.drift t), U.drift_realizes t ht, V.drift_realizes t ht,
    hσ] with ω hX hb hu hv hσ
  simp only [hX, hb, Pi.sub_apply, hu, hv, hσ, samplerCouplingWork, TwistedGeometry.samplerSq]

theorem work_pullback_integrable (D : TwistedGeometry S Z) (U V : ModelL2Trajectory Q ℱ M)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω => samplerCouplingWork M D (U.optimizer t) (V.optimizer t)
      (U.sampler t ω, V.sampler t ω)) Q := by
  apply (Integrable.add (lp_weighted_pairing_integrable Q D.samplerWeight _ _)
    ((integrable_finsetSum _ (fun i _ => lp_weighted_pairing_integrable Q D.samplerWeight
      (U.diffusion t i - V.diffusion t i) (U.diffusion t i - V.diffusion t i))).const_mul
        (1 / 2 : ℝ))).congr
  exact (work_pullback_ae D U V t ht).symm

/-- Primitive continuity of model coefficients supplies measurability of
the displayed source generator integrand on its actual joint law. -/
theorem work_continuous (D : TwistedGeometry S Z) (s s' : S)
    (hb : ∀ θ, Continuous (M.drift θ))
    (hσ : ∀ θ i, Continuous (fun z => M.diffusion θ z i)) :
    Continuous (samplerCouplingWork M D s s') := by
  change Continuous (fun zz : Z × Z =>
    ⟪zz.1 - zz.2, D.samplerWeight
      (M.drift (M.parameter s) zz.1 - M.drift (M.parameter s') zz.2)⟫_ℝ +
      (1 / 2 : ℝ) * ∑ i, ⟪M.diffusion (M.parameter s) zz.1 i -
        M.diffusion (M.parameter s') zz.2 i, D.samplerWeight
          (M.diffusion (M.parameter s) zz.1 i - M.diffusion (M.parameter s') zz.2 i)⟫_ℝ)
  fun_prop

theorem work_integrable (D : TwistedGeometry S Z) (U V : ModelL2Trajectory Q ℱ M)
    (hb : ∀ θ, Continuous (M.drift θ))
    (hσ : ∀ θ i, Continuous (fun z => M.diffusion θ z i)) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (samplerCouplingWork M D (U.optimizer t) (V.optimizer t))
      (samplerPairLaw Q (U.sampler t) (V.sampler t)) := by
  apply (integrable_map_measure (work_continuous D _ _ hb hσ).aestronglyMeasurable
    ((Lp.aestronglyMeasurable (U.sampler t)).aemeasurable.prodMk
      (Lp.aestronglyMeasurable (V.sampler t)).aemeasurable)).mpr
  exact work_pullback_integrable D U V t ht

theorem work_integral (D : TwistedGeometry S Z) (U V : ModelL2Trajectory Q ℱ M)
    (hb : ∀ θ, Continuous (M.drift θ))
    (hσ : ∀ θ i, Continuous (fun z => M.diffusion θ z i)) (t : ℝ) (ht : 0 ≤ t) :
    (∫ zz, samplerCouplingWork M D (U.optimizer t) (V.optimizer t) zz
      ∂samplerPairLaw Q (U.sampler t) (V.sampler t)) =
      weightedPairing Q D.samplerWeight (U.sampler t - V.sampler t) (U.drift t - V.drift t) +
      (1 / 2 : ℝ) * ∑ i, weightedPairing Q D.samplerWeight
        (U.diffusion t i - V.diffusion t i) (U.diffusion t i - V.diffusion t i) := by
  rw [samplerPairLaw, integral_map
    ((Lp.aestronglyMeasurable (U.sampler t)).aemeasurable.prodMk
      (Lp.aestronglyMeasurable (V.sampler t)).aemeasurable)
    (work_continuous D _ _ hb hσ).aestronglyMeasurable]
  rw [integral_congr_ae (work_pullback_ae D U V t ht), integral_add
    (lp_weighted_pairing_integrable Q D.samplerWeight _ _)
    ((integrable_finsetSum _ (fun i _ => lp_weighted_pairing_integrable Q D.samplerWeight
      (U.diffusion t i - V.diffusion t i) (U.diffusion t i - V.diffusion t i))).const_mul
        (1 / 2 : ℝ)), integral_const_mul,
      integral_finsetSum _ (fun i _ => lp_weighted_pairing_integrable Q D.samplerWeight
        (U.diffusion t i - V.diffusion t i) (U.diffusion t i - V.diffusion t i))]
  simp only [weightedPairing_apply, lp_weighted_pairing_eq_integral]

/-- Synchronous weighted Itô isometry for the actual difference residual.
This is the stochastic-integral interface, not a quadratic forward equation. -/
def SynchronousIsometry (D : TwistedGeometry S Z) (U V : ModelL2Trajectory Q ℱ M) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t →
    weightedPairing Q D.samplerWeight
      (martingaleResidual Q (fun r => U.sampler r - V.sampler r)
        (fun r => U.drift r - V.drift r) t -
       martingaleResidual Q (fun r => U.sampler r - V.sampler r)
        (fun r => U.drift r - V.drift r) s)
      (martingaleResidual Q (fun r => U.sampler r - V.sampler r)
        (fun r => U.drift r - V.drift r) t -
       martingaleResidual Q (fun r => U.sampler r - V.sampler r)
        (fun r => U.drift r - V.drift r) s) =
      ∫ r in s..t, diffusionEnergy Q D.samplerWeight
        (fun u i => U.diffusion u i - V.diffusion u i) r

/-- The sampler quadratic forward equation for arbitrary source diffusion
columns follows from actual martingales and synchronous increment isometry. -/
theorem pair_quadratic_forward (D : TwistedGeometry S Z) (U V : ModelL2Trajectory Q ℱ M)
    (hb : ∀ θ, Continuous (M.drift θ))
    (hσ : ∀ θ i, Continuous (fun z => M.diffusion θ z i))
    (hIsometry : SynchronousIsometry D U V) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun r => ∫ zz, couplingQuadratic D zz ∂samplerPairLaw Q (U.sampler r) (V.sampler r))
      (∫ zz, synchronousGenerator M (U.optimizer t) (V.optimizer t) (couplingQuadratic D) zz
        ∂samplerPairLaw Q (U.sampler t) (V.sampler t)) (Ici 0) t := by
  let u : ℝ → Lp Z 2 Q := fun r => U.sampler r - V.sampler r
  let b : ℝ → Lp Z 2 Q := fun r => U.drift r - V.drift r
  let σ : ℝ → I → Lp Z 2 Q := fun r i => U.diffusion r i - V.diffusion r i
  have hrep : ∀ r, (U.noise r - V.noise r) =ᵐ[Q] martingaleResidual Q u b r := by
    intro r
    rw [residual_sub U.sampler V.sampler U.drift V.drift U.drift_continuous V.drift_continuous]
    exact ((U.noise_realizes r).sub (V.noise_realizes r)).trans (Lp.coeFn_sub _ _).symm
  have hadapt (r : ℝ) : AEStronglyMeasurable[ℱ r] (u r) Q := by
    apply ((U.adapted r).sub (V.adapted r)).congr
    exact (Lp.coeFn_sub _ _).symm
  have henergy := expected_energy_hasDerivWithinAt Q ℱ D.samplerWeight D.sampler_symmetric
    u b σ (U.sampler_continuous.sub V.sampler_continuous)
    (U.drift_continuous.sub V.drift_continuous)
    (fun i => (U.diffusion_continuous i).sub (V.diffusion_continuous i))
    (U.noise - V.noise) (U.martingale.sub V.martingale) hrep hadapt hIsometry t ht
  have hcost (r : ℝ) :
      (∫ zz, couplingQuadratic D zz ∂samplerPairLaw Q (U.sampler r) (V.sampler r)) =
        ∫ ω, ⟪u r ω, D.samplerWeight (u r ω)⟫_ℝ ∂Q := by
    change (∫ zz, D.samplerSq (zz.1 - zz.2)
      ∂samplerPairLaw Q (U.sampler r) (V.sampler r)) = _
    rw [samplerPairLaw_cost_integral, lp_weighted_pairing_eq_integral]
  have hgen : (∫ zz, synchronousGenerator M (U.optimizer t) (V.optimizer t)
      (couplingQuadratic D) zz ∂samplerPairLaw Q (U.sampler t) (V.sampler t)) =
      2 * (∫ ω, ⟪u t ω, D.samplerWeight (b t ω)⟫_ℝ ∂Q) +
        ∑ i, ∫ ω, ⟪σ t i ω, D.samplerWeight (σ t i ω)⟫_ℝ ∂Q := by
    simp_rw [synchronousGenerator_quadratic]
    rw [integral_const_mul, work_integral D U V hb hσ t ht]
    simp only [weightedPairing_apply, lp_weighted_pairing_eq_integral]
    dsimp [u, b, σ]
    ring
  rw [hgen, show (fun r => ∫ zz, couplingQuadratic D zz
    ∂samplerPairLaw Q (U.sampler r) (V.sampler r)) =
      (fun r => ∫ ω, ⟪u r ω, D.samplerWeight (u r ω)⟫_ℝ ∂Q) from funext hcost]
  exact henergy

/-- General state/parameter-dependent diffusions realize the actual
quadratic coupled weak solution from martingale trajectories and their
synchronous isometry. Marginal test domains are explicitly empty. -/
theorem isCoupledWeakSolution_quadratic (D : TwistedGeometry S Z)
    (U V : ModelL2Trajectory Q ℱ M)
    (hb : ∀ θ, Continuous (M.drift θ))
    (hσ : ∀ θ i, Continuous (fun z => M.diffusion θ z i))
    (hIsometry : SynchronousIsometry D U V) :
    IsCoupledWeakSolution M ∅ {couplingQuadratic D}
      U.optimizer V.optimizer (fun t => Q.map (U.sampler t)) (fun t => Q.map (V.sampler t))
      (fun t => samplerPairLaw Q (U.sampler t) (V.sampler t)) where
  left := U.isWeakSolution_empty
  right := V.isWeakSolution_empty
  coupling := fun t _ => samplerPairLaw_coupling Q (U.sampler t) (V.sampler t)
  test_integrable := by
    intro φ hφ t _
    have he : φ = couplingQuadratic D := Set.mem_singleton_iff.mp hφ
    subst φ
    exact samplerPairLaw_cost_integrable Q D (U.sampler t) (V.sampler t)
  generator_integrable := by
    intro φ hφ t ht
    have he : φ = couplingQuadratic D := Set.mem_singleton_iff.mp hφ
    subst φ
    have heq := funext (synchronousGenerator_quadratic M D (U.optimizer t) (V.optimizer t))
    rw [heq]
    exact (work_integrable D U V hb hσ t ht).const_mul 2
  forward_equation := by
    intro φ hφ t ht
    have he : φ = couplingQuadratic D := Set.mem_singleton_iff.mp hφ
    subst φ
    exact pair_quadratic_forward D U V hb hσ hIsometry t ht

/-- Source joint monotonicity contracts the actual quadratic coupling
energy of the martingale trajectories. Diffusion remains fully general;
the synchronous stochastic-integral isometry is explicitly required. -/
theorem coupling_energy_decay (D : TwistedGeometry S Z)
    (U V : ModelL2Trajectory Q ℱ M)
    (hb : ∀ θ, Continuous (M.drift θ))
    (hσ : ∀ θ i, Continuous (fun z => M.diffusion θ z i))
    (hIsometry : SynchronousIsometry D U V) (ρ : ℝ)
    (hmono : TwistedJointMonotonicity M D ρ) (t : ℝ) (ht : 0 ≤ t) :
    weakCouplingEnergy D U.optimizer V.optimizer
      (fun r => samplerPairLaw Q (U.sampler r) (V.sampler r)) t ≤
      weakCouplingEnergy D U.optimizer V.optimizer
        (fun r => samplerPairLaw Q (U.sampler r) (V.sampler r)) 0 * Real.exp (-2 * ρ * t) :=
  (isCoupledWeakSolution_quadratic D U V hb hσ hIsometry).energy_decay D
    (by simp) ρ t hmono t ⟨ht, le_rfl⟩

end PBGSO.GeneralMartingaleRealization
