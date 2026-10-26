import PBGSO.Framework
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Stationarity from actual sampler integral equations and pathwise uniqueness

This file makes the stochastic-integral interpretation an explicit argument.
For any supplied integral operator, a solution must satisfy the actual
optimiser ODE and the sampler integral equation. No property of that operator
is assumed: the stationarity proof uses only substitution and uniqueness.
Instantiating it with an Itô integral still requires a separate implementation
of that integral. The frozen sampler invariance input is an actual constant
output law, as in the paper's second assumption, rather than infinitesimal
generator stationarity alone.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace PBGSO

variable {Ω S Θ Z X I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- An integral interpretation supplied by the stochastic implementation.
The same operator is used for every process driven by the same noise.
The separate `C` argument selects the implementation's admissible process
class, for example adapted continuous processes with admissible integrands. -/
abbrev SamplerIntegral := (ℝ → Ω → I → Z) → ℝ → Ω → Z

/-- Actual sampler integral equation for a complete optimiser trajectory.
This retains state- and parameter-dependent diffusion columns. -/
structure IsSamplerIntegralSolution (M : Model S Θ Z X I)
    (J : SamplerIntegral (Ω := Ω) (I := I) (Z := Z))
    (C : (ℝ → S) → (ℝ → Ω → Z) → Prop)
    (s : ℝ → S) (Zp : ℝ → Ω → Z) : Prop where
  admissible : C s Zp
  measurable : ∀ t, 0 ≤ t → Measurable (Zp t)
  continuous_paths : ∀ᵐ ω ∂Q, ContinuousOn (fun t => Zp t ω) (Ici 0)
  drift_integrable : ∀ t, 0 ≤ t → ∀ᵐ ω ∂Q,
    IntervalIntegrable (fun r => M.drift (M.parameter (s r)) (Zp r ω)) volume 0 t
  equation : ∀ t, 0 ≤ t → ∀ᵐ ω ∂Q,
    Zp t ω = Zp 0 ω + (∫ r in 0..t, M.drift (M.parameter (s r)) (Zp r ω)) +
      J (fun r ω i => M.diffusion (M.parameter (s r)) (Zp r ω) i) t ω

/-- A law-consistent integral solution. Its sampler law is the actual
pushforward of the random trajectory, and its optimiser uses that law. -/
structure IsMeanFieldIntegralSolution (M : Model S Θ Z X I)
    (J : SamplerIntegral (Ω := Ω) (I := I) (Z := Z))
    (C : (ℝ → S) → (ℝ → Ω → Z) → Prop)
    (s : ℝ → S) (Zp : ℝ → Ω → Z) : Prop where
  sampler : IsSamplerIntegralSolution Q M J C s Zp
  second_moment : ∀ t, 0 ≤ t → HasFiniteSecondMoment (Q.map (Zp t))
  gradient_integrable : ∀ t, 0 ≤ t → Integrable
    (fun z => M.observation (M.parameter (s t)) (M.position z)) (Q.map (Zp t))
  optimizer_ode : ∀ t, 0 ≤ t →
    HasDerivWithinAt s (M.optimizerField t (s t) (Q.map (Zp t))) (Ici 0) t

/-- Same-driver pathwise uniqueness for the displayed equations. The explicit `C` process class includes
adaptedness and any initial-noise independence or integrand restrictions
required by the intended stochastic implementation. -/
def IntegralPathwiseUniqueness (M : Model S Θ Z X I)
    (J : SamplerIntegral (Ω := Ω) (I := I) (Z := Z))
    (C : (ℝ → S) → (ℝ → Ω → Z) → Prop) : Prop :=
  ∀ s Zp s' Zp', IsMeanFieldIntegralSolution Q M J C s Zp →
    IsMeanFieldIntegralSolution Q M J C s' Zp' →
    s 0 = s' 0 → Zp 0 =ᵐ[Q] Zp' 0 →
    ∀ t, 0 ≤ t → s t = s' t ∧ Zp t =ᵐ[Q] Zp' t

/-- An actual frozen invariant trajectory supplies a constant-optimiser
solution. The invariant sampler law, observation integrability, zero gradient,
and optimiser fixed point are all explicit inputs. -/
theorem frozen_integral_isMeanFieldSolution
    (M : Model S Θ Z X I) (J : SamplerIntegral (Ω := Ω) (I := I) (Z := Z))
    (C : (ℝ → S) → (ℝ → Ω → Z) → Prop)
    (sStar : S) (νStar : Measure Z) (Zstar : ℝ → Ω → Z)
    (hfrozen : IsSamplerIntegralSolution Q M J C (fun _ => sStar) Zstar)
    (hlaw : ∀ t, 0 ≤ t → Q.map (Zstar t) = νStar)
    (hmoment : HasFiniteSecondMoment νStar)
    (hint : Integrable
      (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t, 0 ≤ t → M.optimizer t sStar 0 = 0) :
    IsMeanFieldIntegralSolution Q M J C (fun _ => sStar) Zstar where
  sampler := hfrozen
  second_moment := by intro t ht; simpa [hlaw t ht] using hmoment
  gradient_integrable := by intro t ht; simpa [hlaw t ht] using hint
  optimizer_ode := by
    intro t ht
    simpa [Model.optimizerField, hlaw t ht, hg, hfix t ht] using
      (hasDerivWithinAt_const t (Ici (0 : ℝ)) sStar)

/-- Source stationarity argument directly at the integral-equation level,
with arbitrary multiplicative diffusion and arbitrary optimiser response.
The output law equality is derived from pathwise uniqueness. -/
theorem integral_stationary_of_frozen
    (M : Model S Θ Z X I) (J : SamplerIntegral (Ω := Ω) (I := I) (Z := Z))
    (C : (ℝ → S) → (ℝ → Ω → Z) → Prop)
    (hunique : IntegralPathwiseUniqueness Q M J C)
    (sStar : S) (νStar : Measure Z) (Zstar : ℝ → Ω → Z)
    (hfrozen : IsSamplerIntegralSolution Q M J C (fun _ => sStar) Zstar)
    (hlaw : ∀ t, 0 ≤ t → Q.map (Zstar t) = νStar)
    (hmoment : HasFiniteSecondMoment νStar)
    (hint : Integrable
      (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t, 0 ≤ t → M.optimizer t sStar 0 = 0)
    (s : ℝ → S) (Zp : ℝ → Ω → Z)
    (hsol : IsMeanFieldIntegralSolution Q M J C s Zp)
    (hs : s 0 = sStar) (hz : Zp 0 =ᵐ[Q] Zstar 0) (t : ℝ) (ht : 0 ≤ t) :
    s t = sStar ∧ Q.map (Zp t) = νStar := by
  have hf := frozen_integral_isMeanFieldSolution Q M J C sStar νStar Zstar
    hfrozen hlaw hmoment hint hg hfix
  obtain ⟨hs', hz'⟩ := hunique s Zp (fun _ => sStar) Zstar hsol hf hs hz t ht
  exact ⟨hs', (Measure.map_congr hz').trans (hlaw t ht)⟩

/-- The stationary law is literally the deterministic-optimiser product
law on the complete state, retaining all auxiliary coordinates. -/
theorem integral_stationary_product_law
    [MeasurableSpace S] (M : Model S Θ Z X I)
    (J : SamplerIntegral (Ω := Ω) (I := I) (Z := Z))
    (C : (ℝ → S) → (ℝ → Ω → Z) → Prop)
    (hunique : IntegralPathwiseUniqueness Q M J C)
    (sStar : S) (νStar : Measure Z) (Zstar : ℝ → Ω → Z)
    (hfrozen : IsSamplerIntegralSolution Q M J C (fun _ => sStar) Zstar)
    (hlaw : ∀ t, 0 ≤ t → Q.map (Zstar t) = νStar)
    (hmoment : HasFiniteSecondMoment νStar)
    (hint : Integrable
      (fun z => M.observation (M.parameter sStar) (M.position z)) νStar)
    (hg : M.meanGradient νStar sStar = 0)
    (hfix : ∀ t, 0 ≤ t → M.optimizer t sStar 0 = 0)
    (s : ℝ → S) (Zp : ℝ → Ω → Z)
    (hsol : IsMeanFieldIntegralSolution Q M J C s Zp)
    (hs : s 0 = sStar) (hz : Zp 0 =ᵐ[Q] Zstar 0) (t : ℝ) (ht : 0 ≤ t) :
    Q.map (fun ω => (s t, Zp t ω)) = (Measure.dirac sStar).prod νStar := by
  obtain ⟨hopt, hsam⟩ := integral_stationary_of_frozen Q M J C hunique sStar νStar Zstar
    hfrozen hlaw hmoment hint hg hfix s Zp hsol hs hz t ht
  haveI : IsProbabilityMeasure νStar := hsam ▸
    (Measure.isProbabilityMeasure_map_iff (hsol.sampler.measurable t ht).aemeasurable).mpr
      inferInstance
  rw [hopt, Measure.dirac_prod, ← hsam,
    Measure.map_map measurable_prodMk_left (hsol.sampler.measurable t ht)]
  rfl

end PBGSO
