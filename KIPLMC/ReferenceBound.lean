import KIPLMC.Dynamics
import KIPLMC.Moments
import KineticLangevin.LpConvergence

/-! # KIPLMC1 inherits the shared kinetic comparison

This theorem supplies the paper's three parameter-error terms for concrete
L² integral segments and actual exponential endpoints. Thermal velocity and
Gibbs position reference marginals are explicit. Constructing a stationary
Brownian reference and identifying the independent Gaussian numerical chain
remain necessary for an unconditional theorem about Algorithm 1.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KIPLMC

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The actual pointwise physical particle force, lifted to L². -/
def lpForce {N dθ dx : ℕ} (hN : 0 < N) (U : IPLA.Joint dθ dx → ℝ)
    (L : ℝ≥0) (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U)) :
    Lp (State N dθ dx) 2 P → Lp (State N dθ dx) 2 P :=
  ULA.lpDrift P (gradient (@averagePotential N dθ dx U))
    (averagePotential_gradient_lipschitz hN hdiff hLip)

/-- Sharp KIPLMC1 parameter comparison from actual coupled segments. This
reuses the shared kinetic proof with temperature `1/N`; its hypotheses list
the exact stationary-reference properties still needed by the full sampler. -/
theorem kiplmc1_reference_parameter_bound {N dθ dx : ℕ} (hN : 0 < N)
    (U : IPLA.Joint dθ dx → ℝ) (m : ℝ) (L γ : ℝ≥0)
    (hdiff : Differentiable ℝ U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U)) (hmL : m ≤ (L : ℝ)) (hm : 0 < m)
    (hγ : 0 < (γ : ℝ)) (hfriction : m+(L : ℝ) ≤ (γ : ℝ)^2)
    (h : ℝ) (hh : 0 < h) (hstep : 4*(γ : ℝ)*(L : ℝ)*h ≤ m)
    (S R : ℕ → Lp (State N dθ dx) 2 P × Lp (State N dθ dx) 2 P)
    (A Z W : ℕ → ℝ → Lp (State N dθ dx) 2 P × Lp (State N dθ dx) 2 P)
    (B : ℕ → ℝ → Lp (State N dθ dx) 2 P)
    (hA : ∀ n, Continuous (A n)) (hZ : ∀ n, Continuous (Z n)) (hB : ∀ n, Continuous (B n))
    (hA0 : ∀ n, A n 0 = S n) (hZ0 : ∀ n, Z n 0 = R n) (hZh : ∀ n, Z n h = R (n+1))
    (hupdate : ∀ n, S (n+1) = KineticLangevin.exponentialStep
      (lpForce P hN U L hdiff hLip) γ h (S n) (B n h, ∫ s in 0..h, B n s))
    (heA : ∀ n t, t ∈ Icc 0 h → A n t - A n 0 = -(∫ s in 0..t,
      KineticLangevin.kineticNegativeDrift (lpForce P hN U L hdiff hLip) γ 1 (A n s)) + W n t)
    (heZ : ∀ n t, t ∈ Icc 0 h → Z n t - Z n 0 = -(∫ s in 0..t,
      KineticLangevin.kineticNegativeDrift (lpForce P hN U L hdiff hLip) γ 1 (Z n s)) + W n t)
    (hmild : ∀ n t, t ∈ Icc 0 h → (A n t).1 = KineticLangevin.psi γ 0 t • (A n 0).1 -
      (∫ s in 0..t, Real.exp (-(γ : ℝ)*(t-s)) •
        lpForce P hN U L hdiff hLip (A n s).2) + B n t)
    (hkin : ∀ n t, t ∈ Icc 0 h → (A n t).2-(A n 0).2 = ∫ s in 0..t, (A n s).1)
    (hthermal : ∀ n t, t ∈ Icc 0 h → HasLaw ((Z n t).1) (velocityTarget N dθ dx) P)
    (hstationary : ∀ n, P.map (R n).2 = IPLA.gibbsTarget U)
    (hvelocity : (S 0).1 = (R 0).1)
    (θStar : EuclideanSpace ℝ (Fin dθ)) (hmax : IPLA.IsMarginalMaximizer U θStar) (n : ℕ) :
    Real.sqrt (∫ z, ‖IPLA.parameterCLM z-θStar‖^2 ∂P.map (S n).2) ≤
      Real.sqrt 2 * (1-3*m*h/(4*(γ : ℝ)))^n * ‖(S 0).2-(R 0).2‖ +
      (L : ℝ)*h*(Real.sqrt 2 * Real.sqrt (((dθ : ℝ)+(N : ℝ)*(dx : ℝ))/(N : ℝ)))/m +
      Real.sqrt ((dθ : ℝ)/((N : ℝ)*m)) := by
  have ht := KineticLangevin.lp_klmc_reference_wasserstein_bound_of_velocity_norm P
    (@averagePotential N dθ dx U) m L γ (averagePotential_differentiable hdiff)
    (averagePotential_strongConvex hN hsc) (averagePotential_gradient_lipschitz hN hdiff hLip)
    hmL hm hγ hfriction h hh hstep S R A Z W B hA hZ hB hA0 hZ0 hZh hupdate
    heA heZ hmild hkin _ (Real.sqrt_nonneg _)
    (fun k t hkt ↦ (thermal_velocity_Lp_norm P hN (Z k t).1 (hthermal k t hkt)).le)
    (IPLA.gibbsTarget U) hstationary hvelocity n
  have hfinite : ULA.wasserstein2 (P.map (S n).2) (IPLA.gibbsTarget U) ≠ ⊤ := by
    rw [← hstationary n]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (ULA.wasserstein2_le_Lp_cost P _ _)
  have hc := parameter_concentration hN U m hm hdiff hsc θStar hmax
  have hp := IPLA.projectedRMSReal_le_wasserstein2Real_add
    (@IPLA.parameterCLM N dθ dx) IPLA.norm_parameterCLM_le_one θStar
    _ (Real.sqrt_nonneg _) hfinite hc
  have hf := IPLA.projectedRMS_ne_top (@IPLA.parameterCLM N dθ dx)
    IPLA.norm_parameterCLM_le_one θStar _ hfinite hc
  rw [IPLA.projectedRMSReal_eq_sqrt_integral _ _ _ hf] at hp
  exact hp.trans (add_le_add_left ht _)

end KIPLMC
