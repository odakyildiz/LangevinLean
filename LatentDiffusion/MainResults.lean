import LatentDiffusion.Equilibrium
import LatentDiffusion.MiniBatchVariance

/-! # Interacting latent training: explicit error budgets

`K` is the total number of datum-particle pairs (`M*N` in the manuscript).
The force and the actual pointwise Euler recursion are constructed from the
heterogeneous negative log tilted potentials. No independent assumption on
the lifted force's contraction or smoothness is made.

The stationary-reference integral equation, its primitive drift/noise moments,
and orthogonal centered sampling residuals are explicit added hypotheses.
They must be supplied for a posterior-cloud application. In particular this
file does not assert that arbitrary neural potentials satisfy global convexity,
or that Algorithm 1's printed minibatch temperature has the desired target.
-/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace LatentDiffusion

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {K dθ dz : ℕ}

/-- The original pointwise empirical force, lifted to actual random variables. -/
def particleForce (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) :
    Lp (Cloud.State K dθ dz) 2 P → Lp (Cloud.State K dθ dz) 2 P :=
  liftedForce P (Cloud.meanForce_regular hK U m L hdiff hsc hLip)

/-- The physical parameter projection, also on actual square-integrable states. -/
def parameterOutput :
    Lp (Cloud.State K dθ dz) 2 P →L[ℝ] Lp (EuclideanSpace ℝ (Fin dθ)) 2 P :=
  (@IPLA.parameterCLM K dθ dz).compLpL 2 P

omit [IsProbabilityMeasure P] in
theorem parameterOutput_norm_le : ‖parameterOutput (K := K) (dθ := dθ) (dz := dz) P‖ ≤ 1 :=
  (ContinuousLinearMap.norm_compLpL_le _).trans IPLA.norm_parameterCLM_le_one

/-- **New A.** Every iteration obeys one explicit parameter RMS bound, with
separate initialization, finite-particle, time-discretization and centered
stochastic-oracle errors. Here K=M*N. The independent-copy residual assumption
uses zero L² cross moments and a per-copy second moment V; its 1/sqrt(K) rate
is derived. `σ` bounds only the centered oracle innovations. -/
theorem particle_oracle_parameter_bound
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m h G Wbound V σ : ℝ) (L : ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (hs : StableStep m L h) (hG : 0 ≤ G) (hW : 0 ≤ Wbound) (_hV : 0 ≤ V)
    (R : Lp (Cloud.State K dθ dz) 2 P → Lp (Cloud.State K dθ dz) 2 P)
    (hR : LipschitzWith L R)
    (y ξ ζ : ℕ → Lp (Cloud.State K dθ dz) 2 P)
    (Y W : ℕ → ℝ → Lp (Cloud.State K dθ dz) 2 P)
    (x₀ : Lp (Cloud.State K dθ dz) 2 P) (astar : EuclideanSpace ℝ (Fin dθ))
    (hr : IntegralReference R h G Wbound y ξ Y W)
    (fluctuation : ℕ → Fin K → Lp (Cloud.State K dθ dz) 2 P)
    (hres : ∀ n, particleForce P hK U m L hdiff hsc hLip (y n) - R (y n) =
      MiniBatchVariance.average (fluctuation n))
    (horth : ∀ n i j, i ≠ j → inner ℝ (fluctuation n i) (fluctuation n j) = 0)
    (hvariance : ∀ n i, ‖fluctuation n i‖ ^ 2 ≤ V)
    (horacle : HilbertInnovationControl (particleForce P hK U m L hdiff hsc hLip)
      h σ ξ ζ x₀ x₀)
    (htarget : ∀ n, parameterOutput P (y n) = constantL2 P astar) (n : ℕ) :
    ‖parameterOutput P
        (eulerTrajectory (particleForce P hK U m L hdiff hsc hLip) h
          (fun k => ξ k + h • ζ k) x₀ n) - constantL2 P astar‖ ≤
      (1 - m * h / 2) ^ n * ‖x₀ - y 0‖ +
        (2 / m) * Real.sqrt (V / K) +
        (L : ℝ) / m * (h * G + (4 / 3 : ℝ) * Wbound * Real.sqrt h) +
        Real.sqrt (h * σ ^ 2 / m) := by
  have hF := liftedForce_regular P (Cloud.meanForce_regular hK U m L hdiff hsc hLip)
  have hb (k : ℕ) : ‖particleForce P hK U m L hdiff hsc hLip (y k) - R (y k)‖ ≤
      Real.sqrt (V / K) := by
    rw [hres k]
    exact MiniBatchVariance.mean_sum_of_orthogonal_le hK (fluctuation k) V
      (horth k) (hvariance k)
  have ht := stochastic_equilibrium_output (parameterOutput P) (parameterOutput_norm_le P)
    (constantL2 P astar) (particleForce P hK U m L hdiff hsc hLip) R m h
    (Real.sqrt (V / K)) G Wbound σ L hF hR hs (Real.sqrt_nonneg _) hG hW
    y ξ ζ Y W x₀ hr hb horacle htarget n
  convert ht using 1; ring

/-- The output norm in New A is literally the RMS of the physical parameter
error, with integrability ensured by the L² type. -/
theorem parameterOutput_rms (X : Lp (Cloud.State K dθ dz) 2 P)
    (astar : EuclideanSpace ℝ (Fin dθ)) :
    ‖parameterOutput P X - constantL2 P astar‖ =
      Real.sqrt (∫ ω, ‖IPLA.parameterCLM (X ω) - astar‖ ^ 2 ∂P) := by
  have he := l2_norm_sq_eq_expectation P (parameterOutput P X - constantL2 P astar)
  have hi : (∫ ω, ‖(parameterOutput P X - constantL2 P astar) ω‖ ^ 2 ∂P) =
      ∫ ω, ‖IPLA.parameterCLM (X ω) - astar‖ ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (parameterOutput P X) (constantL2 P astar),
      (@IPLA.parameterCLM K dθ dz).coeFn_compLpL X, constantL2_coe P astar]
      with ω hsub hproj hconst
    change (parameterOutput P X) ω = IPLA.parameterCLM (X ω) at hproj
    rw [hsub]
    simp only [Pi.sub_apply, hproj, hconst]
  rw [hi] at he
  rw [← he, Real.sqrt_sq (norm_nonneg _)]

end LatentDiffusion
