import LatentDiffusion.RegularModel
import LatentDiffusion.RegularEvidenceScores
import LatentDiffusion.RegularMeanField
import PBGSO.EmpiricalMeasurability

/-!
# The source full-batch theorem for the actual posterior optimizer

This theorem combines the actual normalized density model, its proved unique
variational optimizer, evidence differentiation, a constructed Gibbs Langevin
reference, independent initial posterior scores, and the actual pointwise Euler
recursion. All finite-cloud and time-step errors are proved. No local-defect,
reference-existence, stationarity, force-residual or zero-score premise remains.
The explicit added assumptions are local domination for differentiating the
normalizers, the posterior initialization laws, and Brownian independence.
-/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace LatentDiffusion.RegularSourceTheorem
open RegularStochastic RegularEvidenceScores

variable {K dθ dz : ℕ}

/-- The actual unique variational optimizer of the normalized tilted model. -/
def optimizerData
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i)) :=
  Classical.choose (RegularModel.existsUnique_variationalOptimizer U hK m hm hdiff hsc)

def optimizerParameter
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i)) : Parameter dθ :=
  (optimizerData hK U m hm hdiff hsc).1

theorem optimizer_maximizes_evidence
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i)) :
    IsLocalMax (RegularEvidence.logEvidence volume (latentPotential U))
      (optimizerParameter hK U m hm hdiff hsc) := by
  have hp := (Classical.choose_spec (RegularModel.existsUnique_variationalOptimizer U hK m hm hdiff hsc)).1
  have hmax := ((RegularModel.densityModel U m hm hdiff hsc).family.global_minimizers_iff hK _ _).mp hp
  have he : (RegularModel.densityModel U m hm hdiff hsc).family.logEvidence =
      RegularEvidence.logEvidence volume (latentPotential U) := rfl
  rw [he] at hmax
  exact Filter.Eventually.of_forall hmax.1

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Actual physical Brownian increments in particle-normalized coordinates. -/
def noiseIncrement
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (h : ℝ) (k : ℕ) :
    Lp (Cloud.State K dθ dz) 2 P :=
  physicalNoise P B hB ((k : ℝ)*h+h)-physicalNoise P B hB ((k : ℝ)*h)

/-- The corrected source theorem with K=M*N datum-particle pairs. The target
is the actual uniquely defined variational optimizer, and the left side is
literally the root mean square error of the pointwise full-batch Euler code.
V is the exact sum of initial posterior parameter-score variances, so V/K² is
computed rather than postulated as an empirical-error bound. -/
theorem full_batch_optimizer_rms
    {M N : ℕ} (hMN : 0 < M*N)
    (U : Fin (M*N) → Cloud.Joint dθ dz → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) (hs : StableStep m L h)
    (initial : Lp (Latent (M*N) dz) 2 P)
    (hinitial : P.map initial = ULA.gibbsMeasure
      (frozenPotential U (optimizerParameter hMN U m hm hdiff hsc)))
    (hposterior : ∀ i, P.map (fun ω => physicalParticleCLM i
        ((packLp P (optimizerParameter hMN U m hm hdiff hsc) initial) ω)) =
      RegularEvidence.posterior volume (latentPotential U i) (optimizerParameter hMN U m hm hdiff hsc))
    (data : ∀ i, RegularEvidence.LocalNormalizerRegularity volume (latentPotential U i)
      (optimizerParameter hMN U m hm hdiff hsc))
    (hindScores : iIndepFun (fun i ω => scoreLp P U L hLip
      (packLp P (optimizerParameter hMN U m hm hdiff hsc) initial) i ω) P)
    (B : (Fin (M*N) × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hscalar : ∀ s : ℝ, 0 < s → iIndepFun (fun p : ℕ × (Fin (M*N) × Fin dz) => fun ω =>
      ULA.Hilbert.brownianEulerNoise P B hB s p.1 ω p.2) P)
    (hind : ∀ s : ℝ, 0 < s → IndepFun initial
      (fun ω n => ULA.Hilbert.brownianEulerNoise P B hB s n ω) P)
    (x₀ : Lp (Cloud.State (M*N) dθ dz) 2 P) (n : ℕ) :
    Real.sqrt (∫ ω, ‖IPLA.parameterCLM
      (eulerTrajectory (Cloud.meanForce U) h
        (fun k => noiseIncrement P B hB h k ω) (x₀ ω) n)-
      optimizerParameter hMN U m hm hdiff hsc‖^2 ∂P) ≤
      (1-m*h/2)^n * ‖x₀-packLp P (optimizerParameter hMN U m hm hdiff hsc) initial‖ +
      (2/m) * Real.sqrt ((1/((M*N : ℕ) : ℝ))^2 *
        scoreVarianceBudget P U L hLip (packLp P (optimizerParameter hMN U m hm hdiff hsc) initial)) +
      (L : ℝ)/m * (h*Real.sqrt ((L : ℝ)*(dz : ℝ))+
        (4/3 : ℝ)*Real.sqrt (2*(dz : ℝ))*Real.sqrt h) := by
  let a := optimizerParameter hMN U m hm hdiff hsc
  let S := sourceReference P hMN U m L hm hdiff hsc hLip a initial hinitial B hB hscalar hind
  have hS0 : S.path 0=packLp P a initial :=
    sourceReference_initial P hMN U m L hm hdiff hsc hLip a initial hinitial B hB hscalar hind
  have hmeas (i : Fin (M*N)) : Measurable (fun z => Real.exp (-latentPotential U i a z)) :=
    (Real.continuous_exp.comp ((RegularModel.slice_differentiable (U i) (hdiff i) a).continuous.neg)).measurable
  have hZ (i : Fin (M*N)) : 0 < RegularEvidence.normalizer volume (latentPotential U i) a :=
    IPLA.marginalIntegral_pos (U i) m hm (hdiff i) (hsc i) a
  have hopt := sum_score_means_eq_zero_of_evidence_maximum P hMN volume U L hdiff hLip
    (packLp P a initial) a (parameterOutput_packLp P a initial) hposterior data hmeas hZ
      (optimizer_maximizes_evidence hMN U m hm hdiff hsc)
  have hb := full_batch_parameter_bound P hMN U m h L hdiff hsc hLip hs B hB S
    (by rw [hS0]; exact hindScores) (by rw [hS0]; exact hopt) x₀ a
    (by rw [hS0]; exact parameterOutput_packLp P a initial) n
  rw [hS0,physicalNoiseScale_eq hMN] at hb
  have hG := initial_frozen_drift_bound P hMN U m L hm hdiff hsc hLip a initial hinitial
  have htime := mul_le_mul_of_nonneg_left
    (add_le_add_right (mul_le_mul_of_nonneg_left hG hs.positive.le)
      ((4/3 : ℝ)*Real.sqrt (2*(dz : ℝ))*Real.sqrt h)) (div_nonneg L.coe_nonneg hm.le)
  let ξ := noiseIncrement (dθ := dθ) P B hB h
  let F := particleForce P hMN U m L hdiff hsc hLip
  change ‖parameterOutput P (eulerTrajectory F h ξ x₀ n)-constantL2 P a‖ ≤ _ at hb
  have hrms := parameterOutput_rms P (eulerTrajectory F h ξ x₀ n) a
  have hpath := lifted_eulerTrajectory_coe P
    (Cloud.meanForce_regular hMN U m L hdiff hsc hLip) h ξ x₀ n
  have hlhs : Real.sqrt (∫ ω, ‖IPLA.parameterCLM
      (eulerTrajectory (Cloud.meanForce U) h (fun k => ξ k ω) (x₀ ω) n)-a‖^2 ∂P) =
      ‖parameterOutput P (eulerTrajectory F h ξ x₀ n)-constantL2 P a‖ := by
    rw [hrms]
    congr 1
    apply integral_congr_ae
    filter_upwards [hpath] with ω hω
    change (eulerTrajectory F h ξ x₀ n) ω = _ at hω
    rw [hω]
  rw [hlhs]
  dsimp only [ξ, F, noiseIncrement, a] at *
  linarith only [hb, htime]

/-- A primitive per-copy centered second-moment bound gives an explicit budget
linear in the number of copies. It is independent of any empirical error. -/
theorem scoreVarianceBudget_le
    (U : Fin K → Cloud.Joint dθ dz → ℝ) (L : ℝ≥0)
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (X : Lp (Cloud.State K dθ dz) 2 P) (V₀ : ℝ)
    (hvar : ∀ i, ‖scoreLp P U L hLip X i-
      constantL2 P (∫ ω, scoreLp P U L hLip X i ω ∂P)‖^2 ≤ V₀) :
    scoreVarianceBudget P U L hLip X ≤ (K : ℝ)*V₀ := by
  exact (Finset.sum_le_sum (fun i _ => hvar i)).trans_eq (by simp)

theorem score_sampling_rate
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ) (L : ℝ≥0)
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (X : Lp (Cloud.State K dθ dz) 2 P) (V₀ : ℝ)
    (hvar : ∀ i, ‖scoreLp P U L hLip X i-
      constantL2 P (∫ ω, scoreLp P U L hLip X i ω ∂P)‖^2 ≤ V₀) :
    Real.sqrt ((1/(K : ℝ))^2*scoreVarianceBudget P U L hLip X) ≤ Real.sqrt (V₀/K) := by
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ (1/(K : ℝ))^2*((K : ℝ)*V₀) := mul_le_mul_of_nonneg_left
      (scoreVarianceBudget_le P U L hLip X V₀ hvar) (sq_nonneg _)
    _ = _ := by field_simp

/-- The corrected paper rate with K=M*N, an arbitrary initial algorithm
state, and a primitive per-copy posterior score variance V₀. The resulting
finite-particle term is exactly 2 sqrt(V₀/(M*N))/m. -/
theorem full_batch_optimizer_rms_rate
    {M N : ℕ} (hMN : 0 < M*N)
    (U : Fin (M*N) → Cloud.Joint dθ dz → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) (hs : StableStep m L h)
    (initial : Lp (Latent (M*N) dz) 2 P)
    (hinitial : P.map initial = ULA.gibbsMeasure
      (frozenPotential U (optimizerParameter hMN U m hm hdiff hsc)))
    (hposterior : ∀ i, P.map (fun ω => physicalParticleCLM i
        ((packLp P (optimizerParameter hMN U m hm hdiff hsc) initial) ω)) =
      RegularEvidence.posterior volume (latentPotential U i) (optimizerParameter hMN U m hm hdiff hsc))
    (data : ∀ i, RegularEvidence.LocalNormalizerRegularity volume (latentPotential U i)
      (optimizerParameter hMN U m hm hdiff hsc))
    (hindScores : iIndepFun (fun i ω => scoreLp P U L hLip
      (packLp P (optimizerParameter hMN U m hm hdiff hsc) initial) i ω) P)
    (B : (Fin (M*N) × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hscalar : ∀ s : ℝ, 0 < s → iIndepFun (fun p : ℕ × (Fin (M*N) × Fin dz) => fun ω =>
      ULA.Hilbert.brownianEulerNoise P B hB s p.1 ω p.2) P)
    (hind : ∀ s : ℝ, 0 < s → IndepFun initial
      (fun ω n => ULA.Hilbert.brownianEulerNoise P B hB s n ω) P)
    (V₀ : ℝ)
    (hvar : ∀ i, ‖scoreLp P U L hLip
        (packLp P (optimizerParameter hMN U m hm hdiff hsc) initial) i-
      constantL2 P (∫ ω, scoreLp P U L hLip
        (packLp P (optimizerParameter hMN U m hm hdiff hsc) initial) i ω ∂P)‖^2 ≤ V₀)
    (x₀ : Lp (Cloud.State (M*N) dθ dz) 2 P) (n : ℕ) :
    Real.sqrt (∫ ω, ‖IPLA.parameterCLM
      (eulerTrajectory (Cloud.meanForce U) h
        (fun k => noiseIncrement P B hB h k ω) (x₀ ω) n)-
      optimizerParameter hMN U m hm hdiff hsc‖^2 ∂P) ≤
      (1-m*h/2)^n * ‖x₀-packLp P (optimizerParameter hMN U m hm hdiff hsc) initial‖ +
      (2/m) * Real.sqrt (V₀/((M*N : ℕ) : ℝ)) +
      (L : ℝ)/m * (h*Real.sqrt ((L : ℝ)*(dz : ℝ))+
        (4/3 : ℝ)*Real.sqrt (2*(dz : ℝ))*Real.sqrt h) := by
  have hb := full_batch_optimizer_rms P hMN U m h L hm hdiff hsc hLip hs initial hinitial
    hposterior data hindScores B hB hscalar hind x₀ n
  have hv := score_sampling_rate P hMN U L hLip
    (packLp P (optimizerParameter hMN U m hm hdiff hsc) initial) V₀ hvar
  have hv' := mul_le_mul_of_nonneg_left hv (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm.le)
  exact hb.trans (by linarith only [hv'])

/-- Dataset potentials repeated once for each of N particles per datum. -/
def replicatePotentials {M N : ℕ} (U : Fin M → Cloud.Joint dθ dz → ℝ) :
    Fin (M*N) → Cloud.Joint dθ dz → ℝ := fun k => U k.divNat

theorem sum_divNat {M N : ℕ} (g : Fin M → ℝ) :
    (∑ k : Fin (M*N), g k.divNat) = (N : ℝ)*∑ i : Fin M, g i := by
  have hs := (finProdFinEquiv (m := M) (n := N)).sum_comp (fun k => g k.divNat)
  have hi (ij : Fin M × Fin N) : g ((finProdFinEquiv ij).divNat) = g ij.1 := by
    change g ((finProdFinEquiv.symm (finProdFinEquiv ij)).1)=g ij.1
    rw [Equiv.symm_apply_apply]
  simp_rw [hi] at hs
  rw [← hs,Fintype.sum_prod_type]
  simp [Finset.sum_mul,mul_comm]

/-- Replicating data potentials changes neither average evidence nor its
optimizer; K=M*N in the numerical code has the original M-datum target. -/
theorem replicated_averageMarginalPotential {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (U : Fin M → Cloud.Joint dθ dz → ℝ) (a : Parameter dθ) :
    averageMarginalPotential (replicatePotentials (N := N) U) a = averageMarginalPotential U a := by
  unfold averageMarginalPotential replicatePotentials
  rw [sum_divNat (N := N) (fun i => IPLA.marginalPotential (U i) a)]
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hM)
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  push_cast
  field_simp

theorem optimizer_minimizes_marginal
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (hm : 0 < m) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i)) :
    ∀ b, averageMarginalPotential U (optimizerParameter hK U m hm hdiff hsc) ≤
      averageMarginalPotential U b := by
  have hp := (Classical.choose_spec (RegularModel.existsUnique_variationalOptimizer U hK m hm hdiff hsc)).1
  have hmax := ((RegularModel.densityModel U m hm hdiff hsc).family.global_minimizers_iff hK _ _).mp hp
  intro b
  have he := hmax.1 b
  rw [RegularModel.densityModel_logEvidence,RegularModel.densityModel_logEvidence] at he
  exact neg_le_neg_iff.mp he

theorem optimizer_replication {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (U : Fin M → Cloud.Joint dθ dz → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i)) :
    optimizerParameter (Nat.mul_pos hM hN) (replicatePotentials (N := N) U) m hm
      (fun i => hdiff i.divNat) (fun i => hsc i.divNat) =
        optimizerParameter hM U m hm hdiff hsc := by
  have ha := optimizer_minimizes_marginal hM U m hm hdiff hsc
  have hb := optimizer_minimizes_marginal (Nat.mul_pos hM hN) (replicatePotentials (N := N) U)
    m hm (fun i => hdiff i.divNat) (fun i => hsc i.divNat)
  simp_rw [replicated_averageMarginalPotential hM hN] at hb
  exact (averageMarginalPotential_strongConvex U hM m hm hdiff hsc).strictConvexOn hm
    |>.eq_of_isMinOn (fun x _ => hb x) (fun x _ => ha x) (mem_univ _) (mem_univ _)

/-- Connected continuous-time source theorem: the target is the actual unique
variational optimizer and the stationary comparison process is constructed.
Evidence differentiation proves posterior score cancellation internally; no
reference or optimizer-identification premise is supplied. -/
theorem meanField_actual_optimizer_convergence
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (initial : Lp (Latent K dz) 2 P)
    (hinitial : P.map initial = ULA.gibbsMeasure
      (frozenPotential U (optimizerParameter hK U m hm hdiff hsc)))
    (hposterior : ∀ i, P.map (fun ω => physicalParticleCLM i
        ((packLp P (optimizerParameter hK U m hm hdiff hsc) initial) ω)) =
      RegularEvidence.posterior volume (latentPotential U i)
        (optimizerParameter hK U m hm hdiff hsc))
    (data : ∀ i, RegularEvidence.LocalNormalizerRegularity volume (latentPotential U i)
      (optimizerParameter hK U m hm hdiff hsc))
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hscalar : ∀ s : ℝ, 0 < s → iIndepFun (fun p : ℕ × (Fin K × Fin dz) => fun ω =>
      ULA.Hilbert.brownianEulerNoise P B hB s p.1 ω p.2) P)
    (hind : ∀ s : ℝ, 0 < s → IndepFun initial
      (fun ω n => ULA.Hilbert.brownianEulerNoise P B hB s n ω) P)
    (Y : ℝ → Lp (Cloud.State K dθ dz) 2 P) (hY : Continuous Y)
    (hYe : ∀ t, 0 ≤ t → Y t - Y 0 =
      -(∫ r in 0..t, RegularMeanField.force P
        (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (Y r)) + physicalNoise P B hB t)
    (a₀ : Parameter dθ) (ha₀ : parameterOutput P (Y 0) = constantL2 P a₀)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖parameterOutput P (Y t) - constantL2 P (optimizerParameter hK U m hm hdiff hsc)‖ ≤
      Real.exp (-m * t) *
        ‖Y 0 - packLp P (optimizerParameter hK U m hm hdiff hsc) initial‖ := by
  let a := optimizerParameter hK U m hm hdiff hsc
  let S := sourceReference P hK U m L hm hdiff hsc hLip a initial hinitial B hB hscalar hind
  have hS0 : S.path 0 = packLp P a initial :=
    sourceReference_initial P hK U m L hm hdiff hsc hLip a initial hinitial B hB hscalar hind
  have hmeas (i : Fin K) : Measurable (fun z => Real.exp (-latentPotential U i a z)) :=
    (Real.continuous_exp.comp
      ((RegularModel.slice_differentiable (U i) (hdiff i) a).continuous.neg)).measurable
  have hZ (i : Fin K) : 0 < RegularEvidence.normalizer volume (latentPotential U i) a :=
    IPLA.marginalIntegral_pos (U i) m hm (hdiff i) (hsc i) a
  have hopt := sum_score_means_eq_zero_of_evidence_maximum P hK volume U L hdiff hLip
    (packLp P a initial) a (parameterOutput_packLp P a initial) hposterior data hmeas hZ
      (optimizer_maximizes_evidence hK U m hm hdiff hsc)
  have he := RegularMeanField.meanField_optimizer_convergence P hK U m L hdiff hsc hLip
    B hB S (by rw [hS0]; exact hopt) a
    (by rw [hS0]; exact parameterOutput_packLp P a initial) Y hY hYe a₀ ha₀ t ht
  simpa only [hS0] using he

/-- Parameter plus the per-datum empirical transport cost in the manuscript's
normalized product metric. The particle pairing is synchronous in time. -/
def empiricalProductDistanceSq {M N : ℕ}
    (x y : Cloud.State (M * N) dθ dz) : ℝ :=
  ‖IPLA.parameterCLM x - IPLA.parameterCLM y‖ ^ 2 + (M : ℝ)⁻¹ *
    ∑ i : Fin M, ULA.wasserstein2Real
      (PBGSO.Model.empiricalLaw N (fun j => physicalParticleCLM (finProdFinEquiv (i, j)) x))
      (PBGSO.Model.empiricalLaw N (fun j => physicalParticleCLM (finProdFinEquiv (i, j)) y)) ^ 2

@[simp] theorem physicalParticle_apply (i : Fin K) (x : Cloud.State K dθ dz) (j : Fin dz) :
    physicalParticleCLM i x j = Real.sqrt (K : ℝ) * x (Sum.inr (i, j)) := rfl

/-- The normalized physical particle pairing is exactly the cloud Hilbert
energy; the reciprocal-sqrt(K) scaling loses no coordinate or factor. -/
theorem normalized_physical_energy (hK : 0 < K) (x y : Cloud.State K dθ dz) :
    ‖IPLA.parameterCLM x - IPLA.parameterCLM y‖ ^ 2 + (K : ℝ)⁻¹ *
      (∑ i : Fin K, ‖physicalParticleCLM i x - physicalParticleCLM i y‖ ^ 2) = ‖x - y‖ ^ 2 := by
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  simp only [← map_sub, EuclideanSpace.real_norm_sq_eq, IPLA.parameterCLM_apply,
    physicalParticle_apply, mul_pow, Real.sq_sqrt (Nat.cast_nonneg K),
    Fintype.sum_sum_type, Fintype.sum_prod_type, ← Finset.mul_sum]
  rw [← mul_assoc, inv_mul_cancel₀ hK0, one_mul]

/-- A genuine indexwise coupling bounds each per-datum empirical W₂ cost.
This holds for every pair of clouds, with no independence requirement. -/
theorem empiricalProductDistanceSq_le {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (x y : Cloud.State (M * N) dθ dz) :
    empiricalProductDistanceSq x y ≤ ‖x - y‖ ^ 2 := by
  have hpair (i : Fin M) := PBGSO.empiricalCloud_wasserstein_sq_le N hN
    (fun j => physicalParticleCLM (finProdFinEquiv (i, j)) x)
    (fun j => physicalParticleCLM (finProdFinEquiv (i, j)) y)
  have hs := (finProdFinEquiv (m := M) (n := N)).sum_comp
    (fun k => ‖physicalParticleCLM k x - physicalParticleCLM k y‖ ^ 2)
  rw [Fintype.sum_prod_type] at hs
  calc
    empiricalProductDistanceSq x y ≤
      ‖IPLA.parameterCLM x - IPLA.parameterCLM y‖ ^ 2 + (M : ℝ)⁻¹ *
        ∑ i : Fin M, (N : ℝ)⁻¹ * ∑ j : Fin N,
          ‖physicalParticleCLM (finProdFinEquiv (i, j)) x -
            physicalParticleCLM (finProdFinEquiv (i, j)) y‖ ^ 2 := by
      unfold empiricalProductDistanceSq
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpair i))
        (inv_nonneg.mpr (Nat.cast_nonneg M)))
    _ = ‖IPLA.parameterCLM x - IPLA.parameterCLM y‖ ^ 2 + ((M * N : ℕ) : ℝ)⁻¹ *
        ∑ k, ‖physicalParticleCLM k x - physicalParticleCLM k y‖ ^ 2 := by
      rw [← Finset.mul_sum, hs, Nat.cast_mul, mul_inv_rev]
      ring
    _ = _ := normalized_physical_energy (Nat.mul_pos hM hN) x y

theorem empiricalProductDistanceSq_nonneg {M N : ℕ}
    (x y : Cloud.State (M * N) dθ dz) : 0 ≤ empiricalProductDistanceSq x y := by
  unfold empiricalProductDistanceSq
  positivity

theorem empiricalProductDistanceSq_measurable {M N : ℕ} (hN : 0 < N) :
    Measurable (fun p : Cloud.State (M * N) dθ dz × Cloud.State (M * N) dθ dz =>
      empiricalProductDistanceSq p.1 p.2) := by
  let : NeZero N := ⟨hN.ne'⟩
  unfold empiricalProductDistanceSq
  apply Measurable.add
  · fun_prop
  · apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i _
    apply Measurable.pow_const
    let cloud : (Cloud.State (M * N) dθ dz × Cloud.State (M * N) dθ dz) →
        (Fin N → EuclideanSpace ℝ (Fin dz)) × (Fin N → EuclideanSpace ℝ (Fin dz)) :=
      fun p => ((fun j => physicalParticleCLM (finProdFinEquiv (i, j)) p.1),
        (fun j => physicalParticleCLM (finProdFinEquiv (i, j)) p.2))
    have hc : Measurable cloud := by
      apply Measurable.prodMk
      · exact Measurable.of_eval fun j =>
          (physicalParticleCLM (finProdFinEquiv (i, j))).continuous.measurable.comp measurable_fst
      · exact Measurable.of_eval fun j =>
          (physicalParticleCLM (finProdFinEquiv (i, j))).continuous.measurable.comp measurable_snd
    have hm : Measurable (fun z : (Fin N → EuclideanSpace ℝ (Fin dz)) ×
        (Fin N → EuclideanSpace ℝ (Fin dz)) =>
        (ULA.wasserstein2 (PBGSO.Model.empiricalLaw N z.1) (PBGSO.Model.empiricalLaw N z.2)).toReal) :=
      ENNReal.measurable_toReal.comp
        (PBGSO.EmpiricalTransportMeasurable.empirical_wasserstein_measurable
          (H := EuclideanSpace ℝ (Fin dz)) N)
    convert hm.comp hc using 1
    funext p
    rfl

/-- The empirical-product RMS is a genuine integrable expectation and is
bounded by the normalized L² cloud distance. No optimal-coupling identity or
transport measurability assumption is supplied. -/
theorem empiricalProduct_rms_le_l2 {M N : ℕ} (hM : 0 < M) (hN : 0 < N)
    (X Y : Lp (Cloud.State (M * N) dθ dz) 2 P) :
    Real.sqrt (∫ ω, empiricalProductDistanceSq (X ω) (Y ω) ∂P) ≤ ‖X - Y‖ := by
  have hm : AEStronglyMeasurable (fun ω => empiricalProductDistanceSq (X ω) (Y ω)) P :=
    ((empiricalProductDistanceSq_measurable (dθ := dθ) (dz := dz) hN).comp_aemeasurable
      ((Lp.aestronglyMeasurable X).aemeasurable.prodMk (Lp.aestronglyMeasurable Y).aemeasurable)).aestronglyMeasurable
  have hnorm : Integrable (fun ω => ‖X ω - Y ω‖ ^ 2) P :=
    ((Lp.memLp X).sub (Lp.memLp Y)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hi : Integrable (fun ω => empiricalProductDistanceSq (X ω) (Y ω)) P := by
    apply hnorm.mono' hm
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (empiricalProductDistanceSq_nonneg (X ω) (Y ω))]
      exact empiricalProductDistanceSq_le hM hN (X ω) (Y ω)
  have hb := integral_mono_ae hi hnorm
    (Filter.Eventually.of_forall fun ω => empiricalProductDistanceSq_le hM hN (X ω) (Y ω))
  have he : (∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P) = ‖X - Y‖ ^ 2 := by
    rw [l2_norm_sq_eq_expectation]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub X Y] with ω hω
    simp only [hω, Pi.sub_apply]
  rw [he] at hb
  exact (Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_sq (norm_nonneg _))

theorem physicalParticle_law_eq_of_state_law (i : Fin K)
    (X Y : Lp (Cloud.State K dθ dz) 2 P) (hlaw : P.map X = P.map Y) :
    P.map (fun ω => physicalParticleCLM i (X ω)) =
      P.map (fun ω => physicalParticleCLM i (Y ω)) := by
  change P.map (physicalParticleCLM i ∘ X) = P.map (physicalParticleCLM i ∘ Y)
  rw [← Measure.map_map (physicalParticleCLM i).continuous.measurable (Lp.stronglyMeasurable X).measurable,
    ← Measure.map_map (physicalParticleCLM i).continuous.measurable (Lp.stronglyMeasurable Y).measurable, hlaw]

/-- The connected source result for the entire normalized coupled state.
The returned reference has the actual optimizer and actual posterior laws at
every time; full-state contraction is proved before taking any projection. -/
theorem meanField_actual_state_convergence
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (initial : Lp (Latent K dz) 2 P)
    (hinitial : P.map initial = ULA.gibbsMeasure
      (frozenPotential U (optimizerParameter hK U m hm hdiff hsc)))
    (hposterior : ∀ i, P.map (fun ω => physicalParticleCLM i
        ((packLp P (optimizerParameter hK U m hm hdiff hsc) initial) ω)) =
      RegularEvidence.posterior volume (latentPotential U i)
        (optimizerParameter hK U m hm hdiff hsc))
    (data : ∀ i, RegularEvidence.LocalNormalizerRegularity volume (latentPotential U i)
      (optimizerParameter hK U m hm hdiff hsc))
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hscalar : ∀ s : ℝ, 0 < s → iIndepFun (fun p : ℕ × (Fin K × Fin dz) => fun ω =>
      ULA.Hilbert.brownianEulerNoise P B hB s p.1 ω p.2) P)
    (hind : ∀ s : ℝ, 0 < s → IndepFun initial
      (fun ω n => ULA.Hilbert.brownianEulerNoise P B hB s n ω) P)
    (Y : ℝ → Lp (Cloud.State K dθ dz) 2 P) (hY : Continuous Y)
    (hYe : ∀ t, 0 ≤ t → Y t - Y 0 =
      -(∫ r in 0..t, RegularMeanField.force P
        (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (Y r)) + physicalNoise P B hB t)
    (a₀ : Parameter dθ) (ha₀ : parameterOutput P (Y 0) = constantL2 P a₀)
    : ∃ S : FrozenPosteriorSolution P
        (Cloud.meanForce_regular hK U m L hdiff hsc hLip) B hB,
      S.path 0 = packLp P (optimizerParameter hK U m hm hdiff hsc) initial ∧
      (∀ t, 0 ≤ t → parameterOutput P (S.path t) =
        constantL2 P (optimizerParameter hK U m hm hdiff hsc)) ∧
      (∀ t, 0 ≤ t → ∀ i, P.map (fun ω => physicalParticleCLM i (S.path t ω)) =
        RegularEvidence.posterior volume (latentPotential U i)
          (optimizerParameter hK U m hm hdiff hsc)) ∧
      ∀ t, 0 ≤ t → ‖Y t - S.path t‖ ≤
        Real.exp (-m * t) * ‖Y 0 - packLp P (optimizerParameter hK U m hm hdiff hsc) initial‖ := by
  let a := optimizerParameter hK U m hm hdiff hsc
  let S := sourceReference P hK U m L hm hdiff hsc hLip a initial hinitial B hB hscalar hind
  have hS0 : S.path 0 = packLp P a initial :=
    sourceReference_initial P hK U m L hm hdiff hsc hLip a initial hinitial B hB hscalar hind
  have hmeas (i : Fin K) : Measurable (fun z => Real.exp (-latentPotential U i a z)) :=
    (Real.continuous_exp.comp
      ((RegularModel.slice_differentiable (U i) (hdiff i) a).continuous.neg)).measurable
  have hZ (i : Fin K) : 0 < RegularEvidence.normalizer volume (latentPotential U i) a :=
    IPLA.marginalIntegral_pos (U i) m hm (hdiff i) (hsc i) a
  have hopt := sum_score_means_eq_zero_of_evidence_maximum P hK volume U L hdiff hLip
    (packLp P a initial) a (parameterOutput_packLp P a initial) hposterior data hmeas hZ
      (optimizer_maximizes_evidence hK U m hm hdiff hsc)
  let hF := Cloud.meanForce_regular hK U m L hdiff hsc hLip
  let aPath := fun t => a₀ - ∫ r in 0..t,
    headExtract (ProximalLangevin.lpExpectationCLM P (liftedForce P hF (Y r)))
  have hpa := RegularMeanField.meanField_parameter_deterministic P hF Y hY
    (physicalNoise P B hB) (parameterOutput_noise_zero P B hB) hYe a₀ ha₀
  have hpb (t : ℝ) (ht : 0 ≤ t) : parameterOutput P (S.path t) = constantL2 P a := by
    rw [S.parameter_constant P t ht, hS0]
    exact parameterOutput_packLp P a initial
  refine ⟨S, hS0, hpb, ?_, ?_⟩
  · intro t ht i
    have hlaw := physicalParticle_law_eq_of_state_law P i (S.path t) (S.path 0)
      (S.stationary_law t ht)
    rw [hS0] at hlaw
    exact hlaw.trans (hposterior i)
  · intro t ht
    have hSe := RegularMeanField.frozen_is_meanField P hK U m L hdiff hsc hLip B hB S
      (by rw [hS0]; exact hopt)
    have he := RegularMeanField.meanField_contraction P hF Y S.path (physicalNoise P B hB)
      hY S.continuous hYe hSe aPath (fun _ => a) hpa hpb t ht
    simpa only [hS0] using he

/-- Corrected source empirical-cloud endpoint. A single constructed
synchronous posterior reference carries all times. The true per-datum
empirical W₂ statistic is measurable and integrable, and its RMS contracts at
the same rate as the full normalized cloud coupling. No independent-target
W₂ identity, fixed-time optimality or empirical-error estimate is assumed. -/
theorem meanField_actual_empirical_convergence
    {M N : ℕ} (hK : 0 < M * N) (U : Fin (M * N) → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (initial : Lp (Latent (M * N) dz) 2 P)
    (hinitial : P.map initial = ULA.gibbsMeasure
      (frozenPotential U (optimizerParameter hK U m hm hdiff hsc)))
    (hposterior : ∀ i, P.map (fun ω => physicalParticleCLM i
        ((packLp P (optimizerParameter hK U m hm hdiff hsc) initial) ω)) =
      RegularEvidence.posterior volume (latentPotential U i)
        (optimizerParameter hK U m hm hdiff hsc))
    (data : ∀ i, RegularEvidence.LocalNormalizerRegularity volume (latentPotential U i)
      (optimizerParameter hK U m hm hdiff hsc))
    (B : (Fin (M * N) × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hscalar : ∀ s : ℝ, 0 < s → iIndepFun (fun p : ℕ × (Fin (M * N) × Fin dz) => fun ω =>
      ULA.Hilbert.brownianEulerNoise P B hB s p.1 ω p.2) P)
    (hind : ∀ s : ℝ, 0 < s → IndepFun initial
      (fun ω n => ULA.Hilbert.brownianEulerNoise P B hB s n ω) P)
    (Y : ℝ → Lp (Cloud.State (M * N) dθ dz) 2 P) (hY : Continuous Y)
    (hYe : ∀ t, 0 ≤ t → Y t - Y 0 =
      -(∫ r in 0..t, RegularMeanField.force P
        (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (Y r)) + physicalNoise P B hB t)
    (a₀ : Parameter dθ) (ha₀ : parameterOutput P (Y 0) = constantL2 P a₀)
    : ∃ S : FrozenPosteriorSolution P
        (Cloud.meanForce_regular hK U m L hdiff hsc hLip) B hB,
      S.path 0 = packLp P (optimizerParameter hK U m hm hdiff hsc) initial ∧
      (∀ t, 0 ≤ t → parameterOutput P (S.path t) =
        constantL2 P (optimizerParameter hK U m hm hdiff hsc)) ∧
      (∀ t, 0 ≤ t → ∀ i, P.map (fun ω => physicalParticleCLM i (S.path t ω)) =
        RegularEvidence.posterior volume (latentPotential U i)
          (optimizerParameter hK U m hm hdiff hsc)) ∧
      (∀ t, 0 ≤ t → ‖Y t - S.path t‖ ≤
        Real.exp (-m * t) * ‖Y 0 - packLp P (optimizerParameter hK U m hm hdiff hsc) initial‖) ∧
      ∀ t, 0 ≤ t → Real.sqrt
        (∫ ω, empiricalProductDistanceSq (Y t ω) (S.path t ω) ∂P) ≤
          Real.exp (-m * t) * ‖Y 0 - packLp P (optimizerParameter hK U m hm hdiff hsc) initial‖ := by
  obtain ⟨S, hS0, hparameter, hlaw, hstate⟩ :=
    meanField_actual_state_convergence P hK U m L hm hdiff hsc hLip initial hinitial
      hposterior data B hB hscalar hind Y hY hYe a₀ ha₀
  have hM : 0 < M := Nat.pos_of_ne_zero (by
    intro hzero
    rw [hzero, zero_mul] at hK
    exact (lt_irrefl 0 hK))
  have hN : 0 < N := Nat.pos_of_ne_zero (by
    intro hzero
    rw [hzero, mul_zero] at hK
    exact (lt_irrefl 0 hK))
  refine ⟨S, hS0, hparameter, hlaw, hstate, ?_⟩
  intro t ht
  exact (empiricalProduct_rms_le_l2 P hM hN (Y t) (S.path t)).trans (hstate t ht)

end LatentDiffusion.RegularSourceTheorem
