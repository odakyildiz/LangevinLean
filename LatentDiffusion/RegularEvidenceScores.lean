import LatentDiffusion.RegularEvidence
import LatentDiffusion.RegularStochastic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-! # Posterior evidence scores in the actual scaled particle cloud

The parameter slice of a joint potential has precisely the parameter block of
its joint gradient. Actual posterior initialization transfers the evidence
first-order condition to the score random variables used by the numerical
theorem. Neither zero empirical means nor an optimizer force identity is an
extra hypothesis of the final theorem.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal

namespace LatentDiffusion.RegularEvidenceScores

open RegularStochastic

variable {K dθ dz : ℕ}

def pair (a : Parameter dθ) (z : EuclideanSpace ℝ (Fin dz)) : Cloud.Joint dθ dz :=
  WithLp.toLp 2 (Sum.elim a z)

@[simp] theorem pair_head (a : Parameter dθ) (z : EuclideanSpace ℝ (Fin dz))
    (j : Fin dθ) : pair a z (Sum.inl j) = a j := rfl

@[simp] theorem pair_tail (a : Parameter dθ) (z : EuclideanSpace ℝ (Fin dz))
    (j : Fin dz) : pair a z (Sum.inr j) = z j := rfl

theorem pair_hasFDerivAt (a : Parameter dθ) (z : EuclideanSpace ℝ (Fin dz)) :
    HasFDerivAt (fun b ↦ pair b z) (headInsert (J := Fin dz)) a := by
  have h := ((headInsert (d := dθ) (J := Fin dz)).hasFDerivAt (x := a)).add_const
    (pair (0 : Parameter dθ) z)
  convert h using 1
  funext b
  ext j
  cases j <;> simp [pair, headInsert]

/-- Taking a parameter gradient of an actual joint potential is exactly
projection of its joint gradient onto the parameter coordinates. -/
theorem parameter_gradient_pair
    (U : Cloud.Joint dθ dz → ℝ) (a : Parameter dθ)
    (z : EuclideanSpace ℝ (Fin dz)) (hU : DifferentiableAt ℝ U (pair a z)) :
    gradient (fun b ↦ U (pair b z)) a = headExtract (gradient U (pair a z)) := by
  apply ext_inner_right ℝ
  intro b
  rw [inner_gradient_left]
  have hd := hU.hasFDerivAt.comp a (pair_hasFDerivAt a z)
  change fderiv ℝ (U ∘ (fun b ↦ pair b z)) a b = _
  rw [hd.fderiv]
  change fderiv ℝ U (pair a z) (headInsert b) = _
  rw [← inner_gradient_left]
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, headInsert_apply, headExtract_apply,
    Sum.elim_inl, Sum.elim_inr, inner_zero_right, Finset.sum_const_zero, add_zero]

def physicalParticleCLM (i : Fin K) :
    Cloud.State K dθ dz →L[ℝ] EuclideanSpace ℝ (Fin dz) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ Real.sqrt (K : ℝ) • Cloud.block x i
      map_add' := by intro x y; ext j; simp [Cloud.block, mul_add]
      map_smul' := by intro c x; ext j; simp [Cloud.block, mul_left_comm] }

theorem joint_eq_pair (i : Fin K) (x : Cloud.State K dθ dz) (a : Parameter dθ)
    (ha : IPLA.parameterCLM x = a) :
    Cloud.joint i x = pair a (physicalParticleCLM i x) := by
  ext j
  cases j with
  | inl j => exact congrArg (fun b ↦ b j) ha
  | inr j => rfl

def latentPotential (U : Fin K → Cloud.Joint dθ dz → ℝ) (i : Fin K)
    (a : Parameter dθ) (z : EuclideanSpace ℝ (Fin dz)) : ℝ := U i (pair a z)

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Deterministic L² parameter output gives the claimed pointwise parameter
value almost everywhere, as needed to identify each actual particle law. -/
theorem parameter_ae_of_output (X : Lp (Cloud.State K dθ dz) 2 P) (a : Parameter dθ)
    (hX : parameterOutput P X = constantL2 P a) :
    ∀ᵐ ω ∂P, IPLA.parameterCLM (X ω) = a := by
  have hp := (@IPLA.parameterCLM K dθ dz).coeFn_compLpL X
  change (parameterOutput P X : Ω → Parameter dθ) =ᵐ[P]
    (fun ω ↦ IPLA.parameterCLM (X ω)) at hp
  rw [hX] at hp
  filter_upwards [hp, constantL2_coe P a] with ω hω hc
  exact hω.symm.trans hc

/-- An initialized particle's actual score mean is the insertion of its
posterior parameter-gradient mean into the cloud parameter block. -/
theorem score_mean_eq_posterior
    (ν : Measure (EuclideanSpace ℝ (Fin dz)))
    (U : Fin K → Cloud.Joint dθ dz → ℝ) (L : ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (X : Lp (Cloud.State K dθ dz) 2 P) (a : Parameter dθ)
    (hX : parameterOutput P X = constantL2 P a) (i : Fin K)
    (hlaw : P.map (fun ω ↦ physicalParticleCLM i (X ω)) =
      RegularEvidence.posterior ν (latentPotential U i) a)
    (hint : Integrable (fun z ↦ gradient (fun b ↦ latentPotential U i b z) a)
      (RegularEvidence.posterior ν (latentPotential U i) a)) :
    (∫ ω, scoreLp P U L hLip X i ω ∂P) =
      headInsert (J := Fin K × Fin dz)
        (∫ z, gradient (fun b ↦ latentPotential U i b z) a
          ∂RegularEvidence.posterior ν (latentPotential U i) a) := by
  let f : EuclideanSpace ℝ (Fin dz) → Parameter dθ :=
    fun z ↦ gradient (fun b ↦ latentPotential U i b z) a
  have hm : AEMeasurable (fun ω ↦ physicalParticleCLM i (X ω)) P :=
    (physicalParticleCLM i).continuous.measurable.comp_aemeasurable
      (Lp.aestronglyMeasurable X).aemeasurable
  have hf : AEStronglyMeasurable f (P.map (fun ω ↦ physicalParticleCLM i (X ω))) := by
    rw [hlaw]
    exact hint.aestronglyMeasurable
  have hi : Integrable (fun ω ↦ f (physicalParticleCLM i (X ω))) P := by
    apply (integrable_map_measure hf hm).mp
    rwa [hlaw]
  have heq : (fun ω ↦ scoreLp P U L hLip X i ω) =ᵐ[P]
      (fun ω ↦ headInsert (J := Fin K × Fin dz) (f (physicalParticleCLM i (X ω)))) := by
    filter_upwards [PBGSO.liftMap_coe P (parameterScore U i)
      (parameterScore_lipschitz U L hLip i) X, parameter_ae_of_output P X a hX]
      with ω hs hp
    change scoreLp P U L hLip X i ω = _ at hs
    rw [hs]
    unfold parameterScore
    rw [joint_eq_pair i (X ω) a hp]
    rw [← parameter_gradient_pair (U i) a _ (hdiff i _)]
    rfl
  rw [integral_congr_ae heq,
    ContinuousLinearMap.integral_comp_comm (headInsert (J := Fin K × Fin dz)) hi]
  congr 1
  have hh := integral_map hm hf
  rw [hlaw] at hh
  exact hh.symm

/-- Evidence optimality proves the exact centering condition used by the
full-batch theorem for an actual posterior-initialized cloud. -/
theorem sum_score_means_eq_zero_of_evidence_maximum
    (hK : 0 < K) (ν : Measure (EuclideanSpace ℝ (Fin dz)))
    (U : Fin K → Cloud.Joint dθ dz → ℝ) (L : ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (X : Lp (Cloud.State K dθ dz) 2 P) (a : Parameter dθ)
    (hX : parameterOutput P X = constantL2 P a)
    (hlaw : ∀ i, P.map (fun ω ↦ physicalParticleCLM i (X ω)) =
      RegularEvidence.posterior ν (latentPotential U i) a)
    (data : ∀ i, RegularEvidence.LocalNormalizerRegularity ν (latentPotential U i) a)
    (hmeas : ∀ i, Measurable (fun z ↦ Real.exp (-latentPotential U i a z)))
    (hZ : ∀ i, 0 < RegularEvidence.normalizer ν (latentPotential U i) a)
    (hmax : IsLocalMax (RegularEvidence.logEvidence ν (latentPotential U)) a) :
    ∑ i, (∫ ω, scoreLp P U L hLip X i ω ∂P) = 0 := by
  have hm := RegularEvidence.sum_posterior_parameter_gradient_eq_zero hK ν
    (latentPotential U) a data hmeas hZ hmax
  have heach (i : Fin K) := score_mean_eq_posterior P ν U L hdiff hLip X a hX i
    (hlaw i) (RegularEvidence.posterior_gradient_integrable ν _ a (data i) (hmeas i) (hZ i))
  simp_rw [heach]
  rw [← map_sum, hm, map_zero]

end LatentDiffusion.RegularEvidenceScores
