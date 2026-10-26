import PBGSO.ImplementationMetric

/-! # Explicit Euclidean comparisons for the actual implementation metric
The physical Hilbert L² norm is exactly the sum of the four coordinate second
moments under the standard cloud encoding. This derives the bounds
`‖P‖ ≤ 2` and `‖P⁻¹‖ ≤ 1` without independence assumptions, and constructs the
source-A3 contracting metric with the numerical comparisons
`√lower_N / 2` and `2 * √upper_N`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators NNReal ENNReal InnerProductSpace
namespace PBGSO.MethodMetricComparisons
open Methods ImplementationDynamics ConstructedItoParticle

variable {Ω A J : Type*} {N : ℕ} [MeasurableSpace Ω] [Fintype J]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  (Q : Measure Ω)
  (D : ParticleForceData A (EuclideanSpace ℝ J) (EuclideanSpace ℝ (Fin N × J)) N)

/-- The standard cloud encoding preserves the sum of particle squared Euclidean norms. -/
theorem cloud_norm_sq (x : EuclideanSpace ℝ (Fin N × J)) :
    ∑ i, ‖euclideanParticleEncoding N J x i‖^2=‖x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,euclideanParticleEncoding_apply]
  rw [Fintype.sum_prod_type]

/-- The literal kinetic packing has the sum of four squared coordinate norms. -/
theorem momentum_point_norm_sq (hcloud : D.cloud = euclideanParticleEncoding N J)
    (z : ((A × EuclideanSpace ℝ (Fin N × J)) × (A × EuclideanSpace ℝ (Fin N × J)))) :
    ‖(oneEquiv N).symm (momentumEncodedStateEquiv D z)‖^2=
      ‖z.1.1‖^2+‖z.1.2‖^2+‖z.2.1‖^2+‖z.2.2‖^2 := by
  rw [EmpiricalMetric.norm_sq_coordinates]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  change ‖WithLp.toLp 2 (z.2.1,z.1.1)‖^2+
    (∑ i, ‖WithLp.toLp 2 (D.cloud z.2.2 i,D.cloud z.1.2 i)‖^2)=_
  simp_rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖z.2.1‖^2+‖z.1.1‖^2+(∑ i, (‖D.cloud z.2.2 i‖^2+‖D.cloud z.1.2 i‖^2))=_
  rw [hcloud,Finset.sum_add_distrib,cloud_norm_sq,cloud_norm_sq]
  ring

/-- The literal HOL packing has the sum of four squared coordinate norms. -/
theorem higherOrder_point_norm_sq (hcloud : D.cloud = euclideanParticleEncoding N J)
    (z : HOLState A (EuclideanSpace ℝ (Fin N × J))) :
    ‖(oneEquiv N).symm (higherOrderEncodedStateEquiv D z)‖^2=
      ‖z.1‖^2+‖z.2.1‖^2+‖z.2.2.1‖^2+‖z.2.2.2‖^2 := by
  rw [EmpiricalMetric.norm_sq_coordinates]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  change ‖z.1‖^2+
    (∑ i, ‖WithLp.toLp 2 (D.cloud z.2.1 i,
      WithLp.toLp 2 (D.cloud z.2.2.1 i,D.cloud z.2.2.2 i))‖^2)=_
  simp_rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖z.1‖^2+(∑ i, (‖D.cloud z.2.1 i‖^2+(‖D.cloud z.2.2.1 i‖^2+‖D.cloud z.2.2.2 i‖^2)))=_
  rw [hcloud,Finset.sum_add_distrib,Finset.sum_add_distrib,
    cloud_norm_sq,cloud_norm_sq,cloud_norm_sq]
  ring

/-- Actual shared-space kinetic L² packing preserves the sum of four second moments. -/
theorem momentum_lp_norm_sq (hcloud : D.cloud = euclideanParticleEncoding N J)
    (z : ((Lp A 2 Q × Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q) ×
      (Lp A 2 Q × Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q))) :
    ‖momentumPhysicalLpEquiv Q D z‖^2=
      ‖z.1.1‖^2+‖z.1.2‖^2+‖z.2.1‖^2+‖z.2.2‖^2 := by
  let E := oneEquiv (S := HypocoercivePhase A)
    (Z := HypocoercivePhase (EuclideanSpace ℝ J)) N
  have hae : ∀ᵐ ω ∂Q, ‖momentumPhysicalLpEquiv Q D z ω‖^2=
      ‖z.1.1 ω‖^2+‖z.1.2 ω‖^2+‖z.2.1 ω‖^2+‖z.2.2 ω‖^2 := by
    filter_upwards [E.symm.toContinuousLinearMap.coeFn_compLpL (momentumPackLp Q D z),
      momentumPackLp_coe Q D z] with ω h1 h2
    change ‖E.symm.toContinuousLinearMap.compLpL 2 Q (momentumPackLp Q D z) ω‖^2=_
    rw [h1,h2]
    exact momentum_point_norm_sq D hcloud (phaseValue Q z ω)
  have hi₁ := (Lp.memLp z.1.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hi₂ := (Lp.memLp z.1.2).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hi₃ := (Lp.memLp z.2.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hi₄ := (Lp.memLp z.2.2).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  rw [ProximalLangevin.lp_norm_sq_eq_integral Q]
  have e₄ := integral_add ((hi₁.add hi₂).add hi₃) hi₄
  have e₃ := integral_add (hi₁.add hi₂) hi₃
  have e₂ := integral_add hi₁ hi₂
  simp only [Pi.add_apply] at e₄ e₃ e₂
  rw [integral_congr_ae hae,e₄,e₃,e₂]
  simp only [← ProximalLangevin.lp_norm_sq_eq_integral Q]

/-- Actual shared-space HOL L² packing preserves the sum of four second moments. -/
theorem higherOrder_lp_norm_sq (hcloud : D.cloud = euclideanParticleEncoding N J)
    (z : HOLState (Lp A 2 Q) (Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q)) :
    ‖higherOrderPhysicalLpEquiv Q D z‖^2=
      ‖z.1‖^2+‖z.2.1‖^2+‖z.2.2.1‖^2+‖z.2.2.2‖^2 := by
  let E := oneEquiv (S := A) (Z := HigherOrderSampler (EuclideanSpace ℝ J)) N
  have hae : ∀ᵐ ω ∂Q, ‖higherOrderPhysicalLpEquiv Q D z ω‖^2=
      ‖z.1 ω‖^2+‖z.2.1 ω‖^2+‖z.2.2.1 ω‖^2+‖z.2.2.2 ω‖^2 := by
    filter_upwards [E.symm.toContinuousLinearMap.coeFn_compLpL (higherOrderPackLp Q D z),
      higherOrderPackLp_coe Q D z] with ω h1 h2
    change ‖E.symm.toContinuousLinearMap.compLpL 2 Q (higherOrderPackLp Q D z) ω‖^2=_
    rw [h1,h2]
    exact higherOrder_point_norm_sq D hcloud (holValue Q z ω)
  have hi₁ := (Lp.memLp z.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hi₂ := (Lp.memLp z.2.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hi₃ := (Lp.memLp z.2.2.1).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hi₄ := (Lp.memLp z.2.2.2).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  rw [ProximalLangevin.lp_norm_sq_eq_integral Q]
  have e₄ := integral_add ((hi₁.add hi₂).add hi₃) hi₄
  have e₃ := integral_add (hi₁.add hi₂) hi₃
  have e₂ := integral_add hi₁ hi₂
  simp only [Pi.add_apply] at e₄ e₃ e₂
  rw [integral_congr_ae hae,e₄,e₃,e₂]
  simp only [← ProximalLangevin.lp_norm_sq_eq_integral Q]


/-- The kinetic physical L² norm is at most twice the raw maximum coordinate norm. -/
theorem momentum_norm_le_two (hcloud : D.cloud = euclideanParticleEncoding N J)
    (z : ((Lp A 2 Q × Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q) ×
      (Lp A 2 Q × Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q))) :
    ‖momentumPhysicalLpEquiv Q D z‖≤2*‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*‖z‖)).mp
  rw [momentum_lp_norm_sq Q D hcloud]
  have h₁ := (norm_fst_le z.1).trans (norm_fst_le z)
  have h₂ := (norm_snd_le z.1).trans (norm_fst_le z)
  have h₃ := (norm_fst_le z.2).trans (norm_snd_le z)
  have h₄ := (norm_snd_le z.2).trans (norm_snd_le z)
  have h₁' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₁
  have h₂' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₂
  have h₃' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₃
  have h₄' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₄
  nlinarith only [h₁',h₂',h₃',h₄']

/-- The HOL physical L² norm is at most twice the raw maximum coordinate norm. -/
theorem higherOrder_norm_le_two (hcloud : D.cloud = euclideanParticleEncoding N J)
    (z : HOLState (Lp A 2 Q) (Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q)) :
    ‖higherOrderPhysicalLpEquiv Q D z‖≤2*‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*‖z‖)).mp
  rw [higherOrder_lp_norm_sq Q D hcloud]
  have h₁ := norm_fst_le z
  have h₂ := (norm_fst_le z.2).trans (norm_snd_le z)
  have h₃ := ((norm_fst_le z.2.2).trans (norm_snd_le z.2)).trans (norm_snd_le z)
  have h₄ := ((norm_snd_le z.2.2).trans (norm_snd_le z.2)).trans (norm_snd_le z)
  have h₁' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₁
  have h₂' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₂
  have h₃' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₃
  have h₄' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h₄
  nlinarith only [h₁',h₂',h₃',h₄']

/-- The kinetic physical L² norm controls each actual raw coordinate. -/
theorem momentum_norm_ge (hcloud : D.cloud = euclideanParticleEncoding N J)
    (z : ((Lp A 2 Q × Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q) ×
      (Lp A 2 Q × Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q))) :
    ‖z‖≤‖momentumPhysicalLpEquiv Q D z‖ := by
  have he := momentum_lp_norm_sq Q D hcloud z
  have hp := norm_nonneg (momentumPhysicalLpEquiv Q D z)
  rw [Prod.norm_def,Prod.norm_def,Prod.norm_def]
  apply max_le <;> apply max_le
  all_goals nlinarith [sq_nonneg ‖z.1.1‖,sq_nonneg ‖z.1.2‖,
    sq_nonneg ‖z.2.1‖,sq_nonneg ‖z.2.2‖,norm_nonneg z.1.1,
    norm_nonneg z.1.2,norm_nonneg z.2.1,norm_nonneg z.2.2]

/-- The HOL physical L² norm controls each actual raw coordinate. -/
theorem higherOrder_norm_ge (hcloud : D.cloud = euclideanParticleEncoding N J)
    (z : HOLState (Lp A 2 Q) (Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q)) :
    ‖z‖≤‖higherOrderPhysicalLpEquiv Q D z‖ := by
  have he := higherOrder_lp_norm_sq Q D hcloud z
  have hp := norm_nonneg (higherOrderPhysicalLpEquiv Q D z)
  rw [Prod.norm_def,Prod.norm_def,Prod.norm_def]
  apply max_le
  · nlinarith [sq_nonneg ‖z.2.1‖,sq_nonneg ‖z.2.2.1‖,sq_nonneg ‖z.2.2.2‖,norm_nonneg z.1]
  · apply max_le
    · nlinarith [sq_nonneg ‖z.1‖,sq_nonneg ‖z.2.2.1‖,sq_nonneg ‖z.2.2.2‖,norm_nonneg z.2.1]
    · apply max_le
      · nlinarith [sq_nonneg ‖z.1‖,sq_nonneg ‖z.2.1‖,sq_nonneg ‖z.2.2.2‖,norm_nonneg z.2.2.1]
      · nlinarith [sq_nonneg ‖z.1‖,sq_nonneg ‖z.2.1‖,sq_nonneg ‖z.2.2.1‖,norm_nonneg z.2.2.2]

/-- Explicit operator bound for actual kinetic raw-to-physical L² coordinates. -/
theorem momentum_opNorm_le_two (hcloud : D.cloud = euclideanParticleEncoding N J) :
    ‖(momentumPhysicalLpEquiv Q D).toContinuousLinearMap‖≤2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (momentum_norm_le_two Q D hcloud)

/-- Explicit operator bound for actual HOL raw-to-physical L² coordinates. -/
theorem higherOrder_opNorm_le_two (hcloud : D.cloud = euclideanParticleEncoding N J) :
    ‖(higherOrderPhysicalLpEquiv Q D).toContinuousLinearMap‖≤2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (higherOrder_norm_le_two Q D hcloud)

/-- The kinetic physical-to-raw L² inverse is nonexpansive. -/
theorem momentum_inverse_opNorm_le_one (hcloud : D.cloud = euclideanParticleEncoding N J) :
    ‖(momentumPhysicalLpEquiv Q D).symm.toContinuousLinearMap‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  change ‖(momentumPhysicalLpEquiv Q D).symm y‖≤1*‖y‖
  simpa only [ContinuousLinearEquiv.apply_symm_apply,one_mul] using
    momentum_norm_ge Q D hcloud ((momentumPhysicalLpEquiv Q D).symm y)

/-- The HOL physical-to-raw L² inverse is nonexpansive. -/
theorem higherOrder_inverse_opNorm_le_one (hcloud : D.cloud = euclideanParticleEncoding N J) :
    ‖(higherOrderPhysicalLpEquiv Q D).symm.toContinuousLinearMap‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  change ‖(higherOrderPhysicalLpEquiv Q D).symm y‖≤1*‖y‖
  simpa only [ContinuousLinearEquiv.apply_symm_apply,one_mul] using
    higherOrder_norm_ge Q D hcloud ((higherOrderPhysicalLpEquiv Q D).symm y)

section Metrics
variable [IsProbabilityMeasure Q] [FiniteDimensional ℝ A]
  {I : Type*} [Fintype I]

/-- Source A3 constructs the actual kinetic metric with entirely numerical
coordinate comparisons under the standard Euclidean cloud encoding. -/
theorem momentum_metric_explicit (hcloud : D.cloud = euclideanParticleEncoding N J)
    (γ : ℝ) (σ : I → HypocoercivePhase (EuclideanSpace ℝ J))
    (G : TwistedGeometry (HypocoercivePhase A) (HypocoercivePhase (EuclideanSpace ℝ J)))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity (heavyBallModel γ D.F D.G σ) G ρ) :
    ∃ n : ℕ, ∃ T : ((Lp A 2 Q × Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q) ×
      (Lp A 2 Q × Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q)) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin n)) 2 Q,
      (∀ x, (Real.sqrt (EmpiricalMetric.lower N G)/2)*‖x‖≤‖T x‖) ∧
      (∀ x, ‖T x‖≤(2*Real.sqrt (EmpiricalMetric.upper N G))*‖x‖) ∧
      (∀ x y, ⟪T (x-y),T (
        (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) x.2-γ • x.1,x.1)-
        (-coupledForce (D.meanForceLp Q) (D.samplerForceLp Q) y.2-γ • y.1,y.1))⟫_ℝ
          ≤ -ρ*‖T (x-y)‖^2) := by
  classical
  obtain ⟨n,T,hl,hu,hm⟩ := ImplementationMetric.momentum_metric Q D γ σ G ρ hmono
  refine ⟨n,T,?_,?_,hm⟩
  · intro x
    apply le_trans _ (hl x)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    have hden : ‖(momentumPhysicalLpEquiv Q D).symm.toContinuousLinearMap‖+1≤2 := by
      linarith [momentum_inverse_opNorm_le_one Q D hcloud]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      (by positivity : 0<‖(momentumPhysicalLpEquiv Q D).symm.toContinuousLinearMap‖+1) hden
  · intro x
    apply (hu x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    nlinarith [mul_le_mul_of_nonneg_left (momentum_opNorm_le_two Q D hcloud)
      (Real.sqrt_nonneg (EmpiricalMetric.upper N G))]

/-- Source A3 constructs the actual HOL metric with entirely numerical
coordinate comparisons under the standard Euclidean cloud encoding. -/
theorem higherOrder_metric_explicit (hcloud : D.cloud = euclideanParticleEncoding N J)
    (α γ : ℝ) (σ : I → EuclideanSpace ℝ J)
    (G : TwistedGeometry A (HigherOrderSampler (EuclideanSpace ℝ J))) (ρ : ℝ)
    (hmono : TwistedJointMonotonicity (higherOrderModel D.F D.G α γ σ) G ρ) :
    ∃ n : ℕ, ∃ T : HOLState (Lp A 2 Q) (Lp (EuclideanSpace ℝ (Fin N × J)) 2 Q) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin n)) 2 Q,
      (∀ x, (Real.sqrt (EmpiricalMetric.lower N G)/2)*‖x‖≤‖T x‖) ∧
      (∀ x, ‖T x‖≤(2*Real.sqrt (EmpiricalMetric.upper N G))*‖x‖) ∧
      (∀ x y, ⟪T (x-y),T (holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ x-
        holDrift (D.meanForceLp Q) (D.samplerForceLp Q) α γ y)⟫_ℝ ≤ -ρ*‖T (x-y)‖^2) := by
  classical
  obtain ⟨n,T,hl,hu,hm⟩ := ImplementationMetric.higherOrder_metric Q D α γ σ G ρ hmono
  refine ⟨n,T,?_,?_,hm⟩
  · intro x
    apply le_trans _ (hl x)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    have hden : ‖(higherOrderPhysicalLpEquiv Q D).symm.toContinuousLinearMap‖+1≤2 := by
      linarith [higherOrder_inverse_opNorm_le_one Q D hcloud]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _)
      (by positivity : 0<‖(higherOrderPhysicalLpEquiv Q D).symm.toContinuousLinearMap‖+1) hden
  · intro x
    apply (hu x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    nlinarith [mul_le_mul_of_nonneg_left (higherOrder_opNorm_le_two Q D hcloud)
      (Real.sqrt_nonneg (EmpiricalMetric.upper N G))]
end Metrics

end PBGSO.MethodMetricComparisons
