import ProximalLangevin.MeanFieldParticleDrift
import ProximalLangevin.SplittingL2Energy

set_option linter.style.header false

/-! # Constructed iid mean-field copies and their exact drift residual

The copies live on the actual finite product probability space. The reference
parameter is deterministic, its latent coordinates are iid copies, and its
empirical-drift defect is precisely a centered parameter-gradient sample mean.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators RealInnerProductSpace
namespace ProximalLangevin

section Pullback
variable {Ω E F : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {N : ℕ}

/-- A genuine iid copy of a random variable on the finite product space. -/
def iidCopyCLM (i : Fin N) :
    Lp E 2 Q →L[ℝ] Lp E 2 (Measure.pi (fun _ : Fin N => Q)) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun ω : Fin N → Ω => ω i)
    (measurePreserving_eval (fun _ : Fin N => Q) i)).toContinuousLinearMap

theorem iidCopyCLM_coe (i : Fin N) (X : Lp E 2 Q) :
    iidCopyCLM Q i X =ᵐ[Measure.pi (fun _ : Fin N => Q)] fun ω => X (ω i) :=
  Lp.coeFn_compMeasurePreserving X (measurePreserving_eval (fun _ : Fin N => Q) i)

theorem iidCopyCLM_compLp (i : Fin N) (C : E →L[ℝ] F) (X : Lp E 2 Q) :
    iidCopyCLM Q i (C.compLp X) = C.compLp (iidCopyCLM Q i X) := by
  apply Lp.ext
  have hp := (measurePreserving_eval (fun _ : Fin N => Q) i).quasiMeasurePreserving
    |>.ae (C.coeFn_compLp X)
  filter_upwards [iidCopyCLM_coe Q i (C.compLp X),C.coeFn_compLp (iidCopyCLM Q i X),
    iidCopyCLM_coe Q i X,hp] with ω hc hp hx hsrc
  rw [hc,hp,hx,hsrc]

theorem iidCopyCLM_const (i : Fin N) (x : E) :
    iidCopyCLM Q i (Lp.const 2 Q x)=Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) x := by
  apply Lp.ext
  have hp := (measurePreserving_eval (fun _ : Fin N => Q) i).quasiMeasurePreserving
    |>.ae (Lp.coeFn_const (μ := Q) (p := 2) (c := x))
  filter_upwards [iidCopyCLM_coe Q i (Lp.const 2 Q x),
    Lp.coeFn_const (μ := Measure.pi (fun _ : Fin N => Q)) (p := 2) (c := x),hp] with ω hc hp hs
  rw [hc,hp,hs]
  rfl

end Pullback

section Centering
variable {Ω E : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] {N : ℕ}

/-- Center an actual square-integrable random variable by its expectation. -/
def lpCenterCLM : Lp E 2 Q →L[ℝ] Lp E 2 Q :=
  ContinuousLinearMap.id ℝ _-(Lp.constL 2 Q ℝ).comp (lpExpectationCLM Q)

/-- The actual finite-product centered empirical mean as an L² random variable. -/
def iidEmpiricalFluctuation (X : Lp E 2 Q) :
    Lp E 2 (Measure.pi (fun _ : Fin N => Q)) :=
  (N : ℝ)⁻¹ • ∑ i,iidCopyCLM Q i X-
    Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) (lpExpectationCLM Q X)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
theorem iidEmpiricalFluctuation_coe (X : Lp E 2 Q) :
    iidEmpiricalFluctuation Q (N := N) X =ᵐ[Measure.pi (fun _ : Fin N => Q)]
      fun ω => empiricalAverage X ω-(∫ a,X a ∂Q) := by
  have hi : ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => Q),
      ∀ i : Fin N,iidCopyCLM Q i X ω=X (ω i) := ae_all_iff.mpr (fun i => iidCopyCLM_coe Q i X)
  filter_upwards [hi,Lp.coeFn_sub ((N : ℝ)⁻¹ • ∑ i,iidCopyCLM Q i X)
      (Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) (lpExpectationCLM Q X)),
      Lp.coeFn_smul (N : ℝ)⁻¹ (∑ i,iidCopyCLM Q i X),
      Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin N => iidCopyCLM Q i X),
      Lp.coeFn_const (μ := Measure.pi (fun _ : Fin N => Q)) (p := 2)
        (c := lpExpectationCLM Q X)] with ω hi hs ha hsum hc
  rw [iidEmpiricalFluctuation,hs,Pi.sub_apply,ha,Pi.smul_apply,hsum,hc]
  simp only [hi,empiricalAverage,lpExpectationCLM_apply,Function.const_apply]

theorem iidEmpiricalFluctuation_norm (hN : 0<N) (X : Lp E 2 Q) :
    ‖iidEmpiricalFluctuation Q (N := N) X‖=‖lpCenterCLM Q X‖/Real.sqrt (N : ℝ) := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  have hv := iid_empirical_variance Q (fun ω => X ω) (Lp.memLp X) hN
  have hf := iidEmpiricalFluctuation_coe Q (N := N) X
  have hc : lpCenterCLM Q X =ᵐ[Q] fun ω => X ω-(∫ a,X a ∂Q) := by
    filter_upwards [Lp.coeFn_sub X (Lp.const 2 Q (lpExpectationCLM Q X)),
      Lp.coeFn_const (μ := Q) (p := 2) (c := lpExpectationCLM Q X)] with ω hs hm
    rw [lpCenterCLM,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
      Lp.constL_apply,hs,Pi.sub_apply,hm]
    rfl
  have heq : ‖iidEmpiricalFluctuation Q (N := N) X‖^2=‖lpCenterCLM Q X‖^2/(N : ℝ) := by
    have hf' := hf.mono (fun ω h => congrArg (fun x => ‖x‖^2) h)
    have hc' := hc.mono (fun ω h => congrArg (fun x => ‖x‖^2) h)
    rw [lp_norm_sq_eq_integral,lp_norm_sq_eq_integral,
      integral_congr_ae hf',integral_congr_ae hc']
    exact hv
  have hs := congrArg Real.sqrt heq
  rw [Real.sqrt_sq (norm_nonneg _),Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hs
  exact hs

end Centering

section Copies
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
  {N dθ dx : ℕ}

/-- Actual expectation commutes with any bounded linear map. -/
theorem lpExpectationCLM_compLp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (C : E →L[ℝ] F) (X : Lp E 2 Q) :
    lpExpectationCLM Q (C.compLp X)=C (lpExpectationCLM Q X) := by
  rw [lpExpectationCLM_apply,integral_congr_ae (C.coeFn_compLp X),lpExpectationCLM_apply]
  exact C.integral_comp_comm ((Lp.memLp X).integrable (by norm_num))

theorem lpExpectationCLM_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (x : E) : lpExpectationCLM Q (Lp.const 2 Q x)=x := by
  rw [lpExpectationCLM_apply,integral_congr_ae (Lp.coeFn_const (μ := Q) (p := 2) (c := x))]
  simp only [Function.const_apply,integral_const,probReal_univ,one_smul]

/-- Mean-field parameter expectation and genuine iid latent copies. -/
def iidMeanFieldCopiesCLM : Lp (IPLA.Joint dθ dx) 2 Q →L[ℝ]
    MeanFieldParticleState (Measure.pi (fun _ : Fin N => Q)) N dθ dx :=
  ((Lp.constL 2 (Measure.pi (fun _ : Fin N => Q)) ℝ).comp
    (jointParameterCLM.comp (lpExpectationCLM Q))).prod
    (ContinuousLinearMap.pi (fun i : Fin N =>
      ((@jointLatentCLM dθ dx).compLpL 2 (Measure.pi (fun _ : Fin N => Q))).comp (iidCopyCLM Q i)))

@[simp] theorem iidMeanFieldCopiesCLM_parameter (X : Lp (IPLA.Joint dθ dx) 2 Q) :
    (iidMeanFieldCopiesCLM Q (N := N) X).1=
      Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) (jointParameterCLM (lpExpectationCLM Q X)) := rfl

@[simp] theorem iidMeanFieldCopiesCLM_latent (X : Lp (IPLA.Joint dθ dx) 2 Q) (i : Fin N) :
    (iidMeanFieldCopiesCLM Q (N := N) X).2 i=jointLatentCLM.compLp (iidCopyCLM Q i X) := rfl

theorem iidMeanFieldCopiesCLM_parameter_const (X : Lp (IPLA.Joint dθ dx) 2 Q)
    (θ : EuclideanSpace ℝ (Fin dθ)) (hθ : jointParameterCLM.compLp X=Lp.const 2 Q θ) :
    (iidMeanFieldCopiesCLM Q (N := N) X).1=Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) θ := by
  rw [iidMeanFieldCopiesCLM_parameter]
  have h := congrArg (lpExpectationCLM Q) hθ
  rw [lpExpectationCLM_compLp,lpExpectationCLM_const] at h
  rw [h]

/-- Reconstructing one pair from a joint random variable loses no coordinates. -/
theorem lpJointPair_projections {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (X : Lp (IPLA.Joint dθ dx) 2 P) :
    lpJointPair P (jointParameterCLM.compLp X) (jointLatentCLM.compLp X)=X := by
  apply Lp.ext
  filter_upwards [lpJointPair_coe P (jointParameterCLM.compLp X) (jointLatentCLM.compLp X),
    jointParameterCLM.coeFn_compLp X,jointLatentCLM.coeFn_compLp X] with ω hp hθ hx
  rw [hp,hθ,hx]
  ext j
  cases j <;> rfl

/-- Each reference pair is the selected genuine joint copy when its parameter
is deterministic. This is an equality of actual L² random variables. -/
theorem iidMeanFieldCopies_joint (X : Lp (IPLA.Joint dθ dx) 2 Q)
    (θ : EuclideanSpace ℝ (Fin dθ)) (hθ : jointParameterCLM.compLp X=Lp.const 2 Q θ)
    (i : Fin N) :
    lpJointPair (Measure.pi (fun _ : Fin N => Q))
      (iidMeanFieldCopiesCLM Q (N := N) X).1 ((iidMeanFieldCopiesCLM Q X).2 i)=iidCopyCLM Q i X := by
  rw [iidMeanFieldCopiesCLM_parameter_const Q X θ hθ,iidMeanFieldCopiesCLM_latent]
  have hp : jointParameterCLM.compLp (iidCopyCLM Q i X)=
      Lp.const 2 (Measure.pi (fun _ : Fin N => Q)) θ := by
    rw [← iidCopyCLM_compLp,hθ,iidCopyCLM_const]
  rw [← hp]
  exact lpJointPair_projections _ _

/-- Actual pointwise Lipschitz drift commutes with an iid pullback. -/
theorem iidCopyCLM_lpDrift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : E → E) {L : ℝ≥0}
    (hg : LipschitzWith L g) (X : Lp E 2 Q) (i : Fin N) :
    ULA.lpDrift (Measure.pi (fun _ : Fin N => Q)) g hg (iidCopyCLM Q i X)=
      iidCopyCLM Q i (ULA.lpDrift Q g hg X) := by
  apply Lp.ext
  have hsrc := (measurePreserving_eval (fun _ : Fin N => Q) i).quasiMeasurePreserving
    |>.ae (ULA.lpDrift_coe Q g hg X)
  filter_upwards [ULA.lpDrift_coe (Measure.pi (fun _ : Fin N => Q)) g hg (iidCopyCLM Q i X),
    iidCopyCLM_coe Q i X,iidCopyCLM_coe Q i (ULA.lpDrift Q g hg X),hsrc] with ω hd hx hc hs
  rw [hd,hx,hc,hs]

/-- The finite-particle drift defect at the constructed iid reference is exactly
its centered empirical parameter-gradient error. The latent defect is zero. -/
theorem iidMeanFieldCopies_drift_residual (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (X : Lp (IPLA.Joint dθ dx) 2 Q)
    (θ : EuclideanSpace ℝ (Fin dθ)) (hθ : jointParameterCLM.compLp X=Lp.const 2 Q θ) :
    lpParticleDrift (Measure.pi (fun _ : Fin N => Q)) V hLip (iidMeanFieldCopiesCLM Q (N := N) X)-
      iidMeanFieldCopiesCLM Q (lpMeanFieldDrift Q V hLip X)=
      (iidEmpiricalFluctuation Q (N := N)
        (jointParameterCLM.compLp (ULA.lpDrift Q (gradient V) hLip X)),fun _ => 0) := by
  let G := ULA.lpDrift Q (gradient V) hLip X
  have hg (i : Fin N) : lpParticleGradient (Measure.pi (fun _ : Fin N => Q)) V hLip i
      (iidMeanFieldCopiesCLM Q (N := N) X)=iidCopyCLM Q i G := by
    rw [lpParticleGradient,iidMeanFieldCopies_joint Q X θ hθ,iidCopyCLM_lpDrift]
  apply Prod.ext
  · change (N : ℝ)⁻¹ • ∑ i,jointParameterCLM.compLp
        (lpParticleGradient _ V hLip i (iidMeanFieldCopiesCLM Q X))-
      (iidMeanFieldCopiesCLM Q (N := N) (lpMeanFieldDrift Q V hLip X)).1=_
    simp_rw [hg,← iidCopyCLM_compLp]
    rw [iidMeanFieldCopiesCLM_parameter]
    rw [← lpExpectationCLM_compLp Q jointParameterCLM (lpMeanFieldDrift Q V hLip X)]
    rw [lpMeanFieldDrift_parameter,lpExpectationCLM_const]
    simp only [iidEmpiricalFluctuation,lpExpectationCLM_compLp,lpMeanFieldParameterForce]
    rfl
  · funext i
    change jointLatentCLM.compLp (lpParticleGradient _ V hLip i (iidMeanFieldCopiesCLM Q X))-
      (iidMeanFieldCopiesCLM Q (N := N) (lpMeanFieldDrift Q V hLip X)).2 i=0
    rw [hg,iidMeanFieldCopiesCLM_latent,← iidCopyCLM_compLp,← iidCopyCLM_compLp,
      lpMeanFieldDrift_latent]
    exact sub_self _

/-- The actual drift defect has its exact independent-sampling norm. -/
theorem iidMeanFieldCopies_drift_residual_norm (hN : 0<N)
    (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L (gradient V))
    (X : Lp (IPLA.Joint dθ dx) 2 Q) (θ : EuclideanSpace ℝ (Fin dθ))
    (hθ : jointParameterCLM.compLp X=Lp.const 2 Q θ) :
    ‖lpParticleDrift (Measure.pi (fun _ : Fin N => Q)) V hLip (iidMeanFieldCopiesCLM Q (N := N) X)-
      iidMeanFieldCopiesCLM Q (lpMeanFieldDrift Q V hLip X)‖=
      ‖lpCenterCLM Q (jointParameterCLM.compLp (ULA.lpDrift Q (gradient V) hLip X))‖/
        Real.sqrt (N : ℝ) := by
  rw [iidMeanFieldCopies_drift_residual Q V hLip X θ hθ,Prod.norm_mk]
  change max ‖iidEmpiricalFluctuation Q (N := N)
      (jointParameterCLM.compLp (ULA.lpDrift Q (gradient V) hLip X))‖
      ‖(0 : Fin N → Lp (EuclideanSpace ℝ (Fin dx)) 2 (Measure.pi (fun _ : Fin N => Q)))‖=_
  rw [norm_zero,max_eq_left (norm_nonneg _)]
  exact iidEmpiricalFluctuation_norm Q hN _

end Copies
end ProximalLangevin
