import ProximalLangevin.MeanFieldProcess
import ProximalLangevin.MeanFieldVariance

set_option linter.style.header false

/-! # The actual finite-particle drift in a coordinate L² Banach space

The parameter force is the empirical average. Each latent force is its own
joint gradient. The norm takes the maximum of the coordinate L² norms, so
bounds in this space control every tagged particle without exchangeability.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace ProximalLangevin

/-- Coordinate L² space, with the usual product/finite-function maximum norm. -/
abbrev MeanFieldParticleState {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N dθ dx : ℕ) := Lp (EuclideanSpace ℝ (Fin dθ)) 2 P ×
      (Fin N → Lp (EuclideanSpace ℝ (Fin dx)) 2 P)

/-- Embed a latent vector into the joint space. -/
def jointLatentInclusionCLM {dθ dx : ℕ} :
    EuclideanSpace ℝ (Fin dx) →L[ℝ] IPLA.Joint dθ dx :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => IPLA.pair 0 x
      map_add' := by intro x y; ext j; cases j <;> simp [IPLA.pair]
      map_smul' := by intro a x; ext j; cases j <;> simp [IPLA.pair] }

theorem jointLatentInclusionCLM_norm {dθ dx : ℕ} (x : EuclideanSpace ℝ (Fin dx)) :
    ‖(jointLatentInclusionCLM x : IPLA.Joint dθ dx)‖=‖x‖ := by
  have h := IPLA.norm_pair_sq (0 : EuclideanSpace ℝ (Fin dθ)) x
  change ‖IPLA.pair 0 x‖=‖x‖
  simp only [norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_add] at h
  nlinarith [norm_nonneg (IPLA.pair (0 : EuclideanSpace ℝ (Fin dθ)) x),norm_nonneg x]

theorem norm_jointLatentCLM_apply_le {dθ dx : ℕ} (z : IPLA.Joint dθ dx) :
    ‖jointLatentCLM z‖ ≤ ‖z‖ := by
  have hs : ‖jointLatentCLM z‖^2 ≤ ‖z‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,jointLatentCLM_apply,Fintype.sum_sum_type]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (jointLatentCLM z),norm_nonneg z]

section Particle
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {N dθ dx : ℕ}

omit [IsProbabilityMeasure P] in
/-- A pointwise nonexpansive linear map remains nonexpansive on L². -/
theorem lp_linear_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (C : E →L[ℝ] F)
    (hC : ∀ x,‖C x‖≤‖x‖) (X : Lp E 2 P) : ‖C.compLp X‖≤‖X‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [C.coeFn_compLp X] with ω hx
  rw [hx]
  exact hC _

/-- Pair the common parameter random variable with one latent variable. -/
def lpJointPair (θ : Lp (EuclideanSpace ℝ (Fin dθ)) 2 P)
    (x : Lp (EuclideanSpace ℝ (Fin dx)) 2 P) : Lp (IPLA.Joint dθ dx) 2 P :=
  jointParameterInclusionCLM.compLp θ+jointLatentInclusionCLM.compLp x

omit [IsProbabilityMeasure P] in
theorem lpJointPair_coe (θ : Lp (EuclideanSpace ℝ (Fin dθ)) 2 P)
    (x : Lp (EuclideanSpace ℝ (Fin dx)) 2 P) :
    lpJointPair P θ x =ᵐ[P] fun ω => IPLA.pair (θ ω) (x ω) := by
  filter_upwards [Lp.coeFn_add (jointParameterInclusionCLM.compLp θ)
      (jointLatentInclusionCLM.compLp x),jointParameterInclusionCLM.coeFn_compLp θ,
      jointLatentInclusionCLM.coeFn_compLp x] with ω ha hθ hx
  rw [lpJointPair,ha,Pi.add_apply,hθ,hx]
  ext j
  cases j <;> simp [jointLatentInclusionCLM,IPLA.pair]

omit [IsProbabilityMeasure P] in
theorem lpJointPair_difference_le
    (θ θ' : Lp (EuclideanSpace ℝ (Fin dθ)) 2 P)
    (x x' : Lp (EuclideanSpace ℝ (Fin dx)) 2 P) :
    ‖lpJointPair P θ x-lpJointPair P θ' x'‖≤‖θ-θ'‖+‖x-x'‖ := by
  let A := (@jointParameterInclusionCLM dθ dx).compLpL 2 P
  let B := (@jointLatentInclusionCLM dθ dx).compLpL 2 P
  have hid : lpJointPair P θ x-lpJointPair P θ' x'=A (θ-θ')+B (x-x') := by
    change A θ+B x-(A θ'+B x')=A (θ-θ')+B (x-x')
    rw [map_sub,map_sub]
    abel
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add
    (lp_linear_norm_le P _ (fun x => (jointParameterInclusionCLM_norm x).le) _)
    (lp_linear_norm_le P _ (fun x => (jointLatentInclusionCLM_norm x).le) _))

/-- The actual joint gradient at the common parameter and the selected particle. -/
def lpParticleGradient (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (i : Fin N)
    (z : MeanFieldParticleState P N dθ dx) : Lp (IPLA.Joint dθ dx) 2 P :=
  ULA.lpDrift P (gradient V) hLip (lpJointPair P z.1 (z.2 i))

/-- The actual particle drift: averaged parameter force and individual latent forces. -/
def lpParticleDrift (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V))
    (z : MeanFieldParticleState P N dθ dx) : MeanFieldParticleState P N dθ dx :=
  ((N : ℝ)⁻¹ • ∑ i, jointParameterCLM.compLp (lpParticleGradient P V hLip i z),
    fun i => jointLatentCLM.compLp (lpParticleGradient P V hLip i z))

/-- The gradient random variable has the actual parameter/particle coordinates. -/
theorem lpParticleGradient_coe (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (i : Fin N)
    (z : MeanFieldParticleState P N dθ dx) :
    lpParticleGradient P V hLip i z =ᵐ[P]
      fun ω => gradient V (IPLA.pair (z.1 ω) (z.2 i ω)) := by
  filter_upwards [ULA.lpDrift_coe P (gradient V) hLip (lpJointPair P z.1 (z.2 i)),
    lpJointPair_coe P z.1 (z.2 i)] with ω hg hp
  rw [lpParticleGradient,hg,hp]

/-- The displayed common-parameter force is precisely the empirical mean. -/
theorem lpParticleDrift_parameter_coe (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (z : MeanFieldParticleState P N dθ dx) :
    (lpParticleDrift P V hLip z).1 =ᵐ[P]
      fun ω => (N : ℝ)⁻¹ • ∑ i,parameterGradient V (z.1 ω) (z.2 i ω) := by
  have hi : ∀ᵐ ω ∂P,∀ i : Fin N,
      jointParameterCLM.compLp (lpParticleGradient P V hLip i z) ω=
        parameterGradient V (z.1 ω) (z.2 i ω) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [jointParameterCLM.coeFn_compLp (lpParticleGradient P V hLip i z),
      lpParticleGradient_coe P V hLip i z] with ω hc hg
    rw [hc,hg]
    rfl
  filter_upwards [hi,Lp.coeFn_smul (N : ℝ)⁻¹
    (∑ i,jointParameterCLM.compLp (lpParticleGradient P V hLip i z)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin N =>
      jointParameterCLM.compLp (lpParticleGradient P V hLip i z))] with ω hi hs hsum
  rw [lpParticleDrift,hs,Pi.smul_apply,hsum]
  simp only [hi]

/-- Each latent force is the latent block of its own actual joint gradient. -/
theorem lpParticleDrift_latent_coe (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (z : MeanFieldParticleState P N dθ dx) (i : Fin N) :
    (lpParticleDrift P V hLip z).2 i =ᵐ[P]
      fun ω => jointLatentCLM (gradient V (IPLA.pair (z.1 ω) (z.2 i ω))) := by
  filter_upwards [jointLatentCLM.coeFn_compLp (lpParticleGradient P V hLip i z),
    lpParticleGradient_coe P V hLip i z] with ω hc hg
  rw [lpParticleDrift,hc,hg]

theorem lpParticleGradient_difference_le (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (i : Fin N)
    (z w : MeanFieldParticleState P N dθ dx) :
    ‖lpParticleGradient P V hLip i z-lpParticleGradient P V hLip i w‖≤
      2*(L : ℝ)*‖z-w‖ := by
  have hθ : ‖z.1-w.1‖≤‖z-w‖ := norm_fst_le (z-w)
  have hx : ‖z.2 i-w.2 i‖≤‖z-w‖ :=
    (norm_le_pi_norm (z.2-w.2) i).trans (norm_snd_le (z-w))
  have h := (ULA.lpDrift_lipschitz P (gradient V) hLip).norm_sub_le
    (lpJointPair P z.1 (z.2 i)) (lpJointPair P w.1 (w.2 i))
  exact h.trans (by
    have hh := mul_le_mul_of_nonneg_left
      (lpJointPair_difference_le P z.1 w.1 (z.2 i) (w.2 i)) L.coe_nonneg
    nlinarith)

/-- A global dimension-free Lipschitz bound in the coordinate-maximum L² norm. -/
theorem lpParticleDrift_lipschitz (hN : 0<N) (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) :
    LipschitzWith (2*L) (lpParticleDrift P (N := N) V hLip) := by
  have hn : (0 : ℝ)<N := by exact_mod_cast hN
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  have hg (i : Fin N) := lpParticleGradient_difference_le P V hLip i z w
  have hθ (i : Fin N) :
      ‖jointParameterCLM.compLp (lpParticleGradient P V hLip i z)-
        jointParameterCLM.compLp (lpParticleGradient P V hLip i w)‖≤2*(L : ℝ)*‖z-w‖ := by
    change ‖(@jointParameterCLM dθ dx).compLpL 2 P (lpParticleGradient P V hLip i z)-
      (@jointParameterCLM dθ dx).compLpL 2 P (lpParticleGradient P V hLip i w)‖≤_
    rw [← map_sub]
    exact (lp_linear_norm_le P _ norm_jointParameterCLM_apply_le _).trans (hg i)
  have hx (i : Fin N) :
      ‖jointLatentCLM.compLp (lpParticleGradient P V hLip i z)-
        jointLatentCLM.compLp (lpParticleGradient P V hLip i w)‖≤2*(L : ℝ)*‖z-w‖ := by
    change ‖(@jointLatentCLM dθ dx).compLpL 2 P (lpParticleGradient P V hLip i z)-
      (@jointLatentCLM dθ dx).compLpL 2 P (lpParticleGradient P V hLip i w)‖≤_
    rw [← map_sub]
    exact (lp_linear_norm_le P _ norm_jointLatentCLM_apply_le _).trans (hg i)
  change max ‖_‖ ‖_‖≤((2*L : ℝ≥0) : ℝ)*‖z-w‖
  apply max_le
  · change ‖(N : ℝ)⁻¹ • ∑ i,jointParameterCLM.compLp (lpParticleGradient P V hLip i z)-
      (N : ℝ)⁻¹ • ∑ i,jointParameterCLM.compLp (lpParticleGradient P V hLip i w)‖≤_
    rw [← smul_sub,← Finset.sum_sub_distrib,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hn.le)]
    have hs := (norm_sum_le Finset.univ (fun i : Fin N =>
      jointParameterCLM.compLp (lpParticleGradient P V hLip i z)-
      jointParameterCLM.compLp (lpParticleGradient P V hLip i w))).trans
      (Finset.sum_le_sum (fun i _ => hθ i))
    have hm := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul,NNReal.coe_mul,NNReal.coe_ofNat] using hm
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    change ‖jointLatentCLM.compLp (lpParticleGradient P V hLip i z)-
      jointLatentCLM.compLp (lpParticleGradient P V hLip i w)‖≤2*(L : ℝ)*‖z-w‖
    exact hx i

/-- Picard constructs the actual finite-particle coordinate integral equations
from continuous additive inputs, without a stochastic convergence premise. -/
theorem exists_lp_particle_integral (hN : 0<N) (V : IPLA.Joint dθ dx → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L (gradient V)) (initial : MeanFieldParticleState P N dθ dx)
    (B : ℝ → MeanFieldParticleState P N dθ dx) (hB : Continuous B) (hB0 : B 0=0)
    (T : ℝ) (hT : 0≤T) :
    ∃ Z : ℝ → MeanFieldParticleState P N dθ dx,Continuous Z ∧ Z 0=initial ∧
      ∀ t∈Icc 0 T,Z t-initial=-(∫ s in 0..t,lpParticleDrift P V hLip (Z s))+B t :=
  ULA.exists_langevin_integral (lpParticleDrift P V hLip) (2*L)
    (lpParticleDrift_lipschitz P hN V hLip) initial B hB hB0 T hT

end Particle
end ProximalLangevin
