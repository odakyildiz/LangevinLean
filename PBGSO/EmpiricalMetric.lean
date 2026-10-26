import PBGSO.RawEmpiricalDynamics
import PBGSO.MetricFactor
import PBGSO.AdditiveJointBridge

/-! # Source A3 on the actual empirical Hilbert state
The physical finite-cloud metric, its positive linear factor, and drift
monotonicity are derived from the original source geometry and empirical
coupling. The result also integrates to the actual L² force lift.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Set
open scoped NNReal BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.EmpiricalMetric
open ConstructedItoParticle
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [Fintype I] [DecidableEq I]

def optimizerProjection (N : ℕ) : OneHilbert N S Z →L[ℝ] S :=
  (ContinuousLinearMap.fst ℝ S (Fin N → Z)).comp (oneEquiv N).toContinuousLinearMap

def samplerProjection (N : ℕ) (i : Fin N) : OneHilbert N S Z →L[ℝ] Z :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.snd ℝ S (Fin N → Z)).comp (oneEquiv N).toContinuousLinearMap)

/-- Literal empirical weighting: one optimiser and the arithmetic mean of
its sampler quadratic weights. -/
def weight (N : ℕ) (D : TwistedGeometry S Z) : OneHilbert N S Z →L[ℝ] OneHilbert N S Z :=
  (optimizerProjection (S := S) (Z := Z) N).adjoint.comp
    (D.optimizerWeight.comp (optimizerProjection (S := S) (Z := Z) N))+
  (N : ℝ)⁻¹ • ∑ i : Fin N,
    (samplerProjection (S := S) (Z := Z) N i).adjoint.comp
      (D.samplerWeight.comp (samplerProjection (S := S) (Z := Z) N i))

theorem weight_inner (N : ℕ) (D : TwistedGeometry S Z) (x y : OneHilbert N S Z) :
    ⟪x,weight N D y⟫_ℝ =
      ⟪(oneEquiv N x).1,D.optimizerWeight (oneEquiv N y).1⟫_ℝ+
      (N : ℝ)⁻¹*∑ i, ⟪(oneEquiv N x).2 i,D.samplerWeight ((oneEquiv N y).2 i)⟫_ℝ := by
  simp only [weight,add_apply,ContinuousLinearMap.comp_apply,smul_apply,sum_apply,
    inner_add_right,inner_smul_right,inner_sum]
  rw [(optimizerProjection (S := S) (Z := Z) N).adjoint_inner_right]
  simp_rw [(samplerProjection (S := S) (Z := Z) N _).adjoint_inner_right]
  rfl

theorem weight_symmetric (N : ℕ) (D : TwistedGeometry S Z) (x y : OneHilbert N S Z) :
    ⟪x,weight N D y⟫_ℝ = ⟪weight N D x,y⟫_ℝ := by
  rw [real_inner_comm y (weight N D x),weight_inner,weight_inner]
  congr 1
  · exact (D.optimizer_symmetric (oneEquiv N x).1 (oneEquiv N y).1).trans
      (real_inner_comm (oneEquiv N y).1 (D.optimizerWeight (oneEquiv N x).1))
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (D.sampler_symmetric ((oneEquiv N x).2 i) ((oneEquiv N y).2 i)).trans
      (real_inner_comm ((oneEquiv N y).2 i) (D.samplerWeight ((oneEquiv N x).2 i)))

theorem weight_nonneg (N : ℕ) (D : TwistedGeometry S Z) (x : OneHilbert N S Z) :
    0≤⟪x,weight N D x⟫_ℝ := by
  rw [weight_inner]
  exact add_nonneg (D.optimizerSq_nonneg _) (mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun i _ => D.samplerSq_nonneg _)))

theorem norm_sq_coordinates (N : ℕ) (x : OneHilbert N S Z) :
    ‖x‖^2=‖(oneEquiv N x).1‖^2+∑ i, ‖(oneEquiv N x).2 i‖^2 := by
  change ‖x‖^2=‖x.fst‖^2+∑ i, ‖x.snd i‖^2
  rw [WithLp.prod_norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]

def lower (N : ℕ) (D : TwistedGeometry S Z) : ℝ := D.lower*min 1 (N : ℝ)⁻¹
def upper (N : ℕ) (D : TwistedGeometry S Z) : ℝ := D.upper*max 1 (N : ℝ)⁻¹

theorem lower_pos (N : ℕ) (hN : 0<N) (D : TwistedGeometry S Z) : 0<lower N D := by
  dsimp [lower]
  exact mul_pos D.lower_pos (lt_min zero_lt_one (inv_pos.mpr (by exact_mod_cast hN)))

theorem upper_nonneg (N : ℕ) (D : TwistedGeometry S Z) : 0≤upper N D := by
  dsimp [upper]
  exact mul_nonneg (D.lower_pos.le.trans D.lower_le_upper) (le_max_of_le_left zero_le_one)

theorem weight_lower (N : ℕ) (D : TwistedGeometry S Z) (x : OneHilbert N S Z) :
    lower N D*‖x‖^2≤⟪x,weight N D x⟫_ℝ := by
  have ho := D.optimizer_lower (oneEquiv N x).1
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => D.sampler_lower ((oneEquiv N x).2 i))
  rw [← Finset.mul_sum] at hs
  have hs' := mul_le_mul_of_nonneg_left hs (show 0≤(N : ℝ)⁻¹ by positivity)
  have hc1 : lower N D≤D.lower := by
    dsimp [lower]
    exact mul_le_of_le_one_right D.lower_pos.le (min_le_left _ _)
  have hc2 : lower N D≤(N : ℝ)⁻¹*D.lower := by
    dsimp [lower]
    nlinarith [mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (N : ℝ)⁻¹) D.lower_pos.le]
  have h1 := mul_le_mul_of_nonneg_right hc1 (sq_nonneg ‖(oneEquiv N x).1‖)
  have h2 := mul_le_mul_of_nonneg_right hc2
    (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg ‖(oneEquiv N x).2 i‖))
  rw [weight_inner,norm_sq_coordinates]
  nlinarith

theorem weight_upper (N : ℕ) (D : TwistedGeometry S Z) (x : OneHilbert N S Z) :
    ⟪x,weight N D x⟫_ℝ≤upper N D*‖x‖^2 := by
  have hD : 0≤D.upper := D.lower_pos.le.trans D.lower_le_upper
  have ho := D.optimizer_upper (oneEquiv N x).1
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => D.sampler_upper ((oneEquiv N x).2 i))
  rw [← Finset.mul_sum] at hs
  have hs' := mul_le_mul_of_nonneg_left hs (show 0≤(N : ℝ)⁻¹ by positivity)
  have hc1 : D.upper≤upper N D := by
    dsimp [upper]
    exact le_mul_of_one_le_right hD (le_max_left _ _)
  have hc2 : (N : ℝ)⁻¹*D.upper≤upper N D := by
    dsimp [upper]
    nlinarith [mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) (N : ℝ)⁻¹) hD]
  have h1 := mul_le_mul_of_nonneg_right hc1 (sq_nonneg ‖(oneEquiv N x).1‖)
  have h2 := mul_le_mul_of_nonneg_right hc2
    (Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg ‖(oneEquiv N x).2 i‖))
  rw [weight_inner,norm_sq_coordinates]
  nlinarith

/-- The metric factor and all norm comparisons are constructed from the
source SPD geometry; no factorization or comparison conclusion is assumed. -/
theorem exists_factor [FiniteDimensional ℝ S] [FiniteDimensional ℝ Z]
    (N : ℕ) (hN : 0<N) (D : TwistedGeometry S Z) :
    ∃ n : ℕ, ∃ C : OneHilbert N S Z →L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ x, ‖C x‖^2=⟪x,weight N D x⟫_ℝ) ∧
      (∀ x, Real.sqrt (lower N D)*‖x‖≤‖C x‖) ∧
      (∀ x, ‖C x‖≤Real.sqrt (upper N D)*‖x‖) :=
  MetricFactor.exists_coercive_factor (weight N D) (weight_symmetric N D)
    (lower N D) (upper N D) (lower_pos N hN D) (upper_nonneg N D)
    (weight_lower N D) (weight_upper N D)

/-- Source A3 gives drift dissipation on the actual original empirical
state. Nonnegative diffusion correction may be discarded; no new drift
monotonicity premise replaces the source assumption. -/
theorem drift_dissipation (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ) (N : ℕ) (hN : 0<N)
    (t : ℝ) (ht : 0≤t) (x y : OneHilbert N S Z) :
    ⟪x-y,weight N D (RawEmpiricalDynamics.drift M N t x-RawEmpiricalDynamics.drift M N t y)⟫_ℝ ≤
      -ρ*⟪x-y,weight N D (x-y)⟫_ℝ := by
  have hd := particleCouplingWork_le M D ρ hmono N hN t ht
    (oneEquiv N x).1 (oneEquiv N y).1 (oneEquiv N x).2 (oneEquiv N y).2
  have hnoise :
      (N : ℝ)⁻¹*∑ i : Fin N, (1/2 : ℝ)*∑ j : I,
        D.samplerSq (M.diffusion (M.parameter (oneEquiv N x).1) ((oneEquiv N x).2 i) j-
          M.diffusion (M.parameter (oneEquiv N y).1) ((oneEquiv N y).2 i) j) ≥ 0 := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
      mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => D.samplerSq_nonneg _))
  simp only [particleCouplingWork,samplerCouplingWork,Finset.sum_add_distrib] at hd
  rw [weight_inner,weight_inner]
  simp only [map_sub,Prod.fst_sub,Prod.snd_sub,Pi.sub_apply,
    RawEmpiricalDynamics.drift_coordinates]
  dsimp [particleCouplingEnergy,TwistedGeometry.optimizerSq,TwistedGeometry.samplerSq] at hd
  dsimp [TwistedGeometry.samplerSq] at hnoise
  simp only [map_sub] at hd hnoise
  nlinarith
end PBGSO.EmpiricalMetric

namespace PBGSO.EmpiricalMetric
open ConstructedItoParticle
section Lift
variable {Ω S Θ Z X I K : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Pointwise factorization gives the actual L² weighted pairing identity. -/
theorem factor_lp_pairing (N : ℕ) (D : TwistedGeometry S Z)
    (C : OneHilbert N S Z →L[ℝ] K)
    (hC : ∀ x, ‖C x‖^2=⟪x,weight N D x⟫_ℝ)
    (U V : Lp (OneHilbert N S Z) 2 Q) :
    ⟪C.compLpL 2 Q U,C.compLpL 2 Q V⟫_ℝ =
      ⟪U,(weight N D).compLpL 2 Q V⟫_ℝ := by
  rw [L2.inner_def,lp_weighted_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [C.coeFn_compLpL U,C.coeFn_compLpL V] with ω hu hv
  rw [hu,hv]
  exact MetricFactor.pairing (weight N D) C (weight_symmetric N D) hC (U ω) (V ω)

/-- The constructed metric's exact L² energy identity. -/
theorem factor_lp_norm_sq (N : ℕ) (D : TwistedGeometry S Z)
    (C : OneHilbert N S Z →L[ℝ] K)
    (hC : ∀ x, ‖C x‖^2=⟪x,weight N D x⟫_ℝ)
    (U : Lp (OneHilbert N S Z) 2 Q) :
    ‖C.compLpL 2 Q U‖^2=⟪U,(weight N D).compLpL 2 Q U⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq]
  exact factor_lp_pairing Q N D C hC U U

/-- The actual finite-particle L² force inherits source A3 in the genuine
constructed metric. Neither L² drift monotonicity nor contraction is assumed. -/
theorem lift_dissipation (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ) (N : ℕ) (hN : 0<N)
    (C : OneHilbert N S Z →L[ℝ] K)
    (hC : ∀ x, ‖C x‖^2=⟪x,weight N D x⟫_ℝ)
    (t : ℝ) (ht : 0≤t) (L : ℝ≥0)
    (hLip : LipschitzWith L (RawEmpiricalDynamics.drift M N t))
    (U V : Lp (OneHilbert N S Z) 2 Q) :
    ⟪C.compLpL 2 Q (U-V),C.compLpL 2 Q
      (liftMap Q (RawEmpiricalDynamics.drift M N t) hLip U-
        liftMap Q (RawEmpiricalDynamics.drift M N t) hLip V)⟫_ℝ ≤
      -ρ*‖C.compLpL 2 Q (U-V)‖^2 := by
  let f := RawEmpiricalDynamics.drift M N t
  let FU := liftMap Q f hLip U
  let FV := liftMap Q f hLip V
  rw [factor_lp_pairing Q N D C hC,factor_lp_norm_sq Q N D C hC]
  rw [lp_weighted_pairing_eq_integral,lp_weighted_pairing_eq_integral,← integral_const_mul]
  apply integral_mono_ae (lp_weighted_pairing_integrable Q (weight N D) (U-V) (FU-FV))
    ((lp_weighted_pairing_integrable Q (weight N D) (U-V) (U-V)).const_mul (-ρ))
  filter_upwards [liftMap_coe Q f hLip U,liftMap_coe Q f hLip V,
    Lp.coeFn_sub U V,Lp.coeFn_sub FU FV] with ω hu hv hsub hFsub
  change ⟪(U-V) ω,weight N D ((FU-FV) ω)⟫_ℝ ≤ -ρ*⟪(U-V) ω,weight N D ((U-V) ω)⟫_ℝ
  change FU ω=f (U ω) at hu
  change FV ω=f (V ω) at hv
  simp only [Pi.sub_apply] at hsub hFsub
  rw [hsub,hFsub,hu,hv]
  exact drift_dissipation M D ρ hmono N hN t ht (U ω) (V ω)

/-- Exact packing/intertwining transports source-derived empirical
monotonicity to the original numerical coordinate space. The premise is a
literal drift identity, discharged by implementation-coordinate proofs. -/
theorem transported_lift_dissipation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : E →L[ℝ] Lp (OneHilbert N S Z) 2 Q)
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ) (hN : 0<N)
    (C : OneHilbert N S Z →L[ℝ] K)
    (hC : ∀ x, ‖C x‖^2=⟪x,weight N D x⟫_ℝ)
    (t : ℝ) (ht : 0≤t) (L : ℝ≥0)
    (hLip : LipschitzWith L (RawEmpiricalDynamics.drift M N t))
    (f : E → E) (hfield : ∀ x, P (f x)=liftMap Q (RawEmpiricalDynamics.drift M N t) hLip (P x))
    (x y : E) :
    let T := (C.compLpL 2 Q).comp P
    ⟪T (x-y),T (f x-f y)⟫_ℝ ≤ -ρ*‖T (x-y)‖^2 := by
  have h := lift_dissipation Q M D ρ hmono N hN C hC t ht L hLip (P x) (P y)
  simpa only [ContinuousLinearMap.comp_apply,map_sub,hfield] using h

/-- The source metric's coercivity survives the genuine L² lift. -/
theorem factor_lp_coercivity (N : ℕ) (hN : 0<N) (D : TwistedGeometry S Z)
    (C : OneHilbert N S Z →L[ℝ] K)
    (hC : ∀ x, ‖C x‖^2=⟪x,weight N D x⟫_ℝ)
    (U : Lp (OneHilbert N S Z) 2 Q) :
    Real.sqrt (lower N D)*‖U‖≤‖C.compLpL 2 Q U‖ := by
  apply (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp
  rw [mul_pow,Real.sq_sqrt (lower_pos N hN D).le,factor_lp_norm_sq Q N D C hC,
    lp_weighted_pairing_eq_integral,ProximalLangevin.lp_norm_sq_eq_integral Q U,
    ← integral_const_mul]
  exact integral_mono
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U)).mp (Lp.memLp U)).const_mul _)
    (lp_weighted_pairing_integrable Q (weight N D) U U) (fun ω => weight_lower N D (U ω))

/-- The source metric's upper comparison also survives L² lifting. -/
theorem factor_lp_upper (N : ℕ) (D : TwistedGeometry S Z)
    (C : OneHilbert N S Z →L[ℝ] K)
    (hC : ∀ x, ‖C x‖^2=⟪x,weight N D x⟫_ℝ)
    (U : Lp (OneHilbert N S Z) 2 Q) :
    ‖C.compLpL 2 Q U‖≤Real.sqrt (upper N D)*‖U‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (upper_nonneg N D),factor_lp_norm_sq Q N D C hC,
    lp_weighted_pairing_eq_integral,ProximalLangevin.lp_norm_sq_eq_integral Q U,
    ← integral_const_mul]
  exact integral_mono
    (lp_weighted_pairing_integrable Q (weight N D) U U)
    (((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable U)).mp (Lp.memLp U)).const_mul _)
    (fun ω => weight_upper N D (U ω))

/-- Samplewise original empirical drift identities suffice for lifted A3;
no independent global-Lipschitz assumption on repacked physical coordinates
is needed in this version. -/
theorem lift_dissipation_of_coe (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ) (N : ℕ) (hN : 0<N)
    (C : OneHilbert N S Z →L[ℝ] K)
    (hC : ∀ x, ‖C x‖^2=⟪x,weight N D x⟫_ℝ)
    (t : ℝ) (ht : 0≤t) (U V FU FV : Lp (OneHilbert N S Z) 2 Q)
    (hFU : FU =ᵐ[Q] fun ω => RawEmpiricalDynamics.drift M N t (U ω))
    (hFV : FV =ᵐ[Q] fun ω => RawEmpiricalDynamics.drift M N t (V ω)) :
    ⟪C.compLpL 2 Q (U-V),C.compLpL 2 Q (FU-FV)⟫_ℝ ≤
      -ρ*‖C.compLpL 2 Q (U-V)‖^2 := by
  rw [factor_lp_pairing Q N D C hC,factor_lp_norm_sq Q N D C hC]
  rw [lp_weighted_pairing_eq_integral,lp_weighted_pairing_eq_integral,← integral_const_mul]
  apply integral_mono_ae (lp_weighted_pairing_integrable Q (weight N D) (U-V) (FU-FV))
    ((lp_weighted_pairing_integrable Q (weight N D) (U-V) (U-V)).const_mul (-ρ))
  filter_upwards [hFU,hFV,Lp.coeFn_sub U V,Lp.coeFn_sub FU FV] with ω hu hv hsub hFsub
  simp only [Pi.sub_apply] at hsub hFsub
  rw [hsub,hFsub,hu,hv]
  exact drift_dissipation M D ρ hmono N hN t ht (U ω) (V ω)

/-- Transport by an actual packing map and proved samplewise drift identity.
This is the interface used by the original raw method coordinates. -/
theorem transported_lift_dissipation_of_coe {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (P : E →L[ℝ] Lp (OneHilbert N S Z) 2 Q)
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ) (hN : 0<N)
    (C : OneHilbert N S Z →L[ℝ] K)
    (hC : ∀ x, ‖C x‖^2=⟪x,weight N D x⟫_ℝ)
    (t : ℝ) (ht : 0≤t) (f : E → E)
    (hfield : ∀ x, P (f x) =ᵐ[Q] fun ω => RawEmpiricalDynamics.drift M N t (P x ω))
    (x y : E) :
    let T := (C.compLpL 2 Q).comp P
    ⟪T (x-y),T (f x-f y)⟫_ℝ ≤ -ρ*‖T (x-y)‖^2 := by
  have h := lift_dissipation_of_coe Q M D ρ hmono N hN C hC t ht
    (P x) (P y) (P (f x)) (P (f y)) (hfield x) (hfield y)
  simpa only [ContinuousLinearMap.comp_apply,map_sub] using h

/-- The metric on the original raw L² method coordinates is constructed
from an actual coordinate equivalence. A3 supplies its drift dissipation;
coercivity and the upper norm bound are proved, not new assumptions. -/
theorem exists_transported_metric {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ S] [FiniteDimensional ℝ Z]
    (P : E ≃L[ℝ] Lp (OneHilbert N S Z) 2 Q)
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ) (hN : 0<N)
    (t : ℝ) (ht : 0≤t) (f : E → E)
    (hfield : ∀ x, P (f x) =ᵐ[Q] fun ω => RawEmpiricalDynamics.drift M N t (P x ω)) :
    ∃ n : ℕ, ∃ T : E →L[ℝ] Lp (EuclideanSpace ℝ (Fin n)) 2 Q,
      (∀ x, (Real.sqrt (lower N D)/(‖P.symm.toContinuousLinearMap‖+1))*‖x‖≤‖T x‖) ∧
      (∀ x, ‖T x‖≤(Real.sqrt (upper N D)*‖P.toContinuousLinearMap‖)*‖x‖) ∧
      (∀ x y, ⟪T (x-y),T (f x-f y)⟫_ℝ ≤ -ρ*‖T (x-y)‖^2) := by
  obtain ⟨n,C,hC,_,_⟩ := exists_factor N hN D
  let T := (C.compLpL 2 Q).comp P.toContinuousLinearMap
  refine ⟨n,T,?_,?_,?_⟩
  · intro x
    have hl := factor_lp_coercivity Q N hN D C hC (P x)
    have hP : ‖x‖≤(‖P.symm.toContinuousLinearMap‖+1)*‖P x‖ := by
      have hp := P.symm.toContinuousLinearMap.le_opNorm (P x)
      simp only [ContinuousLinearEquiv.coe_coe,P.symm_apply_apply] at hp
      nlinarith [norm_nonneg (P x)]
    have hm := mul_le_mul_of_nonneg_left hP
      (show 0≤Real.sqrt (lower N D)/(‖P.symm.toContinuousLinearMap‖+1) by positivity)
    have hden : 0<‖P.symm.toContinuousLinearMap‖+1 := by positivity
    have he : (Real.sqrt (lower N D)/(‖P.symm.toContinuousLinearMap‖+1))*
        ((‖P.symm.toContinuousLinearMap‖+1)*‖P x‖)=Real.sqrt (lower N D)*‖P x‖ := by
      field_simp
    rw [he] at hm
    exact hm.trans hl
  · intro x
    have hu := factor_lp_upper Q N D C hC (P x)
    have hp := mul_le_mul_of_nonneg_left (P.toContinuousLinearMap.le_opNorm x)
      (Real.sqrt_nonneg (upper N D))
    simp only [ContinuousLinearEquiv.coe_coe] at hp
    exact hu.trans (by nlinarith [hp])
  · exact transported_lift_dissipation_of_coe Q P.toContinuousLinearMap M D ρ hmono hN C hC
      t ht f hfield
end Lift
end PBGSO.EmpiricalMetric
