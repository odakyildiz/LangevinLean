import LatentDiffusion.MainResults
import PBGSO.GeneralProcess
import PBGSO.MethodIntegralSegments
import ProximalLangevin.MeanFieldVariance
import UnadjustedLangevin.GibbsStationarity

/-!
# A closed full-batch theorem from an actual frozen posterior equation

The added analytic input is an actual continuous stationary frozen posterior
solution driven by Brownian noise. Its integral equation, initial optimality and
independent posterior scores are explicit. Numerical defects, empirical-force
residual estimates and reference moment bounds are conclusions, not inputs.
The drift constant below is its exact initial second moment, which is finite
because both the initial cloud and the Lipschitz force belong to L².
-/
noncomputable section
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
namespace LatentDiffusion.RegularStochastic

abbrev Parameter (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Latent (K dz : ℕ) := EuclideanSpace ℝ (Fin K × Fin dz)

/-- Insert a parameter vector into the parameter block. -/
def headInsert {d : ℕ} {J : Type*} [Fintype J] :
    Parameter d →L[ℝ] EuclideanSpace ℝ (Fin d ⊕ J) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => WithLp.toLp 2 (Sum.elim a (fun _ => 0))
      map_add' := by intro a b; ext j; cases j <;> simp
      map_smul' := by intro c a; ext j; cases j <;> simp }

/-- Extract a parameter block from any finite sum of coordinates. -/
def headExtract {d : ℕ} {J : Type*} [Fintype J] :
    EuclideanSpace ℝ (Fin d ⊕ J) →L[ℝ] Parameter d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun j => x (Sum.inl j))
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }

@[simp] theorem headInsert_apply {d : ℕ} {J : Type*} [Fintype J]
    (a : Parameter d) (j : Fin d ⊕ J) :
    headInsert a j = Sum.elim a (fun _ => 0) j := rfl

@[simp] theorem headExtract_apply {d : ℕ} {J : Type*} [Fintype J]
    (x : EuclideanSpace ℝ (Fin d ⊕ J)) (j : Fin d) :
    headExtract x j = x (Sum.inl j) := rfl

@[simp] theorem headInsert_norm {d : ℕ} {J : Type*} [Fintype J] (a : Parameter d) :
    ‖headInsert (J := J) a‖ = ‖a‖ := by
  have h : ‖headInsert (J := J) a‖ ^ 2 = ‖a‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
  nlinarith [norm_nonneg (headInsert (J := J) a), norm_nonneg a]

theorem headExtract_norm_le {d : ℕ} {J : Type*} [Fintype J]
    (x : EuclideanSpace ℝ (Fin d ⊕ J)) : ‖headExtract x‖ ≤ ‖x‖ := by
  have h : ‖headExtract x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, headExtract_apply, Fintype.sum_sum_type]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (headExtract x), norm_nonneg x]

/-- Orthogonal projection onto the latent block. -/
def tailMask {d : ℕ} {J : Type*} [Fintype J] :
    EuclideanSpace ℝ (Fin d ⊕ J) →L[ℝ] EuclideanSpace ℝ (Fin d ⊕ J) :=
  ContinuousLinearMap.id ℝ _ - headInsert.comp headExtract

@[simp] theorem tailMask_head {d : ℕ} {J : Type*} [Fintype J]
    (x : EuclideanSpace ℝ (Fin d ⊕ J)) (j : Fin d) : tailMask x (Sum.inl j) = 0 := by
  simp [tailMask]

@[simp] theorem tailMask_tail {d : ℕ} {J : Type*} [Fintype J]
    (x : EuclideanSpace ℝ (Fin d ⊕ J)) (j : J) : tailMask x (Sum.inr j) = x (Sum.inr j) := by
  simp [tailMask]

theorem tailMask_norm_le {d : ℕ} {J : Type*} [Fintype J]
    (x : EuclideanSpace ℝ (Fin d ⊕ J)) : ‖tailMask x‖ ≤ ‖x‖ := by
  have h : ‖tailMask x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
      tailMask_head, tailMask_tail, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, zero_add]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (tailMask x), norm_nonneg x]

theorem tailMask_opNorm_le {d : ℕ} {J : Type*} [Fintype J] :
    ‖(tailMask : EuclideanSpace ℝ (Fin d ⊕ J) →L[ℝ] _)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => by
    simpa using tailMask_norm_le x)

variable {K dθ dz : ℕ}

/-- One actual per-datum parameter score, inserted into the joint cloud. -/
def parameterScore (U : Fin K → Cloud.Joint dθ dz → ℝ) (i : Fin K)
    (x : Cloud.State K dθ dz) : Cloud.State K dθ dz :=
  headInsert (headExtract (gradient (U i) (Cloud.joint i x)))

theorem parameterScore_lipschitz (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (L : ℝ≥0) (hLip : ∀ i, LipschitzWith L (gradient (U i))) (i : Fin K) :
    LipschitzWith (L * ‖Cloud.jointCLM (dθ := dθ) (dx := dz) i‖₊)
      (parameterScore U i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  rw [parameterScore, parameterScore, ← map_sub, headInsert_norm, ← map_sub]
  apply (headExtract_norm_le _).trans
  apply ((hLip i).norm_sub_le _ _).trans
  have hj := (Cloud.jointCLM (dθ := dθ) (dx := dz) i).le_opNorm (x-y)
  simpa only [NNReal.coe_mul, coe_nnnorm, ContinuousLinearMap.map_sub,
    Cloud.jointCLM_apply, mul_assoc] using mul_le_mul_of_nonneg_left hj L.coe_nonneg

/-- Removing the latent force leaves precisely the empirical parameter score. -/
theorem meanForce_residual (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (hdiff : ∀ i, Differentiable ℝ (U i)) (x : Cloud.State K dθ dz) :
    Cloud.meanForce U x - tailMask (Cloud.meanForce U x) =
      MiniBatchVariance.average (fun i => parameterScore U i x) := by
  ext j
  cases j with
  | inl j =>
    simp [MiniBatchVariance.average, parameterScore, Cloud.meanForce,
      Cloud.gradient_potential_parameter hdiff]
  | inr j => simp [MiniBatchVariance.average, parameterScore]

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The frozen reference force is obtained by zeroing only the optimizer drift. -/
def frozenForce {F : Cloud.State K dθ dz → Cloud.State K dθ dz} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L) (X : Lp (Cloud.State K dθ dz) 2 P) :
    Lp (Cloud.State K dθ dz) 2 P :=
  tailMask.compLpL 2 P (liftedForce P hF X)

theorem frozenForce_lipschitz {F : Cloud.State K dθ dz → Cloud.State K dθ dz}
    {m : ℝ} {L : ℝ≥0} (hF : ForceRegularity F m L) :
    LipschitzWith L (frozenForce P hF) := by
  let C : Lp (Cloud.State K dθ dz) 2 P →L[ℝ] Lp (Cloud.State K dθ dz) 2 P :=
    (tailMask (d := dθ) (J := Fin K × Fin dz)).compLpL 2 P
  have hc : ‖C‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans tailMask_opNorm_le
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  simp only [dist_eq_norm]
  change ‖C (liftedForce P hF X) - C (liftedForce P hF Y)‖ ≤
    (L : ℝ) * ‖X-Y‖
  rw [← C.map_sub]
  exact (C.le_opNorm _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) hc).trans
      ((liftedForce_regular P hF).lipschitz X Y))

/-- Actual square-integrable per-datum scores; finite moments follow from
Lipschitz continuity and square integrability of the cloud. -/
def scoreLp (U : Fin K → Cloud.Joint dθ dz → ℝ) (L : ℝ≥0)
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) (X : Lp (Cloud.State K dθ dz) 2 P)
    (i : Fin K) : Lp (Cloud.State K dθ dz) 2 P :=
  PBGSO.liftMap P (parameterScore U i) (parameterScore_lipschitz U L hLip i) X

theorem lifted_meanForce_residual
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (X : Lp (Cloud.State K dθ dz) 2 P) :
    particleForce P hK U m L hdiff hsc hLip X -
      frozenForce P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) X =
        MiniBatchVariance.average (scoreLp P U L hLip X) := by
  let hF := Cloud.meanForce_regular hK U m L hdiff hsc hLip
  let f := scoreLp P U L hLip X
  have hs : (∑ i, f i) =ᵐ[P] fun ω => ∑ i, parameterScore U i (X ω) := by
    have hsum := Lp.coeFn_finsetSum Finset.univ f
    filter_upwards [hsum, ae_all_iff.mpr (fun i =>
      PBGSO.liftMap_coe P (parameterScore U i) (parameterScore_lipschitz U L hLip i) X)]
      with ω hw hi
    rw [hw]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ => hi i)
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (particleForce P hK U m L hdiff hsc hLip X)
    (frozenForce P hF X), liftedForce_coe P hF X,
    tailMask.coeFn_compLpL (p := 2) (μ := P) (liftedForce P hF X),
    Lp.coeFn_smul (1 / (K : ℝ)) (∑ i, f i), hs] with ω hsub hf ht ha hs
  change (particleForce P hK U m L hdiff hsc hLip X) ω = _ at hf
  change (frozenForce P hF X) ω = _ at ht
  change _ = ((1 / (K : ℝ)) • (∑ i, f i)) ω
  rw [hsub, ha]
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [ht]
  change _ - tailMask ((liftedForce P hF X) ω) = _
  rw [hf, show (liftedForce P hF X) ω = Cloud.meanForce U (X ω) from hf, hs]
  exact meanForce_residual U hdiff (X ω)

/-- A Lipschitz observable has exactly the same L² norm on equal input laws. -/
theorem liftMap_norm_eq_of_law {E A : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    (f : E → A) {C : ℝ≥0} (hf : LipschitzWith C f)
    (X Y : Lp E 2 P) (hlaw : P.map X = P.map Y) :
    ‖PBGSO.liftMap P f hf X‖ = ‖PBGSO.liftMap P f hf Y‖ := by
  have he (Z : Lp E 2 P) : ‖PBGSO.liftMap P f hf Z‖ ^ 2 =
      ∫ z, ‖f z‖ ^ 2 ∂P.map Z := by
    rw [l2_norm_sq_eq_expectation]
    have hm := integral_map (Lp.aestronglyMeasurable Z).aemeasurable
      (show AEStronglyMeasurable (fun z => ‖f z‖ ^ 2) (P.map Z) from
        (hf.continuous.norm.pow 2).aestronglyMeasurable)
    rw [hm]
    apply integral_congr_ae
    filter_upwards [PBGSO.liftMap_coe P f hf Z] with ω hω
    rw [hω]
  have h := (he X).trans ((congrArg (fun μ => ∫ z, ‖f z‖ ^ 2 ∂μ) hlaw).trans (he Y).symm)
  nlinarith [norm_nonneg (PBGSO.liftMap P f hf X), norm_nonneg (PBGSO.liftMap P f hf Y)]

/-- Exact moments of independent centered L² variables, with only the first
order condition on the sum of their means. Individual data means may differ. -/
theorem independent_average_norm_sq {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (g : Fin K → Lp E 2 P)
    (hind : iIndepFun (fun i ω => g i ω) P)
    (hopt : ∑ i, (∫ ω, g i ω ∂P) = 0) :
    ‖MiniBatchVariance.average g‖ ^ 2 = (1 / (K : ℝ)) ^ 2 *
      ∑ i, ‖g i - constantL2 P (∫ ω, g i ω ∂P)‖ ^ 2 := by
  let c (i : Fin K) := ∫ ω, g i ω ∂P
  let z (i : Fin K) := g i - constantL2 P (c i)
  have hzcoe (i : Fin K) : z i =ᵐ[P] fun ω => g i ω - c i := by
    filter_upwards [Lp.coeFn_sub (g i) (constantL2 P (c i)), constantL2_coe P (c i)]
      with ω hsub hc
    simp only [z, hsub, hc, Pi.sub_apply]
  have hmean (i : Fin K) : (∫ ω, (g i ω - c i) ∂P) = 0 := by
    rw [integral_sub ((Lp.memLp (g i)).integrable (by norm_num)) (integrable_const _)]
    simp [c]
  have hzorth (i j : Fin K) (hij : i ≠ j) : inner ℝ (z i) (z j) = 0 := by
    rw [L2.inner_def]
    have he := ((hind.indepFun hij).comp
      (show Measurable (fun x : E => x - c i) by fun_prop)
      (show Measurable (fun x : E => x - c j) by fun_prop)).integral_bilin
        (((Lp.memLp (g i)).integrable (by norm_num)).sub (integrable_const _))
        (((Lp.memLp (g j)).integrable (by norm_num)).sub (integrable_const _)) (innerSL ℝ)
    change (∫ ω, inner ℝ (g i ω - c i) (g j ω - c j) ∂P) =
      inner ℝ (∫ ω, g i ω - c i ∂P) (∫ ω, g j ω - c j ∂P) at he
    rw [hmean i, hmean j, inner_zero_left] at he
    apply (integral_congr_ae ?_).trans he
    filter_upwards [hzcoe i, hzcoe j] with ω hi hj
    rw [hi, hj]
  have hcSum : ∑ i, constantL2 P (c i) = 0 := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => constantL2 P (c i)),
      ae_all_iff.mpr (fun i => constantL2_coe P (c i)), Lp.coeFn_zero E 2 P]
      with ω hs hc hz
    rw [hs, hz]
    simp only [Finset.sum_apply]
    simpa only [hc, Pi.zero_apply, c] using hopt
  have hsum : ∑ i, z i = ∑ i, g i := by
    simp only [z, Finset.sum_sub_distrib, hcSum, sub_zero]
  rw [← MiniBatchVariance.mean_sq_sum_of_orthogonal z hzorth]
  congr 1
  exact congrArg (fun q => ‖(1 / (K : ℝ)) • q‖) hsum.symm

/-- The original latent Brownian vector is inserted without optimizer noise. -/
def tailInsert : Latent K dz →L[ℝ] Cloud.State K dθ dz :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => WithLp.toLp 2 (Sum.elim (fun _ => 0) a)
      map_add' := by intro a b; ext j; cases j <;> simp
      map_smul' := by intro c a; ext j; cases j <;> simp }

@[simp] theorem tailInsert_head (a : Latent K dz) (j : Fin dθ) :
    tailInsert a (Sum.inl j) = 0 := rfl

@[simp] theorem tailInsert_tail (a : Latent K dz) (j : Fin K × Fin dz) :
    tailInsert (dθ := dθ) a (Sum.inr j) = a j := rfl

@[simp] theorem tailInsert_norm (a : Latent K dz) :
    ‖tailInsert (dθ := dθ) a‖ = ‖a‖ := by
  have h : ‖tailInsert (dθ := dθ) a‖ ^ 2 = ‖a‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type]
  nlinarith [norm_nonneg (tailInsert (dθ := dθ) a), norm_nonneg a]

theorem tailInsert_opNorm_le : ‖(tailInsert (K := K) (dθ := dθ) (dz := dz))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => by simp)

/-- Cumulative physical noise: sqrt(2/K) Brownian forcing in scaled latent
coordinates, exactly zero parameter forcing. -/
def physicalNoise
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (t : ℝ) :
    Lp (Cloud.State K dθ dz) 2 P :=
  (Real.sqrt (K : ℝ))⁻¹ • tailInsert.compLpL 2 P (ULA.brownianLangevinNoise P B hB 0 t)

/-- Explicit physical Brownian root-mean-square coefficient. It simplifies to
sqrt(2 dz) when K>0; its displayed form also covers the empty cloud. -/
def physicalNoiseScale (K dz : ℕ) : ℝ :=
  (Real.sqrt (K : ℝ))⁻¹ * Real.sqrt (2 * ((K * dz : ℕ) : ℝ))

theorem physicalNoise_increment_bound
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    ‖physicalNoise (dθ := dθ) P B hB (a+t) - physicalNoise P B hB a‖ ≤
      physicalNoiseScale K dz * Real.sqrt t := by
  let C : Lp (Latent K dz) 2 P →L[ℝ] Lp (Cloud.State K dθ dz) 2 P :=
    tailInsert.compLpL 2 P
  have hc : ‖C‖ ≤ 1 := (ContinuousLinearMap.norm_compLpL_le _).trans tailInsert_opNorm_le
  change ‖(Real.sqrt (K : ℝ))⁻¹ • C (ULA.brownianLangevinNoise P B hB 0 (a+t)) -
    (Real.sqrt (K : ℝ))⁻¹ • C (ULA.brownianLangevinNoise P B hB 0 a)‖ ≤ _
  rw [← smul_sub, ← C.map_sub, PBGSO.MethodSegments.brownianNoise_increment,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hn := ULA.brownianLangevinNoise_norm P B hB a t ha ht
  have hn' := (C.le_opNorm (ULA.brownianLangevinNoise P B hB a t)).trans
    (mul_le_of_le_one_left (norm_nonneg _) hc)
  have h := mul_le_mul_of_nonneg_left (hn'.trans hn.le)
    (inv_nonneg.mpr (Real.sqrt_nonneg (K : ℝ)))
  simpa [physicalNoiseScale, Fintype.card_prod, mul_assoc] using h

@[simp] theorem physicalNoise_zero
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) :
    physicalNoise (dθ := dθ) P B hB 0 = 0 := by
  simp [physicalNoise]

/-- Equal laws transfer arbitrary continuous square-integrable observables. -/
theorem l2_norm_eq_of_law {E A : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
    (f : E → A) (hf : Continuous f) (X Y : Lp E 2 P) (X' Y' : Lp A 2 P)
    (hX : X' =ᵐ[P] fun ω => f (X ω)) (hY : Y' =ᵐ[P] fun ω => f (Y ω))
    (hlaw : P.map X = P.map Y) : ‖X'‖ = ‖Y'‖ := by
  have he (Z : Lp E 2 P) (Z' : Lp A 2 P) (hZ : Z' =ᵐ[P] fun ω => f (Z ω)) :
      ‖Z'‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 ∂P.map Z := by
    rw [l2_norm_sq_eq_expectation]
    have hm := integral_map (Lp.aestronglyMeasurable Z).aemeasurable
      (show AEStronglyMeasurable (fun z => ‖f z‖ ^ 2) (P.map Z) from
        (hf.norm.pow 2).aestronglyMeasurable)
    rw [hm]
    apply integral_congr_ae
    filter_upwards [hZ] with ω hω
    rw [hω]
  have h := (he X X' hX).trans
    ((congrArg (fun μ => ∫ z, ‖f z‖ ^ 2 ∂μ) hlaw).trans (he Y Y' hY).symm)
  nlinarith [norm_nonneg X', norm_nonneg Y']

theorem frozenForce_coe {F : Cloud.State K dθ dz → Cloud.State K dθ dz}
    {m : ℝ} {L : ℝ≥0} (hF : ForceRegularity F m L) (X : Lp (Cloud.State K dθ dz) 2 P) :
    frozenForce P hF X =ᵐ[P] fun ω => tailMask (F (X ω)) := by
  filter_upwards [tailMask.coeFn_compLpL (p := 2) (μ := P) (liftedForce P hF X),
    liftedForce_coe P hF X] with ω ht hf
  exact ht.trans (congrArg tailMask hf)

theorem residual_coe {F : Cloud.State K dθ dz → Cloud.State K dθ dz}
    {m : ℝ} {L : ℝ≥0} (hF : ForceRegularity F m L) (X : Lp (Cloud.State K dθ dz) 2 P) :
    liftedForce P hF X - frozenForce P hF X =ᵐ[P]
      fun ω => F (X ω) - tailMask (F (X ω)) := by
  filter_upwards [Lp.coeFn_sub (liftedForce P hF X) (frozenForce P hF X),
    liftedForce_coe P hF X, frozenForce_coe P hF X] with ω hs hf hr
  simp only [hs, Pi.sub_apply, hf, hr]

theorem frozenForce_norm_eq_of_law {F : Cloud.State K dθ dz → Cloud.State K dθ dz}
    {m : ℝ} {L : ℝ≥0} (hF : ForceRegularity F m L)
    (X Y : Lp (Cloud.State K dθ dz) 2 P) (hlaw : P.map X = P.map Y) :
    ‖frozenForce P hF X‖ = ‖frozenForce P hF Y‖ := by
  have hf : Continuous F := (LipschitzWith.of_dist_le_mul
    (fun x y => by simpa only [dist_eq_norm] using hF.lipschitz x y)).continuous
  exact l2_norm_eq_of_law P (fun x => tailMask (F x)) (tailMask.continuous.comp hf)
    X Y _ _ (frozenForce_coe P hF X) (frozenForce_coe P hF Y) hlaw

theorem residual_norm_eq_of_law {F : Cloud.State K dθ dz → Cloud.State K dθ dz}
    {m : ℝ} {L : ℝ≥0} (hF : ForceRegularity F m L)
    (X Y : Lp (Cloud.State K dθ dz) 2 P) (hlaw : P.map X = P.map Y) :
    ‖liftedForce P hF X - frozenForce P hF X‖ =
      ‖liftedForce P hF Y - frozenForce P hF Y‖ := by
  have hf : Continuous F := (LipschitzWith.of_dist_le_mul
    (fun x y => by simpa only [dist_eq_norm] using hF.lipschitz x y)).continuous
  exact l2_norm_eq_of_law P (fun x => F x - tailMask (F x))
    (hf.sub (tailMask.continuous.comp hf)) X Y _ _ (residual_coe P hF X)
      (residual_coe P hF Y) hlaw

/-- Optimizer coordinates of the frozen force vanish as an L² identity. -/
theorem parameterOutput_frozen_zero {F : Cloud.State K dθ dz → Cloud.State K dθ dz}
    {m : ℝ} {L : ℝ≥0} (hF : ForceRegularity F m L) (X : Lp (Cloud.State K dθ dz) 2 P) :
    parameterOutput P (frozenForce P hF X) = 0 := by
  apply Lp.ext
  filter_upwards [(@IPLA.parameterCLM K dθ dz).coeFn_compLpL
    (frozenForce P hF X), frozenForce_coe P hF X, Lp.coeFn_zero (Parameter dθ) 2 P]
      with ω hp hf hz
  change (parameterOutput P (frozenForce P hF X)) ω = _ at hp
  rw [hp, hf, hz]
  ext j
  simp

/-- Every physical Brownian input has exactly zero optimizer coordinates. -/
theorem parameterOutput_noise_zero
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (t : ℝ) :
    parameterOutput (dθ := dθ) P (physicalNoise P B hB t) = 0 := by
  let Z := ULA.brownianLangevinNoise P B hB 0 t
  have he : parameterOutput (dθ := dθ) P (tailInsert.compLpL 2 P Z) = 0 := by
    apply Lp.ext
    filter_upwards [(@IPLA.parameterCLM K dθ dz).coeFn_compLpL
      (tailInsert.compLpL 2 P Z), tailInsert.coeFn_compLpL (p := 2) (μ := P) Z,
      Lp.coeFn_zero (Parameter dθ) 2 P] with ω hp ht hz
    change (parameterOutput P (tailInsert.compLpL 2 P Z)) ω = _ at hp
    rw [hp, ht, hz]
    ext j
    simp
  simp only [physicalNoise, Z, map_smul, he, smul_zero]

/-- Additional analytic solution assumption: an actual continuous frozen
posterior solution with its literal Brownian integral equation and invariant
cloud law. Invariance is explicitly a probability-law assumption, separate
from smoothness. No desired finite-particle or discretization estimate occurs.
A Gibbs-stationarity bridge below discharges invariance from an initial Gibbs
law and independent Brownian inputs whenever the latent potential is supplied.
-/
structure FrozenPosteriorSolution
    {F : Cloud.State K dθ dz → Cloud.State K dθ dz} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L)
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) where
  path : ℝ → Lp (Cloud.State K dθ dz) 2 P
  continuous : Continuous path
  equation : ∀ t, 0 ≤ t → path t - path 0 =
    -(∫ r in 0..t, frozenForce P hF (path r)) + physicalNoise P B hB t
  stationary_law : ∀ t, 0 ≤ t → P.map (path t) = P.map (path 0)

variable {F : Cloud.State K dθ dz → Cloud.State K dθ dz} {m : ℝ} {L : ℝ≥0}
  {hF : ForceRegularity F m L}
  {B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ}
  {hB : ∀ i, IsPreBrownianReal (B i) P}

/-- The constant optimizer is proved from zero optimizer drift and zero noise. -/
theorem FrozenPosteriorSolution.parameter_constant
    (S : FrozenPosteriorSolution P hF B hB) (t : ℝ) (ht : 0 ≤ t) :
    parameterOutput P (S.path t) = parameterOutput P (S.path 0) := by
  let C := parameterOutput (K := K) (dθ := dθ) (dz := dz) P
  have hi := C.intervalIntegral_comp_comm (μ := volume)
    (((frozenForce_lipschitz P hF).continuous.comp S.continuous).intervalIntegrable 0 t)
  simp only [Function.comp_apply] at hi
  have hi0 : C (∫ r in 0..t, frozenForce P hF (S.path r)) = 0 := by
    rw [← hi]
    simp only [C, parameterOutput_frozen_zero, intervalIntegral.integral_zero]
  have he := congrArg C (S.equation t ht)
  simp only [map_sub, map_add, map_neg, hi0, neg_zero,
    C, parameterOutput_noise_zero, add_zero] at he
  exact sub_eq_zero.mp he

/-- Segment moment and local defect inputs are all constructed from the global
stationary equation. The drift radius is its exact initial L² norm. -/
theorem FrozenPosteriorSolution.integralReference
    (S : FrozenPosteriorSolution P hF B hB) (h : ℝ) (hh : 0 ≤ h) :
    IntegralReference (frozenForce P hF) h ‖frozenForce P hF (S.path 0)‖
      (physicalNoiseScale K dz)
      (fun n => S.path ((n : ℝ) * h))
      (fun n => physicalNoise P B hB ((n : ℝ)*h+h) - physicalNoise P B hB ((n : ℝ)*h))
      (fun n t => S.path ((n : ℝ)*h+t))
      (fun n t => physicalNoise P B hB ((n : ℝ)*h+t) - physicalNoise P B hB ((n : ℝ)*h)) where
  starts n := by simp
  ends n := by congr 1; push_cast; ring
  noise_end n := rfl
  integrable n := ((frozenForce_lipschitz P hF).continuous.comp
    (S.continuous.comp (continuous_const.add continuous_id))).intervalIntegrable 0 h
  drift_radius n t ht := (frozenForce_norm_eq_of_law P hF _ _
    (S.stationary_law ((n : ℝ)*h+t) (by positivity [ht.1]))).le
  noise_growth n t ht := physicalNoise_increment_bound P B hB _ _ (by positivity) ht.1
  equation n t ht := by
    have he := PBGSO.MethodSegments.integral_shift S.path
      (fun r => -frozenForce P hF (S.path r)) (physicalNoise P B hB)
      ((frozenForce_lipschitz P hF).continuous.comp S.continuous).neg
      (fun r hr => by simpa only [intervalIntegral.integral_neg] using S.equation r hr)
      ((n : ℝ)*h) t (by positivity) ht.1
    simpa only [intervalIntegral.integral_neg, add_zero] using he

/-- Exact initial score-variance budget. It is a finite sum of genuine L²
moments, not an assumed bound on a sampling residual. -/
def scoreVarianceBudget (U : Fin K → Cloud.Joint dθ dz → ℝ) (L : ℝ≥0)
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (X : Lp (Cloud.State K dθ dz) 2 P) : ℝ :=
  ∑ i, ‖scoreLp P U L hLip X i -
    constantL2 P (∫ ω, scoreLp P U L hLip X i ω ∂P)‖ ^ 2

/-- The full-batch discretization converges to the specified optimizer with
finite-cloud and time-step errors derived from the actual posterior equation.
Initialization, finite-particle variance, drift discretization and Brownian
roughness appear separately; there is no numerical-error hypothesis. -/
theorem full_batch_parameter_bound
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m h : ℝ) (L : ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) (hs : StableStep m L h)
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (S : FrozenPosteriorSolution P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) B hB)
    (hind : iIndepFun (fun i ω => scoreLp P U L hLip (S.path 0) i ω) P)
    (hopt : ∑ i, (∫ ω, scoreLp P U L hLip (S.path 0) i ω ∂P) = 0)
    (x₀ : Lp (Cloud.State K dθ dz) 2 P) (astar : Parameter dθ)
    (hstar : parameterOutput P (S.path 0) = constantL2 P astar) (n : ℕ) :
    ‖parameterOutput P
      (eulerTrajectory (particleForce P hK U m L hdiff hsc hLip) h
        (fun k => physicalNoise P B hB ((k : ℝ)*h+h) - physicalNoise P B hB ((k : ℝ)*h)) x₀ n) -
      constantL2 P astar‖ ≤
      (1 - m*h/2)^n * ‖x₀ - S.path 0‖ +
      (2/m) * Real.sqrt ((1/(K : ℝ))^2 * scoreVarianceBudget P U L hLip (S.path 0)) +
      (L : ℝ)/m * (h * ‖frozenForce P (Cloud.meanForce_regular hK U m L hdiff hsc hLip)
        (S.path 0)‖ + (4/3 : ℝ)*physicalNoiseScale K dz*Real.sqrt h) := by
  let hF := Cloud.meanForce_regular hK U m L hdiff hsc hLip
  let F := particleForce P hK U m L hdiff hsc hLip
  let R := frozenForce P hF
  let b := Real.sqrt ((1/(K : ℝ))^2 * scoreVarianceBudget P U L hLip (S.path 0))
  have hres (k : ℕ) : ‖F (S.path ((k : ℝ)*h)) - R (S.path ((k : ℝ)*h))‖ ≤ b := by
    change ‖liftedForce P hF (S.path ((k : ℝ)*h)) - frozenForce P hF (S.path ((k : ℝ)*h))‖ ≤ b
    rw [residual_norm_eq_of_law P hF _ _ (S.stationary_law _ (mul_nonneg (Nat.cast_nonneg _) hs.positive.le))]
    change ‖particleForce P hK U m L hdiff hsc hLip (S.path 0) -
      frozenForce P hF (S.path 0)‖ ≤ b
    rw [lifted_meanForce_residual P hK U m L hdiff hsc hLip]
    have hv := independent_average_norm_sq P (scoreLp P U L hLip (S.path 0)) hind hopt
    change ‖MiniBatchVariance.average (scoreLp P U L hLip (S.path 0))‖ ≤ Real.sqrt _
    unfold scoreVarianceBudget
    rw [← hv, Real.sqrt_sq (norm_nonneg _)]
  have he := equilibrium_reference_error F R m h b ‖R (S.path 0)‖ (physicalNoiseScale K dz)
    L (liftedForce_regular P hF) (frozenForce_lipschitz P hF) hs (Real.sqrt_nonneg _)
    (norm_nonneg _) (by unfold physicalNoiseScale; positivity)
    _ _ _ _ x₀ (S.integralReference P h hs.positive.le) hres n
  have ht : parameterOutput P (S.path ((n : ℝ)*h)) = constantL2 P astar :=
    (S.parameter_constant P _ (mul_nonneg (Nat.cast_nonneg _) hs.positive.le)).trans hstar
  rw [← ht, ← map_sub]
  have hc := (parameterOutput P).le_opNorm
    (eulerTrajectory F h
      (fun k => physicalNoise P B hB ((k : ℝ)*h+h) - physicalNoise P B hB ((k : ℝ)*h)) x₀ n -
        S.path ((n : ℝ)*h))
  apply (hc.trans (mul_le_of_le_one_left (norm_nonneg _) (parameterOutput_norm_le P))).trans
  simpa [b, R, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using he

/-- Physical latent configurations in particle-normalized cloud coordinates. -/
def pack (astar : Parameter dθ) (z : Latent K dz) : Cloud.State K dθ dz :=
  headInsert astar + (Real.sqrt (K : ℝ))⁻¹ • tailInsert z

/-- The same physical embedding acting on actual L² random variables. -/
def packLp (astar : Parameter dθ) (Z : Lp (Latent K dz) 2 P) :
    Lp (Cloud.State K dθ dz) 2 P :=
  constantL2 P (headInsert astar) + (Real.sqrt (K : ℝ))⁻¹ • tailInsert.compLpL 2 P Z

theorem packLp_coe (astar : Parameter dθ) (Z : Lp (Latent K dz) 2 P) :
    packLp P astar Z =ᵐ[P] fun ω => pack astar (Z ω) := by
  filter_upwards [Lp.coeFn_add (constantL2 P (headInsert astar))
    ((Real.sqrt (K : ℝ))⁻¹ • tailInsert.compLpL 2 P Z),
    constantL2_coe P (headInsert (J := Fin K × Fin dz) astar),
    Lp.coeFn_smul (Real.sqrt (K : ℝ))⁻¹ (tailInsert.compLpL 2 P Z),
    (tailInsert (dθ := dθ)).coeFn_compLpL (p := 2) (μ := P) Z] with ω ha hc hs ht
  change _ = headInsert astar + (Real.sqrt (K : ℝ))⁻¹ • tailInsert (Z ω)
  unfold packLp
  rw [ha]
  simp only [Pi.add_apply]
  rw [hc, hs]
  simp only [Pi.smul_apply]
  rw [ht]

theorem packLp_continuous (astar : Parameter dθ) : Continuous (packLp (K := K) (dz := dz) P astar) := by
  unfold packLp
  fun_prop

theorem packLp_law_eq (astar : Parameter dθ) (Z T : Lp (Latent K dz) 2 P)
    (h : P.map Z = P.map T) : P.map (packLp P astar Z) = P.map (packLp P astar T) := by
  rw [Measure.map_congr (packLp_coe P astar Z), Measure.map_congr (packLp_coe P astar T)]
  have hm : Measurable (pack (K := K) (dz := dz) astar) := by
    have hc : Continuous (pack (K := K) (dz := dz) astar) := by unfold pack; fun_prop
    exact hc.measurable
  change P.map (pack astar ∘ Z) = P.map (pack astar ∘ T)
  rw [← Measure.map_map hm (Lp.stronglyMeasurable Z).measurable,
    ← Measure.map_map hm (Lp.stronglyMeasurable T).measurable, h]

/-- A structural pointwise force identity passes to actual L² force maps.
For the manuscript the latent potential is the sum of frozen datum potentials.
This is an identity of coefficients, not an error bound. -/
theorem frozenForce_packLp {F : Cloud.State K dθ dz → Cloud.State K dθ dz}
    {m : ℝ} {L : ℝ≥0} (hF : ForceRegularity F m L)
    (V : Latent K dz → ℝ) (A : ℝ≥0) (hV : LipschitzWith A (gradient V))
    (astar : Parameter dθ)
    (hforce : ∀ z, tailMask (F (pack astar z)) =
      (Real.sqrt (K : ℝ))⁻¹ • tailInsert (gradient V z)) (Z : Lp (Latent K dz) 2 P) :
    frozenForce P hF (packLp P astar Z) =
      (Real.sqrt (K : ℝ))⁻¹ • tailInsert.compLpL 2 P (ULA.lpDrift P (gradient V) hV Z) := by
  apply Lp.ext
  filter_upwards [frozenForce_coe P hF (packLp P astar Z), packLp_coe P astar Z,
    Lp.coeFn_smul (Real.sqrt (K : ℝ))⁻¹
      (tailInsert.compLpL 2 P (ULA.lpDrift P (gradient V) hV Z)),
    (tailInsert (dθ := dθ)).coeFn_compLpL (p := 2) (μ := P)
      (ULA.lpDrift P (gradient V) hV Z), ULA.lpDrift_coe P (gradient V) hV Z]
      with ω hr hp hs ht hv
  rw [hr, hp, hs]
  simp only [Pi.smul_apply]
  rw [ht, hv, hforce]

/-- Gibbs stationarity discharges the invariant-law field from a genuine
latent Langevin equation, initial Gibbs law, and independent Brownian inputs.
No invariant process law or moment estimate is assumed in this constructor. -/
def FrozenPosteriorSolution.of_latent_gibbs
    {F : Cloud.State K dθ dz → Cloud.State K dθ dz} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L)
    (V : Latent K dz → ℝ) (a : ℝ) (A : ℝ≥0) (ha : 0 < a)
    (hdiff : Differentiable ℝ V) (hsc : StrongConvexOn Set.univ a V)
    (hV : LipschitzWith A (gradient V)) (astar : Parameter dθ)
    (hforce : ∀ z, tailMask (F (pack astar z)) =
      (Real.sqrt (K : ℝ))⁻¹ • tailInsert (gradient V z))
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (Z : ℝ → Lp (Latent K dz) 2 P) (hZ : Continuous Z)
    (hZe : ∀ t, 0 ≤ t → Z t - Z 0 =
      -(∫ r in 0..t, ULA.lpDrift P (gradient V) hV (Z r)) + ULA.brownianLangevinNoise P B hB 0 t)
    (hinitial : P.map (Z 0) = ULA.gibbsMeasure V)
    (hscalar : ∀ h : ℝ, 0 < h → iIndepFun (fun p : ℕ × (Fin K × Fin dz) => fun ω =>
      ULA.Hilbert.brownianEulerNoise P B hB h p.1 ω p.2) P)
    (hind : ∀ h : ℝ, 0 < h → IndepFun (Z 0)
      (fun ω n => ULA.Hilbert.brownianEulerNoise P B hB h n ω) P) :
    FrozenPosteriorSolution P hF B hB where
  path t := packLp P astar (Z t)
  continuous := (packLp_continuous P astar).comp hZ
  equation t ht := by
    let C : Lp (Latent K dz) 2 P →L[ℝ] Lp (Cloud.State K dθ dz) 2 P :=
      (Real.sqrt (K : ℝ))⁻¹ • tailInsert.compLpL 2 P
    have hC (r : ℝ) : C (ULA.lpDrift P (gradient V) hV (Z r)) =
      frozenForce P hF (packLp P astar (Z r)) :=
      (frozenForce_packLp P hF V A hV astar hforce (Z r)).symm
    have hi := C.intervalIntegral_comp_comm (μ := volume)
      (((ULA.lpDrift_lipschitz P (gradient V) hV).continuous.comp hZ).intervalIntegrable 0 t)
    simp only [Function.comp_apply] at hi
    have he := congrArg C (hZe t ht)
    simp only [map_sub, map_add, map_neg, ← hi, hC] at he
    simpa only [packLp, C, smul_apply, physicalNoise,
      add_sub_add_left_eq_sub] using he
  stationary_law t ht := by
    apply packLp_law_eq P astar
    rw [hinitial]
    exact ULA.lp_langevin_gibbs_stationary P V a A ha hdiff hsc hV (Z 0) hinitial
      B hB hscalar hind Z hZ t ht (fun s hs => hZe s hs.1)

/-- The cloud-noise coefficient has no particle-number penalty. -/
theorem physicalNoiseScale_eq (hK : 0 < K) : physicalNoiseScale K dz = Real.sqrt (2 * (dz : ℝ)) := by
  have hK0 : (Real.sqrt (K : ℝ)) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hK)
  unfold physicalNoiseScale
  rw [show (2 * ((K * dz : ℕ) : ℝ)) = (K : ℝ) * (2 * (dz : ℝ)) by push_cast; ring,
    Real.sqrt_mul (Nat.cast_nonneg K)]
  rw [← mul_assoc, inv_mul_cancel₀ hK0, one_mul]

/-- Extract all scaled latent coordinates. -/
def tailExtract : Cloud.State K dθ dz →L[ℝ] Latent K dz :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun j => x (Sum.inr j))
      map_add' := by intro a b; rfl
      map_smul' := by intro c a; rfl }

@[simp] theorem tailExtract_apply (x : Cloud.State K dθ dz) (j : Fin K × Fin dz) :
    tailExtract x j = x (Sum.inr j) := rfl

theorem tailExtract_norm_le (x : Cloud.State K dθ dz) : ‖tailExtract x‖ ≤ ‖x‖ := by
  have h : ‖tailExtract x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, tailExtract_apply, Fintype.sum_sum_type]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (tailExtract x), norm_nonneg x]

@[simp] theorem tailInsert_single (j : Fin K × Fin dz) :
    tailInsert (dθ := dθ) (EuclideanSpace.single j 1) =
      EuclideanSpace.single (Sum.inr j) 1 := by
  ext a
  cases a <;> simp [tailInsert, Pi.single_apply]

/-- The physical frozen posterior potential, summed over all datum-particle
pairs. Its latent Gibbs measure has the manuscript's unit temperature. -/
def frozenPotential (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (astar : Parameter dθ) (z : Latent K dz) : ℝ :=
  Cloud.potential U (pack astar z)

theorem pack_sub (astar : Parameter dθ) (z w : Latent K dz) :
    pack astar z - pack astar w = (Real.sqrt (K : ℝ))⁻¹ • tailInsert (z-w) := by
  simp only [pack, add_sub_add_left_eq_sub, map_sub, smul_sub]

theorem pack_norm_sub (astar : Parameter dθ) (z w : Latent K dz) :
    ‖pack astar z - pack astar w‖ = (Real.sqrt (K : ℝ))⁻¹ * ‖z-w‖ := by
  rw [pack_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), tailInsert_norm]

theorem frozenPotential_differentiable
    (U : Fin K → Cloud.Joint dθ dz → ℝ) (hdiff : ∀ i, Differentiable ℝ (U i))
    (astar : Parameter dθ) : Differentiable ℝ (frozenPotential U astar) := by
  apply (Cloud.potential_differentiable hdiff).comp
  let C : Latent K dz →L[ℝ] Cloud.State K dθ dz := (Real.sqrt (K : ℝ))⁻¹ • tailInsert
  change Differentiable ℝ (fun z => headInsert astar + C z)
  exact (differentiable_const _).add C.differentiable

/-- Chain rule includes exactly the reciprocal-sqrt(K) scaling. -/
theorem gradient_frozenPotential
    (U : Fin K → Cloud.Joint dθ dz → ℝ) (hdiff : ∀ i, Differentiable ℝ (U i))
    (astar : Parameter dθ) (z : Latent K dz) :
    gradient (frozenPotential U astar) z =
      (Real.sqrt (K : ℝ))⁻¹ • tailExtract (gradient (Cloud.potential U) (pack astar z)) := by
  let C : Latent K dz →L[ℝ] Cloud.State K dθ dz := (Real.sqrt (K : ℝ))⁻¹ • tailInsert
  have hp : HasFDerivAt (pack astar) C z := by
    change HasFDerivAt (fun z => headInsert astar + C z) C z
    exact HasFDerivAt.const_add _ C.hasFDerivAt
  have hd := ((Cloud.potential_differentiable hdiff) (pack astar z)).hasFDerivAt.comp z hp
  ext j
  have h := inner_gradient_left (𝕜 := ℝ) (f := frozenPotential U astar) (x := z)
    (y := EuclideanSpace.single j 1)
  rw [show fderiv ℝ (frozenPotential U astar) z =
    (fderiv ℝ (Cloud.potential U) (pack astar z)).comp C from hd.fderiv] at h
  simp only [ContinuousLinearMap.comp_apply, C, smul_apply, tailInsert_single,
    map_smul, ← inner_gradient_left,
    EuclideanSpace.inner_single_right, one_mul, conj_trivial] at h
  simpa only [PiLp.smul_apply, smul_eq_mul, tailExtract_apply] using h

/-- No free coefficient-matching assumption remains: the actual heterogeneous
frozen cloud force is the embedded gradient of the displayed latent potential. -/
theorem frozenPotential_force_identity (hK : 0 < K)
    (U : Fin K → Cloud.Joint dθ dz → ℝ) (hdiff : ∀ i, Differentiable ℝ (U i))
    (astar : Parameter dθ) (z : Latent K dz) :
    tailMask (Cloud.meanForce U (pack astar z)) =
      (Real.sqrt (K : ℝ))⁻¹ • tailInsert (gradient (frozenPotential U astar) z) := by
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  have hs : ((Real.sqrt (K : ℝ))⁻¹)^2 = (K : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg K)]
  rw [gradient_frozenPotential U hdiff astar z]
  ext j
  cases j with
  | inl j => simp
  | inr j =>
    simp only [tailMask_tail, Cloud.meanForce, PiLp.smul_apply, smul_eq_mul,
      tailInsert_tail, map_smul, tailExtract_apply]
    nlinarith [congrArg (fun a : ℝ => a * gradient (Cloud.potential U) (pack astar z) (Sum.inr j)) hs]

theorem inv_sqrt_sq (K : ℕ) : ((Real.sqrt (K : ℝ))⁻¹)^2 = (K : ℝ)⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg K)]

theorem pack_affine (astar : Parameter dθ) (z w : Latent K dz)
    (a b : ℝ) (hab : a+b=1) :
    pack astar (a • z + b • w) = a • pack astar z + b • pack astar w := by
  unfold pack
  rw [map_add, map_smul, map_smul]
  have hc : a • headInsert (J := Fin K × Fin dz) astar + b • headInsert astar = headInsert astar := by
    rw [← add_smul, hab, one_smul]
  conv_lhs => rw [← hc]
  module

theorem frozenPotential_strongConvex (hK : 0 < K)
    (U : Fin K → Cloud.Joint dθ dz → ℝ) (m : ℝ)
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i)) (astar : Parameter dθ) :
    StrongConvexOn Set.univ m (frozenPotential U astar) := by
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  refine ⟨convex_univ, ?_⟩
  intro z hz w hw a b ha hb hab
  have hc := (Cloud.potential_strongConvex hsc).2 (Set.mem_univ (pack astar z))
    (Set.mem_univ (pack astar w)) ha hb hab
  rw [← pack_affine astar z w a b hab, pack_norm_sub] at hc
  dsimp only at hc ⊢
  rw [mul_pow, inv_sqrt_sq] at hc
  have he : ((K : ℝ)*m/2) * ((K : ℝ)⁻¹ * ‖z-w‖^2) =
      (m/2)*‖z-w‖^2 := by field_simp
  simpa only [frozenPotential, smul_eq_mul, he] using hc

theorem frozenPotential_gradient_lipschitz (hK : 0 < K)
    (U : Fin K → Cloud.Joint dθ dz → ℝ) (L : ℝ≥0)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) (astar : Parameter dθ) :
    LipschitzWith L (gradient (frozenPotential U astar)) := by
  have hK0 : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  let s := (Real.sqrt (K : ℝ))⁻¹
  have hs : 0 ≤ s := inv_nonneg.mpr (Real.sqrt_nonneg _)
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm, gradient_frozenPotential U hdiff, ← smul_sub, ← map_sub,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (K : ℝ)))]
  calc
    s * ‖tailExtract (gradient (Cloud.potential U) (pack astar z) -
        gradient (Cloud.potential U) (pack astar w))‖ ≤
      s * ‖gradient (Cloud.potential U) (pack astar z) -
        gradient (Cloud.potential U) (pack astar w)‖ :=
      mul_le_mul_of_nonneg_left (tailExtract_norm_le _) hs
    _ ≤ s * (((K : ℝ)*(L : ℝ)) * ‖pack astar z - pack astar w‖) := by
      have ht := (Cloud.potential_gradient_lipschitz hdiff hLip).norm_sub_le (pack astar z) (pack astar w)
      simpa only [NNReal.coe_mul, NNReal.coe_natCast] using mul_le_mul_of_nonneg_left ht hs
    _ = (L : ℝ) * ‖z-w‖ := by
      rw [pack_norm_sub]
      change s * ((K : ℝ)*(L : ℝ)*(s*‖z-w‖)) = _
      calc
        _ = (s^2*(K : ℝ)) * (L : ℝ) * ‖z-w‖ := by ring
        _ = _ := by rw [show s^2 = (K : ℝ)⁻¹ from inv_sqrt_sq K, inv_mul_cancel₀ hK0, one_mul]

/-- Global Picard construction for a Lipschitz force. Finite-horizon Picard
solutions are glued by their proved same-input uniqueness. -/
theorem exists_global_integral {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] (g : H → H) (C : ℝ≥0) (hg : LipschitzWith C g)
    (initial : H) (W : ℝ → H) (hW : Continuous W) (hW0 : W 0 = 0) :
    ∃ Y : ℝ → H, Continuous Y ∧ Y 0 = initial ∧
      ∀ t, 0 ≤ t → Y t - Y 0 = -(∫ r in 0..t, g (Y r)) + W t := by
  classical
  let flow := fun n : ℕ => Classical.choose
    (ULA.exists_langevin_integral g C hg initial W hW hW0 ((n : ℝ)+1) (by positivity))
  have hs (n : ℕ) : Continuous (flow n) ∧ flow n 0 = initial ∧
      ∀ t ∈ Icc 0 ((n : ℝ)+1), flow n t - initial =
        -(∫ r in 0..t, g (flow n r)) + W t :=
    Classical.choose_spec (ULA.exists_langevin_integral g C hg initial W hW hW0 ((n : ℝ)+1) (by positivity))
  have coherent (m n : ℕ) (r : ℝ) (hr : 0 ≤ r)
      (hm : r ≤ (m : ℝ)+1) (hn : r ≤ (n : ℝ)+1) : flow m r = flow n r := by
    exact ULA.langevin_integral_unique g C hg initial W (flow m) (flow n)
      (hs m).1 (hs n).1 r hr
      (fun t ht => (hs m).2.2 t ⟨ht.1, ht.2.trans hm⟩)
      (fun t ht => (hs n).2.2 t ⟨ht.1, ht.2.trans hn⟩) ⟨hr, le_rfl⟩
  let Y := fun t : ℝ => flow (Nat.ceil (max 0 t)) (max 0 t)
  have agree (n : ℕ) (r : ℝ) (hr : max 0 r ≤ (n : ℝ)+1) : Y r = flow n (max 0 r) := by
    apply coherent _ n _ (le_max_left _ _)
    · exact (Nat.le_ceil _).trans (by linarith)
    · exact hr
  have hc : Continuous Y := by
    apply continuous_iff_continuousAt.mpr
    intro t
    let n := Nat.ceil (max 0 t)
    have ht : max 0 t < (n : ℝ)+1 := lt_of_le_of_lt (Nat.le_ceil _) (by linarith)
    have hc : Continuous (fun r : ℝ => max 0 r) := continuous_const.max continuous_id
    have hev : ∀ᶠ r in nhds t, max 0 r < (n : ℝ)+1 :=
      hc.continuousAt.eventually (gt_mem_nhds ht)
    apply ((hs n).1.comp hc).continuousAt.congr_of_eventuallyEq
    exact hev.mono fun r hr => agree n r hr.le
  have hz : Y 0 = initial := by
    have he : Y 0 = flow 0 0 := by simpa only [max_self] using agree 0 0 (by norm_num)
    exact he.trans (hs 0).2.1
  refine ⟨Y, hc, hz, ?_⟩
  intro t ht
  let n := Nat.ceil t
  have hnt : t ≤ (n : ℝ)+1 := (Nat.le_ceil t).trans (by linarith)
  have he (r : ℝ) (hr : r ∈ Icc 0 t) : Y r = flow n r := by
    simpa only [max_eq_right hr.1] using agree n r (by rw [max_eq_right hr.1]; exact hr.2.trans hnt)
  have hi : (∫ r in 0..t, g (Y r)) = ∫ r in 0..t, g (flow n r) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht] at hr
    change g (Y r) = g (flow n r)
    rw [he r hr]
  rw [he t ⟨ht, le_rfl⟩, hz, hi]
  exact (hs n).2.2 t ⟨ht, hnt⟩

/-- The frozen posterior Langevin trajectory is constructed from the actual
initial random variable and Brownian path; existence is not a new hypothesis. -/
def latentFlow (V : Latent K dz → ℝ) (A : ℝ≥0) (hV : LipschitzWith A (gradient V))
    (initial : Lp (Latent K dz) 2 P)
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) : ℝ → Lp (Latent K dz) 2 P :=
  Classical.choose (exists_global_integral (ULA.lpDrift P (gradient V) hV) A
    (ULA.lpDrift_lipschitz P (gradient V) hV) initial (ULA.brownianLangevinNoise P B hB 0)
    (ULA.brownianLangevinNoise_continuous P B hB 0) (ULA.brownianLangevinNoise_zero P B hB 0))

theorem latentFlow_spec (V : Latent K dz → ℝ) (A : ℝ≥0) (hV : LipschitzWith A (gradient V))
    (initial : Lp (Latent K dz) 2 P)
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) :
    Continuous (latentFlow P V A hV initial B hB) ∧
      latentFlow P V A hV initial B hB 0 = initial ∧
      ∀ t, 0 ≤ t → latentFlow P V A hV initial B hB t - latentFlow P V A hV initial B hB 0 =
        -(∫ r in 0..t, ULA.lpDrift P (gradient V) hV (latentFlow P V A hV initial B hB r)) +
          ULA.brownianLangevinNoise P B hB 0 t :=
  Classical.choose_spec (exists_global_integral (ULA.lpDrift P (gradient V) hV) A
    (ULA.lpDrift_lipschitz P (gradient V) hV) initial (ULA.brownianLangevinNoise P B hB 0)
    (ULA.brownianLangevinNoise_continuous P B hB 0) (ULA.brownianLangevinNoise_zero P B hB 0))

/-- The manuscript's actual heterogeneous stationary reference, fully
constructed from initial Gibbs data and independent Brownian coordinates. -/
def sourceReference
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hm : 0 < m) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) (astar : Parameter dθ)
    (initial : Lp (Latent K dz) 2 P)
    (hinitial : P.map initial = ULA.gibbsMeasure (frozenPotential U astar))
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hscalar : ∀ h : ℝ, 0 < h → iIndepFun (fun p : ℕ × (Fin K × Fin dz) => fun ω =>
      ULA.Hilbert.brownianEulerNoise P B hB h p.1 ω p.2) P)
    (hind : ∀ h : ℝ, 0 < h → IndepFun initial
      (fun ω n => ULA.Hilbert.brownianEulerNoise P B hB h n ω) P) :
    FrozenPosteriorSolution P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) B hB := by
  let V := frozenPotential U astar
  let hv := frozenPotential_gradient_lipschitz hK U L hdiff hLip astar
  let Z := latentFlow P V L hv initial B hB
  have hs := latentFlow_spec P V L hv initial B hB
  have hzero : Z 0 = initial := hs.2.1
  exact FrozenPosteriorSolution.of_latent_gibbs P
    (Cloud.meanForce_regular hK U m L hdiff hsc hLip) V m L hm
    (frozenPotential_differentiable U hdiff astar) (frozenPotential_strongConvex hK U m hsc astar)
    hv astar (frozenPotential_force_identity hK U hdiff astar) B hB Z hs.1 hs.2.2
    (by rw [hzero]; exact hinitial) hscalar (by rw [hzero]; exact hind)

/-- Packing retains exactly the specified deterministic parameter. -/
theorem parameterOutput_packLp (astar : Parameter dθ) (Z : Lp (Latent K dz) 2 P) :
    parameterOutput P (packLp P astar Z) = constantL2 P astar := by
  apply Lp.ext
  filter_upwards [(@IPLA.parameterCLM K dθ dz).coeFn_compLpL (packLp P astar Z),
    packLp_coe P astar Z, constantL2_coe P astar] with ω hp hpack hc
  change (parameterOutput P (packLp P astar Z)) ω = _ at hp
  rw [hp, hpack, hc]
  ext j
  simp [pack]

/-- The constructed reference starts from the supplied posterior coupling. -/
theorem sourceReference_initial
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hm : 0 < m) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) (astar : Parameter dθ)
    (initial : Lp (Latent K dz) 2 P)
    (hinitial : P.map initial = ULA.gibbsMeasure (frozenPotential U astar))
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hscalar : ∀ h : ℝ, 0 < h → iIndepFun (fun p : ℕ × (Fin K × Fin dz) => fun ω =>
      ULA.Hilbert.brownianEulerNoise P B hB h p.1 ω p.2) P)
    (hind : ∀ h : ℝ, 0 < h → IndepFun initial
      (fun ω n => ULA.Hilbert.brownianEulerNoise P B hB h n ω) P) :
    (sourceReference P hK U m L hm hdiff hsc hLip astar initial hinitial B hB hscalar hind).path 0 =
      packLp P astar initial := by
  change packLp P astar (latentFlow P (frozenPotential U astar) L
    (frozenPotential_gradient_lipschitz hK U L hdiff hLip astar) initial B hB 0) = _
  rw [(latentFlow_spec P _ _ _ initial B hB).2.1]

/-- The reference drift RMS is bounded from the Gibbs score theorem itself;
no a priori drift-moment bound is required. -/
theorem initial_frozen_drift_bound
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hm : 0 < m) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) (astar : Parameter dθ)
    (initial : Lp (Latent K dz) 2 P)
    (hinitial : P.map initial = ULA.gibbsMeasure (frozenPotential U astar)) :
    ‖frozenForce P (Cloud.meanForce_regular hK U m L hdiff hsc hLip)
      (packLp P astar initial)‖ ≤ Real.sqrt ((L : ℝ) * (dz : ℝ)) := by
  let hv := frozenPotential_gradient_lipschitz hK U L hdiff hLip astar
  rw [frozenForce_packLp P _ (frozenPotential U astar) L hv astar
    (frozenPotential_force_identity hK U hdiff astar)]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hc : ‖(tailInsert (K := K) (dθ := dθ) (dz := dz)).compLpL 2 P‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le _).trans tailInsert_opNorm_le
  have hn := ((tailInsert (K := K) (dθ := dθ) (dz := dz)).compLpL 2 P).le_opNorm
    (ULA.lpDrift P (gradient (frozenPotential U astar)) hv initial)
  have hg := ULA.lpDrift_norm_le_of_strongConvex_gibbs_law P (frozenPotential U astar) m L hm
    (frozenPotential_differentiable U hdiff astar) (frozenPotential_strongConvex hK U m hsc astar)
    hv initial hinitial
  have h := mul_le_mul_of_nonneg_left
    (hn.trans ((mul_le_of_le_one_left (norm_nonneg _) hc).trans hg))
    (inv_nonneg.mpr (Real.sqrt_nonneg (K : ℝ)))
  have hK0 : Real.sqrt (K : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hK)
  have he : (Real.sqrt (K : ℝ))⁻¹ * Real.sqrt ((L : ℝ) * (Module.finrank ℝ (Latent K dz) : ℝ)) =
      Real.sqrt ((L : ℝ) * (dz : ℝ)) := by
    rw [show ((L : ℝ) * (Module.finrank ℝ (Latent K dz) : ℝ)) =
      (K : ℝ) * ((L : ℝ) * (dz : ℝ)) by simp [Latent]; ring,
      Real.sqrt_mul (Nat.cast_nonneg K), ← mul_assoc, inv_mul_cancel₀ hK0, one_mul]
  exact h.trans_eq he

end Probability
end LatentDiffusion.RegularStochastic
