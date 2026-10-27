import LatentDiffusion.RegularStochastic
import PBGSO.AdditiveContraction
import ProximalLangevin.MeanFieldCopies
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Actual nonstationary mean-field, spatial, and temporal comparisons

All drifts are computed from the original heterogeneous pair potentials. The
added moment assumptions concern actual reference forces, and the independence
assumptions concern the supplied independent posterior/reference copies.
Neither a propagation-of-chaos estimate nor a numerical error is a premise.
-/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators RealInnerProductSpace
namespace LatentDiffusion.RegularMeanField
open RegularStochastic
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {K dθ dz : ℕ}

/-- Average the parameter coordinates; preserve each latent random variable. -/
def averageCLM : Lp (Cloud.State K dθ dz) 2 P →L[ℝ] Lp (Cloud.State K dθ dz) 2 P :=
  (Lp.constL 2 P ℝ).comp
    (headInsert.comp (headExtract.comp (ProximalLangevin.lpExpectationCLM P))) +
      tailMask.compLpL 2 P

theorem averageCLM_coe (X : Lp (Cloud.State K dθ dz) 2 P) :
    averageCLM P X =ᵐ[P] fun ω =>
      headInsert (headExtract (ProximalLangevin.lpExpectationCLM P X)) + tailMask (X ω) := by
  filter_upwards [Lp.coeFn_add
    (Lp.const 2 P (headInsert (headExtract (ProximalLangevin.lpExpectationCLM P X))))
    (tailMask.compLpL 2 P X),
    Lp.coeFn_const (μ := P) (p := 2)
      (c := headInsert (J := Fin K × Fin dz) (headExtract (ProximalLangevin.lpExpectationCLM P X))),
    tailMask.coeFn_compLpL (p := 2) (μ := P) X] with ω ha hc ht
  change ((Lp.const 2 P (headInsert (J := Fin K × Fin dz)
    (headExtract (ProximalLangevin.lpExpectationCLM P X))) : Lp (Cloud.State K dθ dz) 2 P) +
      tailMask.compLpL 2 P X) ω = _
  rw [ha]
  simp only [Pi.add_apply, hc, ht, Function.const_apply]

theorem averageCLM_norm_le (X : Lp (Cloud.State K dθ dz) 2 P) :
    ‖averageCLM P X‖ ≤ 2 * ‖X‖ := by
  have hc : ‖Lp.const 2 P (headInsert (J := Fin K × Fin dz)
      (headExtract (ProximalLangevin.lpExpectationCLM P X)))‖ ≤ ‖X‖ := by
    have hc0 : ‖Lp.const 2 P (headInsert (J := Fin K × Fin dz)
        (headExtract (ProximalLangevin.lpExpectationCLM P X)))‖ ≤
        ‖headInsert (J := Fin K × Fin dz) (headExtract (ProximalLangevin.lpExpectationCLM P X))‖ := by
      simpa using Lp.norm_const_le 2 P (headInsert (J := Fin K × Fin dz)
        (headExtract (ProximalLangevin.lpExpectationCLM P X)))
    exact hc0.trans ((headInsert_norm _).le.trans
      ((headExtract_norm_le _).trans (ProximalLangevin.lpExpectationCLM_norm_le P X)))
  let C : Lp (Cloud.State K dθ dz) 2 P →L[ℝ] Lp (Cloud.State K dθ dz) 2 P :=
    (tailMask (d := dθ) (J := Fin K × Fin dz)).compLpL 2 P
  have hn : ‖C‖ ≤ 1 := (ContinuousLinearMap.norm_compLpL_le _).trans tailMask_opNorm_le
  have ht : ‖C X‖ ≤ ‖X‖ := (C.le_opNorm X).trans (mul_le_of_le_one_left (norm_nonneg _) hn)
  change ‖(Lp.const 2 P (headInsert (J := Fin K × Fin dz)
    (headExtract (ProximalLangevin.lpExpectationCLM P X))) : Lp (Cloud.State K dθ dz) 2 P) + C X‖ ≤ _
  exact (norm_add_le _ _).trans (by linarith)

theorem averageCLM_lipschitz : LipschitzWith 2
    (averageCLM (K := K) (dθ := dθ) (dz := dz) P) := by
  apply LipschitzWith.of_dist_le_mul
  intro X Y
  simpa only [dist_eq_norm, ← map_sub, NNReal.coe_ofNat] using averageCLM_norm_le P (X-Y)

/-- Actual McKean mean-field force: expected parameter score, pointwise latent
scores. The force is globally Lipschitz, proved from pointwise regularity. -/
def force {F : Cloud.State K dθ dz → Cloud.State K dθ dz} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L) (X : Lp (Cloud.State K dθ dz) 2 P) :=
  averageCLM P (liftedForce P hF X)

theorem force_lipschitz {F : Cloud.State K dθ dz → Cloud.State K dθ dz}
    {m : ℝ} {L : ℝ≥0} (hF : ForceRegularity F m L) :
    LipschitzWith (2*L) (force P hF) :=
  (averageCLM_lipschitz P).comp (LipschitzWith.of_dist_le_mul
    (fun X Y => by simpa only [dist_eq_norm] using (liftedForce_regular P hF).lipschitz X Y))

/-- Constructed global continuous L² mean-field solution. Existence is derived
by Picard from the original smooth drift and Brownian input. -/
theorem exists_meanField
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (initial : Lp (Cloud.State K dθ dz) 2 P)
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) :
    ∃ Y : ℝ → Lp (Cloud.State K dθ dz) 2 P, Continuous Y ∧ Y 0 = initial ∧
      ∀ t, 0 ≤ t → Y t - Y 0 =
        -(∫ r in 0..t, force P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (Y r)) +
          physicalNoise P B hB t := by
  have hc : Continuous (physicalNoise (dθ := dθ) P B hB) := by
    let C : Lp (Latent K dz) 2 P →L[ℝ] Lp (Cloud.State K dθ dz) 2 P := tailInsert.compLpL 2 P
    have hs : Continuous (fun _ : ℝ => (Real.sqrt (K : ℝ))⁻¹) := continuous_const
    exact hs.smul (C.continuous.comp (ULA.brownianLangevinNoise_continuous P B hB 0))
  exact exists_global_integral _ (2*L) (force_lipschitz P _) initial _ hc (physicalNoise_zero P B hB)

/-- The exact empirical force left by mean-field averaging is the average of
centered per-datum parameter scores. -/
theorem actual_centered_residual
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (X : Lp (Cloud.State K dθ dz) 2 P) :
    particleForce P hK U m L hdiff hsc hLip X -
      force P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) X =
    ProximalLangevin.lpCenterCLM P
      (MiniBatchVariance.average (scoreLp P U L hLip X)) := by
  let hF := Cloud.meanForce_regular hK U m L hdiff hsc hLip
  let Z := liftedForce P hF X
  have hres := lifted_meanForce_residual P hK U m L hdiff hsc hLip X
  change Z - frozenForce P hF X = _ at hres
  rw [← hres]
  change Z - averageCLM P Z = (Z - frozenForce P hF X) -
    Lp.const 2 P (ProximalLangevin.lpExpectationCLM P (Z - frozenForce P hF X))
  have he : ProximalLangevin.lpExpectationCLM P (Z - frozenForce P hF X) =
      headInsert (headExtract (ProximalLangevin.lpExpectationCLM P Z)) := by
    rw [map_sub]
    have ht := ProximalLangevin.lpExpectationCLM_compLp P tailMask Z
    change ProximalLangevin.lpExpectationCLM P (tailMask.compLpL 2 P Z) = _ at ht
    change ProximalLangevin.lpExpectationCLM P Z -
      ProximalLangevin.lpExpectationCLM P (tailMask.compLpL 2 P Z) = _
    rw [ht]
    ext j
    cases j <;> simp
  rw [he]
  change Z - (Lp.const 2 P (headInsert (J := Fin K × Fin dz)
    (headExtract (ProximalLangevin.lpExpectationCLM P Z))) + tailMask.compLpL 2 P Z) =
    (Z-tailMask.compLpL 2 P Z)-Lp.const 2 P (headInsert (J := Fin K × Fin dz)
      (headExtract (ProximalLangevin.lpExpectationCLM P Z)))
  abel

/-- Centering a finite sum is exactly the finite sum of centered variables. -/
theorem center_average {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (g : Fin K → Lp E 2 P) :
    ProximalLangevin.lpCenterCLM P (MiniBatchVariance.average g) =
      MiniBatchVariance.average (fun i => g i - constantL2 P (∫ ω, g i ω ∂P)) := by
  unfold MiniBatchVariance.average
  rw [map_smul, map_sum]
  rfl

/-- Independent heterogeneous mean-field scores give the explicit empirical
force scale from their primitive centered second moments. -/
theorem meanField_residual_bound
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (X : Lp (Cloud.State K dθ dz) 2 P) (V : ℝ)
    (hind : iIndepFun (fun i ω => scoreLp P U L hLip X i ω) P)
    (hvar : ∀ i, ‖scoreLp P U L hLip X i -
      constantL2 P (∫ ω, scoreLp P U L hLip X i ω ∂P)‖^2 ≤ V) :
    ‖particleForce P hK U m L hdiff hsc hLip X -
      force P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) X‖ ≤ Real.sqrt (V/K) := by
  rw [actual_centered_residual P hK U m L hdiff hsc hLip, center_average]
  let g := scoreLp P U L hLip X
  let z (i : Fin K) := g i - constantL2 P (∫ ω, g i ω ∂P)
  have horth (i j : Fin K) (hij : i ≠ j) : inner ℝ (z i) (z j) = 0 := by
    rw [L2.inner_def]
    have hmean (i : Fin K) : (∫ ω, (g i ω - ∫ w, g i w ∂P) ∂P) = 0 := by
      rw [integral_sub ((Lp.memLp (g i)).integrable (by norm_num)) (integrable_const _)]
      simp
    have he := ((hind.indepFun hij).comp
      (show Measurable (fun x : Cloud.State K dθ dz => x - ∫ ω, g i ω ∂P) by fun_prop)
      (show Measurable (fun x : Cloud.State K dθ dz => x - ∫ ω, g j ω ∂P) by fun_prop)).integral_bilin
        (((Lp.memLp (g i)).integrable (by norm_num)).sub (integrable_const _))
        (((Lp.memLp (g j)).integrable (by norm_num)).sub (integrable_const _)) (innerSL ℝ)
    change (∫ ω, inner ℝ (g i ω - ∫ w, g i w ∂P) (g j ω - ∫ w, g j w ∂P) ∂P) =
      inner ℝ (∫ ω, g i ω - ∫ w, g i w ∂P ∂P) (∫ ω, g j ω - ∫ w, g j w ∂P ∂P) at he
    rw [hmean i, hmean j, inner_zero_left] at he
    apply (integral_congr_ae ?_).trans he
    filter_upwards [Lp.coeFn_sub (g i) (constantL2 P (∫ ω, g i ω ∂P)),
      Lp.coeFn_sub (g j) (constantL2 P (∫ ω, g j ω ∂P)),
      constantL2_coe P (∫ ω, g i ω ∂P), constantL2_coe P (∫ ω, g j ω ∂P)] with ω hi hj hci hcj
    simp only [z, hi, hj, hci, hcj, Pi.sub_apply]
  exact MiniBatchVariance.mean_sum_of_orthogonal_le hK z V horth hvar

/-- Nonstationary spatial discretization: independent reference scores and
one-copy centered second moments imply the actual particle/mean-field error.
The bound is uniform at each fixed time; it does not put a time supremum inside
an expectation. The interacting particle solution is constructed by Picard. -/
theorem exists_spatial_comparison
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hm : 0 < m) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (Y : ℝ → Lp (Cloud.State K dθ dz) 2 P) (hY : Continuous Y)
    (B : ℝ → Lp (Cloud.State K dθ dz) 2 P) (hB : Continuous B) (hB0 : B 0=0)
    (hYe : ∀ t, 0 ≤ t → Y t-Y 0 =
      -(∫ r in 0..t, force P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (Y r))+B t)
    (V : ℝ) (_hV : 0 ≤ V)
    (hind : ∀ t, 0 ≤ t → iIndepFun (fun i ω => scoreLp P U L hLip (Y t) i ω) P)
    (hvar : ∀ t, 0 ≤ t → ∀ i, ‖scoreLp P U L hLip (Y t) i -
      constantL2 P (∫ ω, scoreLp P U L hLip (Y t) i ω ∂P)‖^2 ≤ V) :
    ∃ X : ℝ → Lp (Cloud.State K dθ dz) 2 P, Continuous X ∧ X 0=Y 0 ∧
      (∀ t, 0 ≤ t → X t-X 0 =
        -(∫ r in 0..t, particleForce P hK U m L hdiff hsc hLip (X r))+B t) ∧
      ∀ t, 0 ≤ t → ‖X t-Y t‖ ≤ Real.sqrt (V/K)/m*(1-Real.exp (-m*t)) := by
  let hF := Cloud.meanForce_regular hK U m L hdiff hsc hLip
  let F := particleForce P hK U m L hdiff hsc hLip
  have hlip : LipschitzWith L F := LipschitzWith.of_dist_le_mul
    (fun X Z => by simpa only [dist_eq_norm, F, particleForce] using (liftedForce_regular P hF).lipschitz X Z)
  obtain ⟨X,hX,hX0,hXe⟩ := exists_global_integral F L hlip (Y 0) B hB hB0
  refine ⟨X,hX,hX0,hXe,?_⟩
  intro t ht
  let f := fun r => F (Y r)-force P hF (Y r)
  have hf : Continuous f := (hlip.continuous.comp hY).sub ((force_lipschitz P hF).continuous.comp hY)
  have hforced (r : ℝ) (hr : r ∈ Icc 0 t) : Y r-Y 0 =
      -(∫ s in 0..r, F (Y s))+(∫ s in 0..r, f s)+B r := by
    have hiF := (hlip.continuous.comp hY).intervalIntegrable (μ := volume) 0 r
    have hiM := ((force_lipschitz P hF).continuous.comp hY).intervalIntegrable (μ := volume) 0 r
    rw [show (∫ s in 0..r, f s) = (∫ s in 0..r, F (Y s))-
      (∫ s in 0..r, force P hF (Y s)) from intervalIntegral.integral_sub hiF hiM]
    have he := hYe r hr.1
    change Y r-Y 0 = -(∫ s in 0..r, force P hF (Y s))+B r at he
    rw [he]
    abel
  have hbound := PBGSO.forced_additive_integral_contraction F L hlip
    (ContinuousLinearMap.id ℝ _) m (Real.sqrt (V/K)) hm (Real.sqrt_nonneg _)
    (fun x y => by simpa only [ContinuousLinearMap.id_apply, real_inner_comm, F, particleForce] using
      (liftedForce_regular P hF).monotone x y)
    X Y B f hX hY hf t (fun r hr => hXe r hr.1) hforced
    (fun r hr => by
      simpa only [ContinuousLinearMap.id_apply] using
        meanField_residual_bound P hK U m L hdiff hsc hLip (Y r) V (hind r hr.1) (hvar r hr.1))
    hX0 t ⟨ht,le_rfl⟩
  exact hbound

/-- Primitive actual state moments imply the force-moment input used by Euler
consistency. A force-radius or discretization-error bound is not assumed. -/
theorem force_radius_of_state_radius {F : Cloud.State K dθ dz → Cloud.State K dθ dz}
    {m : ℝ} {L : ℝ≥0} (hF : ForceRegularity F m L)
    (X : Lp (Cloud.State K dθ dz) 2 P) (R : ℝ) (hR : ‖X‖ ≤ R) :
    ‖liftedForce P hF X‖ ≤ ‖liftedForce P hF 0‖+(L : ℝ)*R := by
  have hl := (liftedForce_regular P hF).lipschitz X 0
  simp only [sub_zero] at hl
  calc
    _ = ‖(liftedForce P hF X-liftedForce P hF 0)+liftedForce P hF 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖liftedForce P hF X-liftedForce P hF 0‖+‖liftedForce P hF 0‖ := norm_add_le _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hR L.coe_nonneg]

/-- Actual nonstationary time discretization from a uniform second-moment
condition on the continuous particle states. The supplied initial state is
arbitrary, the Brownian increments match exactly, and the local defect is
proved from the original integral equation. -/
theorem temporal_comparison
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m h R : ℝ) (L : ℝ≥0) (hR : 0 ≤ R)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i))) (hs : StableStep m L h)
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (X : ℝ → Lp (Cloud.State K dθ dz) 2 P) (hX : Continuous X)
    (hXe : ∀ t, 0 ≤ t → X t-X 0 =
      -(∫ r in 0..t, particleForce P hK U m L hdiff hsc hLip (X r))+physicalNoise P B hB t)
    (hMoment : ∀ t, 0 ≤ t → ‖X t‖ ≤ R) (n : ℕ) :
    ‖eulerTrajectory (particleForce P hK U m L hdiff hsc hLip) h
      (fun k => physicalNoise P B hB ((k : ℝ)*h+h)-physicalNoise P B hB ((k : ℝ)*h)) (X 0) n-
      X ((n : ℝ)*h)‖ ≤
      (L : ℝ)/m * (h*(‖particleForce P hK U m L hdiff hsc hLip 0‖+(L : ℝ)*R)+
        (4/3 : ℝ)*Real.sqrt (2*(dz : ℝ))*Real.sqrt h) := by
  let hF := Cloud.meanForce_regular hK U m L hdiff hsc hLip
  let F := particleForce P hK U m L hdiff hsc hLip
  let G := ‖F 0‖+(L : ℝ)*R
  let y := fun n : ℕ => X ((n : ℝ)*h)
  let ξ : ℕ → Lp (Cloud.State K dθ dz) 2 P := fun n => physicalNoise P B hB ((n : ℝ)*h+h)-physicalNoise P B hB ((n : ℝ)*h)
  let Y : ℕ → ℝ → Lp (Cloud.State K dθ dz) 2 P := fun n t => X ((n : ℝ)*h+t)
  let W : ℕ → ℝ → Lp (Cloud.State K dθ dz) 2 P := fun n t => physicalNoise P B hB ((n : ℝ)*h+t)-physicalNoise P B hB ((n : ℝ)*h)
  have hlip : LipschitzWith L F := LipschitzWith.of_dist_le_mul
    (fun x z => by simpa only [dist_eq_norm, F, particleForce] using (liftedForce_regular P hF).lipschitz x z)
  have hr : IntegralReference F h G (physicalNoiseScale K dz) y ξ Y W :=
    { starts := by intro n; simp [Y,y]
      ends := by intro n; dsimp [Y,y]; congr 1; push_cast; ring
      noise_end := by intro n; rfl
      integrable := fun n => (hlip.continuous.comp
        (hX.comp (continuous_const.add continuous_id))).intervalIntegrable 0 h
      drift_radius := by
        intro n t ht
        exact force_radius_of_state_radius P hF _ R
          (hMoment _ (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hs.positive.le) ht.1))
      noise_growth := fun n t ht => physicalNoise_increment_bound P B hB _ _
        (mul_nonneg (Nat.cast_nonneg _) hs.positive.le) ht.1
      equation := by
        intro n t ht
        have he := PBGSO.MethodSegments.integral_shift X (fun r => -F (X r)) (physicalNoise P B hB)
          (hlip.continuous.comp hX).neg
          (fun r hr => by simpa only [intervalIntegral.integral_neg] using hXe r hr)
          ((n : ℝ)*h) t (mul_nonneg (Nat.cast_nonneg _) hs.positive.le) ht.1
        simpa only [Y, W, intervalIntegral.integral_neg, add_zero] using he }
  have he := integral_reference_error_bound F F m h 0 G (physicalNoiseScale K dz) L
    (liftedForce_regular P hF) hs le_rfl (by dsimp [G]; positivity)
    (by unfold physicalNoiseScale; positivity) y ξ Y W (X 0) hr (by intro k; simp) n
  simpa [y, ξ, G, physicalNoiseScale_eq hK] using he

theorem inner_headInsert (a : Parameter dθ) (x : Cloud.State K dθ dz) :
    inner ℝ (headInsert a) x = inner ℝ a (headExtract x) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fintype.sum_sum_type]

theorem inner_average_pointwise (a : Parameter dθ) (z x : Cloud.State K dθ dz) :
    inner ℝ (headInsert a + tailMask z) x =
      inner ℝ z x + inner ℝ (a-headExtract z) (headExtract x) := by
  rw [inner_add_left]
  change inner ℝ (headInsert a) x + inner ℝ (z-headInsert (headExtract z)) x = _
  rw [inner_sub_left, inner_headInsert, inner_headInsert, inner_sub_left]
  ring

/-- Averaging is invisible when paired against a deterministic parameter
block. This is the orthogonality identity that proves mean-field contraction. -/
theorem inner_average_eq (Z X : Lp (Cloud.State K dθ dz) 2 P) (a : Parameter dθ)
    (hX : parameterOutput P X = constantL2 P a) :
    inner ℝ (averageCLM P Z) X = inner ℝ Z X := by
  let c := headExtract (ProximalLangevin.lpExpectationCLM P Z)
  have hhead : headExtract.compLpL 2 P X = constantL2 P a := by
    exact hX
  have hiZ : Integrable (fun ω => headExtract (Z ω)) P :=
    headExtract.integrable_comp ((Lp.memLp Z).integrable (by norm_num))
  have hi : Integrable (fun ω => c-headExtract (Z ω)) P := (integrable_const _).sub hiZ
  have hcross : (∫ ω, inner ℝ (c-headExtract (Z ω)) a ∂P) = 0 := by
    simp_rw [real_inner_comm a]
    rw [integral_inner hi a, integral_sub (integrable_const _) hiZ]
    have he := headExtract.integral_comp_comm ((Lp.memLp Z).integrable (by norm_num))
    rw [he]
    simp [c, ProximalLangevin.lpExpectationCLM_apply]
  have hicross : Integrable (fun ω => inner ℝ (c-headExtract (Z ω)) a) P := by
    have hh := (innerSL ℝ a).integrable_comp hi
    change Integrable (fun ω => inner ℝ a (c-headExtract (Z ω))) P at hh
    apply hh.congr
    exact Filter.Eventually.of_forall (fun ω => (real_inner_comm a _).symm)
  rw [L2.inner_def, L2.inner_def]
  have he : (∫ ω, inner ℝ ((averageCLM P Z) ω) (X ω) ∂P) =
      ∫ ω, inner ℝ (Z ω) (X ω) + inner ℝ (c-headExtract (Z ω)) a ∂P := by
    apply integral_congr_ae
    filter_upwards [averageCLM_coe P Z, (@IPLA.parameterCLM K dθ dz).coeFn_compLpL X,
      constantL2_coe P a] with ω hav hp hc
    have hpa : headExtract (X ω) = a := by
      change (parameterOutput P X) ω = _ at hp
      rw [hX, hc] at hp
      exact hp.symm
    rw [hav, inner_average_pointwise, hpa]
  rw [he, integral_add (L2.integrable_inner Z X) hicross, hcross, add_zero]

/-- Strong monotonicity of the actual mean-field force on deterministic
parameter states is inherited from the original pair potentials. -/
theorem force_monotone_on_deterministic
    {F : Cloud.State K dθ dz → Cloud.State K dθ dz} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L) (X Y : Lp (Cloud.State K dθ dz) 2 P)
    (a b : Parameter dθ) (hX : parameterOutput P X = constantL2 P a)
    (hY : parameterOutput P Y = constantL2 P b) :
    m*‖X-Y‖^2 ≤ inner ℝ (force P hF X-force P hF Y) (X-Y) := by
  have hxy : parameterOutput P (X-Y) = constantL2 P (a-b) := by
    rw [map_sub,hX,hY]
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (constantL2 P a) (constantL2 P b),
      constantL2_coe P a,constantL2_coe P b,constantL2_coe P (a-b)] with ω hs ha hb hab
    simp only [hs,ha,hb,hab,Pi.sub_apply]
  change m*‖X-Y‖^2 ≤ inner ℝ
    (averageCLM P (liftedForce P hF X)-averageCLM P (liftedForce P hF Y)) (X-Y)
  rw [← map_sub,inner_average_eq P _ (X-Y) (a-b) hxy]
  exact (liftedForce_regular P hF).monotone X Y

/-- A mean-field force has a deterministic parameter block equal to the true
expected parameter force. -/
theorem force_parameter
    {F : Cloud.State K dθ dz → Cloud.State K dθ dz} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L) (X : Lp (Cloud.State K dθ dz) 2 P) :
    parameterOutput P (force P hF X) = constantL2 P
      (headExtract (ProximalLangevin.lpExpectationCLM P (liftedForce P hF X))) := by
  apply Lp.ext
  filter_upwards [(@IPLA.parameterCLM K dθ dz).coeFn_compLpL (force P hF X),
    averageCLM_coe P (liftedForce P hF X),
    constantL2_coe P (headExtract (ProximalLangevin.lpExpectationCLM P (liftedForce P hF X)))]
      with ω hp hav hc
  change (parameterOutput P (force P hF X)) ω = _ at hp
  rw [hp,hc]
  change IPLA.parameterCLM ((averageCLM P (liftedForce P hF X)) ω) = _
  rw [hav]
  ext j
  simp

theorem constantL2_eq_const {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (x : E) :
    constantL2 P x = Lp.const 2 P x := by
  apply Lp.ext
  exact (constantL2_coe P x).trans (Lp.coeFn_const (μ := P) (p := 2) (c := x)).symm

/-- Every actual mean-field solution has deterministic parameter trajectories;
this follows from the equation rather than being imposed on the solution. -/
theorem meanField_parameter_deterministic
    {F : Cloud.State K dθ dz → Cloud.State K dθ dz} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L)
    (Y : ℝ → Lp (Cloud.State K dθ dz) 2 P) (hY : Continuous Y)
    (B : ℝ → Lp (Cloud.State K dθ dz) 2 P)
    (hB : ∀ t, parameterOutput P (B t)=0)
    (hYe : ∀ t, 0 ≤ t → Y t-Y 0 = -(∫ r in 0..t, force P hF (Y r))+B t)
    (a₀ : Parameter dθ) (ha₀ : parameterOutput P (Y 0)=constantL2 P a₀)
    (t : ℝ) (ht : 0 ≤ t) :
    parameterOutput P (Y t)=constantL2 P
      (a₀-∫ r in 0..t, headExtract (ProximalLangevin.lpExpectationCLM P (liftedForce P hF (Y r)))) := by
  let A := fun r => headExtract (ProximalLangevin.lpExpectationCLM P (liftedForce P hF (Y r)))
  have hfLip : LipschitzWith L (liftedForce P hF) := LipschitzWith.of_dist_le_mul
    (fun X Z => by simpa only [dist_eq_norm] using (liftedForce_regular P hF).lipschitz X Z)
  have hA : Continuous A := headExtract.continuous.comp
    ((ProximalLangevin.lpExpectationCLM P).continuous.comp (hfLip.continuous.comp hY))
  let C := parameterOutput (K := K) (dθ := dθ) (dz := dz) P
  have hi := C.intervalIntegral_comp_comm (μ := volume)
    (((force_lipschitz P hF).continuous.comp hY).intervalIntegrable 0 t)
  simp only [Function.comp_apply] at hi
  have hiConst := (Lp.constL 2 P ℝ : Parameter dθ →L[ℝ] Lp (Parameter dθ) 2 P).intervalIntegral_comp_comm
    (μ := volume) (hA.intervalIntegrable 0 t)
  have he := congrArg C (hYe t ht)
  simp only [map_sub,map_add,map_neg,← hi,C,force_parameter,hB,add_zero,ha₀,
    constantL2_eq_const] at he
  have hi' : (∫ r in 0..t, Lp.const 2 P (A r)) = Lp.const 2 P (∫ r in 0..t, A r) := by
    simpa only [Lp.constL_apply] using hiConst
  change parameterOutput P (Y t)-Lp.const 2 P a₀ = -(∫ r in 0..t, Lp.const 2 P (A r)) at he
  rw [hi'] at he
  rw [constantL2_eq_const]
  change parameterOutput P (Y t) = Lp.const 2 P (a₀-∫ r in 0..t, A r)
  have hc : Lp.const 2 P (a₀-∫ r in 0..t, A r) =
      Lp.const 2 P a₀-Lp.const 2 P (∫ r in 0..t, A r) :=
    (Lp.constL 2 P ℝ).map_sub _ _
  rw [hc]
  calc
    _ = -Lp.const 2 P (∫ r in 0..t, A r)+Lp.const 2 P a₀ := sub_eq_iff_eq_add.mp he
    _ = _ := by abel

/-- Actual nonstationary mean-field solutions driven by the same Brownian
input contract exponentially. Joint strong convexity supplies the energy
inequality, and deterministic parameters are the only subspace condition. -/
theorem meanField_contraction
    {F : Cloud.State K dθ dz → Cloud.State K dθ dz} {m : ℝ} {L : ℝ≥0}
    (hF : ForceRegularity F m L)
    (Y Z B : ℝ → Lp (Cloud.State K dθ dz) 2 P) (hY : Continuous Y) (hZ : Continuous Z)
    (hYe : ∀ t, 0 ≤ t → Y t-Y 0 = -(∫ r in 0..t, force P hF (Y r))+B t)
    (hZe : ∀ t, 0 ≤ t → Z t-Z 0 = -(∫ r in 0..t, force P hF (Z r))+B t)
    (a b : ℝ → Parameter dθ)
    (hpa : ∀ t, 0 ≤ t → parameterOutput P (Y t)=constantL2 P (a t))
    (hpb : ∀ t, 0 ≤ t → parameterOutput P (Z t)=constantL2 P (b t))
    (t : ℝ) (ht : 0 ≤ t) :
    ‖Y t-Z t‖ ≤ Real.exp (-m*t)*‖Y 0-Z 0‖ := by
  let e := fun r => ‖Y r-Z r‖^2
  let e' := fun r => -2*inner ℝ (Y r-Z r) (force P hF (Y r)-force P hF (Z r))
  have hc : ContinuousOn e (Icc 0 t) := ((hY.sub hZ).norm.pow 2).continuousOn
  have hd : ∀ r ∈ Ico 0 t, HasDerivWithinAt e (e' r) (Ici r) r := by
    intro r hr
    have hdiff := KineticLangevin.integral_difference_hasDerivWithinAt
      (force P hF) (2*L) (force_lipschitz P hF) Y Z B hY hZ t
      (fun s hs => hYe s hs.1) (fun s hs => hZe s hs.1) r hr
    simpa only [e,e',inner_neg_right,mul_neg,neg_mul] using hdiff.norm_sq
  have hm : ∀ r ∈ Ico 0 t, e' r ≤ -2*m*e r := by
    intro r hr
    have h := force_monotone_on_deterministic P hF (Y r) (Z r) (a r) (b r) (hpa r hr.1) (hpb r hr.1)
    rw [real_inner_comm] at h
    dsimp [e,e']
    nlinarith
  have he := PBGSO.energy_decay hc hd hm t ⟨ht,le_rfl⟩
  have heexp : Real.exp (-m*t)^2=Real.exp (-2*m*t) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,heexp]
  simpa only [e,mul_comm] using he

/-- Equal state laws give equal actual posterior score means. -/
theorem liftMap_expectation_eq_of_law {E A : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    (f : E → A) {C : ℝ≥0} (hf : LipschitzWith C f)
    (X Y : Lp E 2 P) (hlaw : P.map X=P.map Y) :
    (∫ ω, PBGSO.liftMap P f hf X ω ∂P) = ∫ ω, PBGSO.liftMap P f hf Y ω ∂P := by
  rw [integral_congr_ae (PBGSO.liftMap_coe P f hf X),
    integral_congr_ae (PBGSO.liftMap_coe P f hf Y)]
  have hx := integral_map (Lp.aestronglyMeasurable X).aemeasurable hf.continuous.aestronglyMeasurable
  have hy := integral_map (Lp.aestronglyMeasurable Y).aemeasurable hf.continuous.aestronglyMeasurable
  rw [← hx,← hy,hlaw]

/-- At a zero total posterior score, the computed mean-field drift is exactly
the frozen posterior drift. Individual per-datum score means need not vanish. -/
theorem force_eq_frozen_of_score_mean_zero
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (X : Lp (Cloud.State K dθ dz) 2 P)
    (hopt : ∑ i, (∫ ω, scoreLp P U L hLip X i ω ∂P)=0) :
    force P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) X =
      frozenForce P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) X := by
  let hF := Cloud.meanForce_regular hK U m L hdiff hsc hLip
  let Z := liftedForce P hF X
  let E := ProximalLangevin.lpExpectationCLM (E := Cloud.State K dθ dz) P
  have heZ : E (Z-frozenForce P hF X) = headInsert (headExtract (E Z)) := by
    rw [map_sub]
    have ht := ProximalLangevin.lpExpectationCLM_compLp P tailMask Z
    change E (tailMask.compLpL 2 P Z)=tailMask (E Z) at ht
    change E Z-E (tailMask.compLpL 2 P Z)=_
    rw [ht]
    ext j
    cases j <;> simp
  have hzero : E (MiniBatchVariance.average (scoreLp P U L hLip X))=0 := by
    rw [MiniBatchVariance.average,map_smul,map_sum]
    change (1/(K : ℝ)) • (∑ i, ∫ ω, scoreLp P U L hLip X i ω ∂P)=0
    rw [hopt,smul_zero]
  have he := congrArg E (lifted_meanForce_residual P hK U m L hdiff hsc hLip X)
  change E (Z-frozenForce P hF X)=_ at he
  rw [heZ,hzero] at he
  have hp : headExtract (E Z)=0 := by
    have hh := congrArg (headExtract (d := dθ) (J := Fin K × Fin dz)) he
    ext j
    have hj := congrArg (fun x : Parameter dθ => x j) hh
    simpa using hj
  change Lp.const 2 P (headInsert (J := Fin K × Fin dz) (headExtract (E Z)))+
      tailMask.compLpL 2 P Z = tailMask.compLpL 2 P Z
  rw [hp,map_zero]
  simp

/-- A constructed stationary posterior reference is also an actual mean-field
solution. Posterior optimality cancels the expected optimizer drift. -/
theorem frozen_is_meanField
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (S : FrozenPosteriorSolution P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) B hB)
    (hopt : ∑ i, (∫ ω, scoreLp P U L hLip (S.path 0) i ω ∂P)=0) :
    ∀ t, 0 ≤ t → S.path t-S.path 0 =
      -(∫ r in 0..t, force P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (S.path r))+
        physicalNoise P B hB t := by
  intro t ht
  have hp (r : ℝ) (hr : 0 ≤ r) :
      force P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (S.path r) =
        frozenForce P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (S.path r) := by
    apply force_eq_frozen_of_score_mean_zero P hK U m L hdiff hsc hLip
    have hs (i : Fin K) : (∫ ω, scoreLp P U L hLip (S.path r) i ω ∂P) =
        ∫ ω, scoreLp P U L hLip (S.path 0) i ω ∂P :=
      liftMap_expectation_eq_of_law P (parameterScore U i) (parameterScore_lipschitz U L hLip i)
        _ _ (S.stationary_law r hr)
    simp_rw [hs]
    exact hopt
  rw [show (∫ r in 0..t, force P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (S.path r)) =
    ∫ r in 0..t, frozenForce P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (S.path r) by
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le ht] at hr
      exact hp r hr.1]
  exact S.equation t ht

/-- The actual mean-field optimizer converges to the posterior evidence
optimizer. The initial coupling and parameter are arbitrary; no convergence
estimate is assumed. -/
theorem meanField_optimizer_convergence
    (hK : 0 < K) (U : Fin K → Cloud.Joint dθ dz → ℝ)
    (m : ℝ) (L : ℝ≥0) (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn Set.univ m (U i))
    (hLip : ∀ i, LipschitzWith L (gradient (U i)))
    (B : (Fin K × Fin dz) → ℝ≥0 → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (S : FrozenPosteriorSolution P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) B hB)
    (hopt : ∑ i, (∫ ω, scoreLp P U L hLip (S.path 0) i ω ∂P)=0)
    (astar : Parameter dθ) (hstar : parameterOutput P (S.path 0)=constantL2 P astar)
    (Y : ℝ → Lp (Cloud.State K dθ dz) 2 P) (hY : Continuous Y)
    (hYe : ∀ t, 0 ≤ t → Y t-Y 0 =
      -(∫ r in 0..t, force P (Cloud.meanForce_regular hK U m L hdiff hsc hLip) (Y r))+
        physicalNoise P B hB t)
    (a₀ : Parameter dθ) (ha₀ : parameterOutput P (Y 0)=constantL2 P a₀)
    (t : ℝ) (ht : 0 ≤ t) :
    ‖parameterOutput P (Y t)-constantL2 P astar‖ ≤ Real.exp (-m*t)*‖Y 0-S.path 0‖ := by
  let hF := Cloud.meanForce_regular hK U m L hdiff hsc hLip
  let a := fun t => a₀-∫ r in 0..t, headExtract (ProximalLangevin.lpExpectationCLM P (liftedForce P hF (Y r)))
  have hpa := meanField_parameter_deterministic P hF Y hY (physicalNoise P B hB)
    (parameterOutput_noise_zero P B hB) hYe a₀ ha₀
  have hpb (r : ℝ) (hr : 0 ≤ r) : parameterOutput P (S.path r)=constantL2 P astar :=
    (S.parameter_constant P r hr).trans hstar
  have he := meanField_contraction P hF Y S.path (physicalNoise P B hB) hY S.continuous
    hYe (frozen_is_meanField P hK U m L hdiff hsc hLip B hB S hopt) a (fun _ => astar) hpa hpb t ht
  rw [← hpb t ht,← map_sub]
  exact ((parameterOutput P).le_opNorm _).trans
    ((mul_le_of_le_one_left (norm_nonneg _) (parameterOutput_norm_le P)).trans he)

end LatentDiffusion.RegularMeanField
