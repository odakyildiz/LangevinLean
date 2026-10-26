import PBGSO.ContinuousVolume
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Differentiability of flow constructions

This file derives joint C¹ dependence of actual globally defined ODE
trajectories from a C¹ globally Lipschitz primitive vector field. Neither
continuity in initial data, differentiability of the flow, the semigroup
identity, nor a variational equation is an input.

The proof constructs the actual Picard operator on continuous paths,
proves C¹ superposition using compact uniform continuity of the primitive
derivative, and applies the Banach implicit function theorem. Scaled time
and the derived semigroup identity extend the short-time construction to
all times. Localization of a merely C¹ source field is a separate bridge.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Filter
open scoped Topology NNReal
namespace PBGSO.FlowDifferentiability

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]

/-- Uniform contraction and continuity of the primitive map imply
continuity of its actual parameterized fixed points. -/
theorem fixedPoint_continuousAt (F : A × B → B) (ψ : A → B)
    (c : ℝ≥0) (hc : c < 1) (hLip : ∀ a, LipschitzWith c (fun b => F (a, b)))
    (hfix : ∀ a, F (a, ψ a) = ψ a) (a₀ : A)
    (hF : ContinuousAt F (a₀, ψ a₀)) : ContinuousAt ψ a₀ := by
  have hcontract (a : A) : ContractingWith c (fun b => F (a, b)) := ⟨hc, hLip a⟩
  have hbound (a : A) : dist (ψ a) (ψ a₀) ≤
      dist (ψ a₀) (F (a, ψ a₀)) / (1 - (c : ℝ)) := by
    simpa only [dist_comm] using
      (hcontract a).dist_le_of_fixedPoint (ψ a₀) (hfix a)
  have hlim : Tendsto (fun a => dist (ψ a₀) (F (a, ψ a₀)) / (1 - (c : ℝ)))
      (𝓝 a₀) (𝓝 0) := by
    have hFa : ContinuousAt (fun a : A => F (a, ψ a₀)) a₀ :=
      ContinuousAt.comp' (f := fun a : A => (a, ψ a₀)) hF
        (continuousAt_id.prodMk continuousAt_const)
    have h := ((continuousAt_const (y := ψ a₀)).dist hFa).div_const (1 - (c : ℝ))
    simpa only [hfix a₀, dist_self, zero_div] using h
  have hd := squeeze_zero (fun a => dist_nonneg : ∀ a, 0 ≤ dist (ψ a) (ψ a₀)) hbound hlim
  exact tendsto_iff_dist_tendsto_zero.mpr hd

/-- Only a neighborhood of the parameter needs a common contraction
constant. This is needed for time-scaled Picard maps. -/
theorem fixedPoint_continuousAt_of_eventually (F : A × B → B) (ψ : A → B)
    (a₀ : A) (c : ℝ≥0) (hc : c < 1)
    (hLip : ∀ᶠ a in 𝓝 a₀, LipschitzWith c (fun b => F (a, b)))
    (hfix : ∀ a, F (a, ψ a) = ψ a)
    (hF : ContinuousAt F (a₀, ψ a₀)) : ContinuousAt ψ a₀ := by
  have hbound : ∀ᶠ a in 𝓝 a₀, dist (ψ a) (ψ a₀) ≤
      dist (ψ a₀) (F (a, ψ a₀)) / (1 - (c : ℝ)) := by
    filter_upwards [hLip] with a ha
    simpa only [dist_comm] using
      (show ContractingWith c (fun b => F (a, b)) from ⟨hc, ha⟩).dist_le_of_fixedPoint
        (ψ a₀) (hfix a)
  have hFa : ContinuousAt (fun a : A => F (a, ψ a₀)) a₀ :=
    ContinuousAt.comp' (f := fun a : A => (a, ψ a₀)) hF
      (continuousAt_id.prodMk continuousAt_const)
  have hlim : Tendsto (fun a => dist (ψ a₀) (F (a, ψ a₀)) / (1 - (c : ℝ)))
      (𝓝 a₀) (𝓝 0) := by
    simpa only [hfix a₀, dist_self, zero_div] using
      ((continuousAt_const (y := ψ a₀)).dist hFa).div_const (1 - (c : ℝ))
  exact tendsto_iff_dist_tendsto_zero.mpr
    (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hbound hlim)

/-- A bounded linear map of norm less than one has invertible `I-L`.
This discharges the implicit theorem's inverse premise from contraction. -/
theorem one_sub_isInvertible (L : B →L[ℝ] B) (hL : ‖L‖ < 1) :
    (ContinuousLinearMap.id ℝ B - L).IsInvertible := by
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hL
  refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
  change (u : B →L[ℝ] B) = ContinuousLinearMap.id ℝ B - L
  exact hu

/-- Actual fixed points of a jointly strictly differentiable contraction
are strictly differentiable in their parameter. The derivative formula and
invertibility are derived from primitive derivatives and contraction. -/
theorem fixedPoint_hasStrictFDerivAt (F : A × B → B) (ψ : A → B)
    (c : ℝ≥0) (hc : c < 1) (hLip : ∀ a, LipschitzWith c (fun b => F (a, b)))
    (hfix : ∀ a, F (a, ψ a) = ψ a) (a₀ : A)
    (D : (A × B) →L[ℝ] B) (hF : HasStrictFDerivAt F D (a₀, ψ a₀)) :
    HasStrictFDerivAt ψ
      (((ContinuousLinearMap.id ℝ B - D.comp (ContinuousLinearMap.inr ℝ A B)).inverse).comp
        (D.comp (ContinuousLinearMap.inl ℝ A B))) a₀ := by
  let R : A × B → B := fun p => p.2 - F p
  let DR : (A × B) →L[ℝ] B := ContinuousLinearMap.snd ℝ A B - D
  have hR : HasStrictFDerivAt R DR (a₀, ψ a₀) := hasStrictFDerivAt_snd.sub hF
  have hpartial : HasFDerivAt (fun b => F (a₀, b))
      (D.comp (ContinuousLinearMap.inr ℝ A B)) (ψ a₀) :=
    hF.hasFDerivAt.comp (ψ a₀)
      ((hasFDerivAt_const a₀ (ψ a₀)).prodMk (hasFDerivAt_id (ψ a₀)))
  have hnorm := hpartial.le_of_lipschitz (hLip a₀)
  have hbound : ‖D.comp (ContinuousLinearMap.inr ℝ A B)‖ < 1 :=
    hnorm.trans_lt (show (c : ℝ) < 1 by exact_mod_cast hc)
  have hDR : DR.comp (ContinuousLinearMap.inr ℝ A B) =
      ContinuousLinearMap.id ℝ B - D.comp (ContinuousLinearMap.inr ℝ A B) := by
    ext b
    rfl
  have hinv : (DR.comp (ContinuousLinearMap.inr ℝ A B)).IsInvertible := by
    rw [hDR]
    exact one_sub_isInvertible _ hbound
  have hImplicit := hR.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  have hψ := fixedPoint_continuousAt F ψ c hc hLip hfix a₀ hF.continuousAt
  have hgraph : Tendsto (fun a => (a, ψ a)) (𝓝 a₀) (𝓝 (a₀, ψ a₀)) :=
    continuousAt_id.prodMk hψ
  have hevent := hgraph.eventually (hR.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv)
  have hEq : hR.implicitFunctionOfProdDomain hinv =ᶠ[𝓝 a₀] ψ := by
    filter_upwards [hevent] with a ha
    exact ha.mp (by simp only [R, hfix, sub_self])
  have hfinal := hImplicit.congr_of_eventuallyEq hEq
  convert hfinal using 1
  rw [hDR]
  ext a
  simp only [DR, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_snd', zero_sub,
    neg_apply, map_neg, neg_neg]

/-- C¹ regularity of actual parameterized fixed points follows from the
primitive C¹ contraction map; smoothness of the fixed-point selector is
proved by the implicit theorem rather than assumed. -/
theorem fixedPoint_contDiffAt (F : A × B → B) (ψ : A → B)
    (c : ℝ≥0) (hc : c < 1) (hLip : ∀ a, LipschitzWith c (fun b => F (a, b)))
    (hfix : ∀ a, F (a, ψ a) = ψ a) (a₀ : A)
    (hF : ContDiffAt ℝ 1 F (a₀, ψ a₀)) : ContDiffAt ℝ 1 ψ a₀ := by
  let R : A × B → B := fun p => p.2 - F p
  have hR : ContDiffAt ℝ 1 R (a₀, ψ a₀) := contDiffAt_snd.sub hF
  have hRder := hR.hasStrictFDerivAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hFder := hF.hasStrictFDerivAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hpartial : HasFDerivAt (fun b => F (a₀, b))
      ((fderiv ℝ F (a₀, ψ a₀)).comp (ContinuousLinearMap.inr ℝ A B)) (ψ a₀) :=
    hFder.hasFDerivAt.comp (ψ a₀)
      ((hasFDerivAt_const a₀ (ψ a₀)).prodMk (hasFDerivAt_id (ψ a₀)))
  have hnorm := hpartial.le_of_lipschitz (hLip a₀)
  have hDR : (fderiv ℝ R (a₀, ψ a₀)).comp (ContinuousLinearMap.inr ℝ A B) =
      ContinuousLinearMap.id ℝ B - (fderiv ℝ F (a₀, ψ a₀)).comp
        (ContinuousLinearMap.inr ℝ A B) := by
    rw [show fderiv ℝ R (a₀, ψ a₀) = ContinuousLinearMap.snd ℝ A B -
      fderiv ℝ F (a₀, ψ a₀) from (hasFDerivAt_snd.sub hFder.hasFDerivAt).fderiv]
    ext b
    rfl
  have hinv : ((fderiv ℝ R (a₀, ψ a₀)).comp
      (ContinuousLinearMap.inr ℝ A B)).IsInvertible := by
    rw [hDR]
    exact one_sub_isInvertible _ (hnorm.trans_lt (by exact_mod_cast hc))
  have hψ := fixedPoint_continuousAt F ψ c hc hLip hfix a₀ hF.continuousAt
  have hevent := (continuousAt_id.prodMk hψ).eventually
    (hR.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv)
  have hEq : hR.implicitFunction (by norm_num) hinv =ᶠ[𝓝 a₀] ψ := by
    filter_upwards [hevent] with a ha
    exact ha.mp (by simp only [R, id_eq, hfix, sub_self])
  exact (hR.contDiffAt_implicitFunction (by norm_num) hinv).congr_of_eventuallyEq hEq.symm

/-- Local uniform contraction gives C¹ dependence of fixed points. -/
theorem fixedPoint_contDiffAt_of_eventually (F : A × B → B) (ψ : A → B)
    (a₀ : A) (c : ℝ≥0) (hc : c < 1)
    (hLip : ∀ᶠ a in 𝓝 a₀, LipschitzWith c (fun b => F (a, b)))
    (hfix : ∀ a, F (a, ψ a) = ψ a)
    (hF : ContDiffAt ℝ 1 F (a₀, ψ a₀)) : ContDiffAt ℝ 1 ψ a₀ := by
  let R : A × B → B := fun p => p.2 - F p
  have hR : ContDiffAt ℝ 1 R (a₀, ψ a₀) := contDiffAt_snd.sub hF
  have hRder := hR.hasStrictFDerivAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hFder := hF.hasStrictFDerivAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hpartial : HasFDerivAt (fun b => F (a₀, b))
      ((fderiv ℝ F (a₀, ψ a₀)).comp (ContinuousLinearMap.inr ℝ A B)) (ψ a₀) :=
    hFder.hasFDerivAt.comp (ψ a₀)
      ((hasFDerivAt_const a₀ (ψ a₀)).prodMk (hasFDerivAt_id (ψ a₀)))
  have hnorm := hpartial.le_of_lipschitz (hLip.self_of_nhds)
  have hDR : (fderiv ℝ R (a₀, ψ a₀)).comp (ContinuousLinearMap.inr ℝ A B) =
      ContinuousLinearMap.id ℝ B - (fderiv ℝ F (a₀, ψ a₀)).comp
        (ContinuousLinearMap.inr ℝ A B) := by
    rw [show fderiv ℝ R (a₀, ψ a₀) = ContinuousLinearMap.snd ℝ A B -
      fderiv ℝ F (a₀, ψ a₀) from (hasFDerivAt_snd.sub hFder.hasFDerivAt).fderiv]
    ext b
    rfl
  have hinv : ((fderiv ℝ R (a₀, ψ a₀)).comp
      (ContinuousLinearMap.inr ℝ A B)).IsInvertible := by
    rw [hDR]
    exact one_sub_isInvertible _ (hnorm.trans_lt (by exact_mod_cast hc))
  have hψ := fixedPoint_continuousAt_of_eventually F ψ a₀ c hc hLip hfix hF.continuousAt
  have hevent := (continuousAt_id.prodMk hψ).eventually
    (hR.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv)
  have hEq : hR.implicitFunction (by norm_num) hinv =ᶠ[𝓝 a₀] ψ := by
    filter_upwards [hevent] with a ha
    exact ha.mp (by simp only [R, id_eq, hfix, sub_self])
  exact (hR.contDiffAt_implicitFunction (by norm_num) hinv).congr_of_eventuallyEq hEq.symm

section Curves
variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Pointwise application of a continuous operator field is a bounded
linear map on the actual continuous-curve Banach space. -/
def curveOperator (D : C(K, E →L[ℝ] E)) : C(K, E) →L[ℝ] C(K, E) :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun k => D k (v k), D.continuous.clm_apply v.continuous⟩
      map_add' := fun v w => by ext k; exact (D k).map_add _ _
      map_smul' := fun r v => by ext k; exact (D k).map_smul r _ }
    ‖D‖ (by
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg D) (norm_nonneg v))).mpr
      intro k
      exact ((D k).le_opNorm (v k)).trans
        (mul_le_mul (D.norm_coe_le_norm k) (v.norm_coe_le_norm k) (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem curveOperator_apply (D : C(K, E →L[ℝ] E)) (v : C(K, E)) (k : K) :
    curveOperator D v k = D k (v k) := rfl

/-- The actual superposition map on continuous paths. -/
def superposition (f : E → E) (hf : Continuous f) (v : C(K, E)) : C(K, E) :=
  ⟨fun k => f (v k), hf.comp v.continuous⟩

/-- The actual derivative field along a continuous path. -/
def derivativeAlong (f : E → E) (hf : ContDiff ℝ 1 f) (u : C(K, E)) : C(K, E →L[ℝ] E) :=
  ⟨fun k => fderiv ℝ f (u k), (hf.continuous_fderiv (by norm_num)).comp u.continuous⟩

/-- A C¹ finite-dimensional force induces a strictly differentiable map
on actual continuous paths. Compactness supplies the uniform derivative
remainder; no stronger Lipschitz assumption on the derivative is used. -/
theorem superposition_hasStrictFDerivAt [ProperSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f) (u : C(K, E)) :
    HasStrictFDerivAt (superposition f hf.continuous)
      (curveOperator (derivativeAlong f hf u)) u := by
  apply HasStrictFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  let R := ‖u‖ + 1
  have hUC := (isCompact_closedBall (0 : E) R).uniformContinuousOn_of_continuous
    (hf.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨δ₀, hδ₀, hmod⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  let δ := min 1 (δ₀ / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (half_pos hδ₀)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ₀' : δ < δ₀ := (min_le_right _ _).trans_lt (half_lt_self hδ₀)
  have hu (k : K) : u k ∈ Metric.closedBall (0 : E) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (u.norm_coe_le_norm k).trans (show ‖u‖ ≤ R by dsimp [R]; linarith)
  filter_upwards [Metric.ball_mem_nhds (u, u) hδ] with p hp
  have hv : ‖p.1 - u‖ < δ := by
    simpa only [dist_eq_norm] using (show dist p.1 u ≤ dist p (u, u) by rw [Prod.dist_eq]; exact le_max_left _ _).trans_lt hp
  have hw : ‖p.2 - u‖ < δ := by
    simpa only [dist_eq_norm] using (show dist p.2 u ≤ dist p (u, u) by rw [Prod.dist_eq]; exact le_max_right _ _).trans_lt hp
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg (p.1 - p.2)))).mpr
  intro k
  let g : E → E := fun z => f z - (fderiv ℝ f (u k)) z
  have hd (z : E) : HasFDerivAt g (fderiv ℝ f z - fderiv ℝ f (u k)) z :=
    ((hf.differentiable (by norm_num)) z).hasFDerivAt.sub (fderiv ℝ f (u k)).hasFDerivAt
  have hb (z : E) (hz : z ∈ Metric.closedBall (u k) δ) :
      ‖fderiv ℝ f z - fderiv ℝ f (u k)‖ ≤ ε := by
    have hz' : dist z (u k) ≤ δ := hz
    have hzR : z ∈ Metric.closedBall (0 : E) R := by
      apply (dist_triangle z (u k) 0).trans
      simpa only [dist_zero_right] using
        (add_le_add hz' (u.norm_coe_le_norm k)).trans (by dsimp [R]; linarith)
    simpa only [dist_eq_norm] using (hmod z hzR (u k) (hu k) (hz'.trans_lt hδ₀')).le
  have hvk : p.1 k ∈ Metric.closedBall (u k) δ := by
    change dist (p.1 k) (u k) ≤ δ
    simpa only [dist_eq_norm, ContinuousMap.sub_apply] using
      ((p.1 - u).norm_coe_le_norm k).trans hv.le
  have hwk : p.2 k ∈ Metric.closedBall (u k) δ := by
    change dist (p.2 k) (u k) ≤ δ
    simpa only [dist_eq_norm, ContinuousMap.sub_apply] using
      ((p.2 - u).norm_coe_le_norm k).trans hw.le
  have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hd z).differentiableAt)
    (fun z hz => by simpa only [(hd z).fderiv] using hb z hz)
    (convex_closedBall (u k) δ) hwk hvk
  change ‖f (p.1 k) - f (p.2 k) - (fderiv ℝ f (u k)) ((p.1 - p.2) k)‖ ≤ _
  have heq : f (p.1 k) - f (p.2 k) - (fderiv ℝ f (u k)) ((p.1 - p.2) k) =
      g (p.1 k) - g (p.2 k) := by
    dsimp [g]
    rw [map_sub]
    abel
  rw [heq]
  exact hmean.trans (mul_le_mul_of_nonneg_left ((p.1 - p.2).norm_coe_le_norm k) hε.le)

/-- Operator fields act continuously and linearly on path space. -/
def curveOperatorMap : C(K, E →L[ℝ] E) →L[ℝ] (C(K, E) →L[ℝ] C(K, E)) :=
  LinearMap.mkContinuous
    { toFun := curveOperator (K := K) (E := E)
      map_add' := fun D D' => by ext v k; rfl
      map_smul' := fun r D => by ext v k; rfl }
    1 (by
      intro D
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg D) (norm_nonneg v))).mpr
      intro k
      exact ((D k).le_opNorm (v k)).trans
        (mul_le_mul (D.norm_coe_le_norm k) (v.norm_coe_le_norm k)
          (norm_nonneg _) (norm_nonneg _)))

theorem superposition_contDiff [ProperSpace E] (f : E → E) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (superposition (K := K) f hf.continuous) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun u => curveOperator (derivativeAlong f hf u), ?_,
    fun u => (superposition_hasStrictFDerivAt f hf u).hasFDerivAt⟩
  exact (curveOperatorMap (K := K) (E := E)).continuous.comp
    (ContinuousMap.continuous_postcomp ⟨fderiv ℝ f, hf.continuous_fderiv (by norm_num)⟩)

end Curves

section TimeCurves
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
open Set MeasureTheory

abbrev Time (T : ℝ) := Icc (-T) T

def extendCurve (T : ℝ) (hT : 0 ≤ T) (v : C(Time T, E)) : ℝ → E :=
  fun t => v (projIcc (-T) T (by linarith) t)

theorem extendCurve_continuous (T : ℝ) (hT : 0 ≤ T) (v : C(Time T, E)) :
    Continuous (extendCurve T hT v) := v.continuous.comp continuous_projIcc

@[simp] theorem extendCurve_val (T : ℝ) (hT : 0 ≤ T) (v : C(Time T, E)) (t : Time T) :
    extendCurve T hT v t = v t := by simp only [extendCurve, projIcc_val]

/-- The genuine Volterra integration operator on continuous paths. -/
def volterra (T : ℝ) (hT : 0 ≤ T) : C(Time T, E) →L[ℝ] C(Time T, E) :=
  LinearMap.mkContinuous
    { toFun := fun v =>
        ⟨fun t => ∫ s in (0 : ℝ)..(t : ℝ), extendCurve T hT v s,
          (intervalIntegral.differentiable_integral_of_continuous
            (extendCurve_continuous T hT v)).continuous.comp continuous_subtype_val⟩
      map_add' := fun v w => by
        ext t
        exact intervalIntegral.integral_add
          ((extendCurve_continuous T hT v).intervalIntegrable _ _)
          ((extendCurve_continuous T hT w).intervalIntegrable _ _)
      map_smul' := fun r v => by
        ext t
        exact intervalIntegral.integral_smul r (extendCurve T hT v) }
    T (by
      intro v
      apply (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg v))).mpr
      intro t
      exact (intervalIntegral.norm_integral_le_of_norm_le_const
        (fun s _ => v.norm_coe_le_norm _)).trans (by
          rw [sub_zero, mul_comm T]
          exact mul_le_mul_of_nonneg_left (abs_le.mpr t.property) (norm_nonneg v)))

@[simp] theorem volterra_apply (T : ℝ) (hT : 0 ≤ T) (v : C(Time T, E)) (t : Time T) :
    volterra T hT v t = ∫ s in (0 : ℝ)..(t : ℝ), extendCurve T hT v s := rfl

theorem volterra_norm_le (T : ℝ) (hT : 0 ≤ T) (v : C(Time T, E)) :
    ‖volterra T hT v‖ ≤ T * ‖v‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hT (norm_nonneg v))).mpr
  intro t
  exact (intervalIntegral.norm_integral_le_of_norm_le_const
    (fun s _ => v.norm_coe_le_norm _)).trans (by
      rw [sub_zero, mul_comm T]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr t.property) (norm_nonneg v))

/-- Picard's primitive map on the actual continuous-curve Banach space. -/
def picardMap (T : ℝ) (hT : 0 ≤ T) (f : E → E) (hf : Continuous f)
    (p : E × C(Time T, E)) : C(Time T, E) :=
  ContinuousMap.const (Time T) p.1 + volterra T hT (superposition f hf p.2)

theorem superposition_lipschitz (K : Type*) [TopologicalSpace K] [CompactSpace K]
    (f : E → E) (hf : Continuous f) (L : ℝ≥0) (hLip : LipschitzWith L f) :
    LipschitzWith L (superposition (K := K) f hf) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [dist_eq_norm, dist_eq_norm]
  apply (ContinuousMap.norm_le _ (mul_nonneg L.coe_nonneg (norm_nonneg _))).mpr
  intro k
  exact (hLip.norm_sub_le (v k) (w k)).trans
    (mul_le_mul_of_nonneg_left ((v - w).norm_coe_le_norm k) L.coe_nonneg)

theorem picardMap_lipschitz (T : ℝ) (hT : 0 ≤ T) (f : E → E) (hf : Continuous f)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (x : E) :
    LipschitzWith (⟨T, hT⟩ * L) (fun v => picardMap T hT f hf (x, v)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [picardMap, dist_eq_norm, add_sub_add_left_eq_sub, ← map_sub]
  exact (volterra_norm_le T hT _).trans (by
    simp only [NNReal.coe_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((superposition_lipschitz (Time T) f hf L hLip).norm_sub_le v w) hT)

theorem picardMap_contDiff [ProperSpace E] (T : ℝ) (hT : 0 ≤ T)
    (f : E → E) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (picardMap T hT f hf.continuous) :=
  ((ContinuousLinearMap.const ℝ (Time T) : E →L[ℝ] C(Time T, E)).contDiff.comp contDiff_fst).add
    ((volterra T hT).contDiff.comp ((superposition_contDiff f hf).comp contDiff_snd))

/-- Restrict any actual globally defined individual ODE trajectories to
continuous paths. No continuity in initial data is assumed here. -/
def flowCurve (T : ℝ) (Φ : ℝ × E → E) (f : E → E)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (x : E) : C(Time T, E) :=
  ⟨fun t => Φ (t, x),
    (continuous_iff_continuousAt.mpr (fun t => (hODE t x).continuousAt)).comp
      continuous_subtype_val⟩

@[simp] theorem flowCurve_apply (T : ℝ) (Φ : ℝ × E → E) (f : E → E) (hODE) (x : E)
    (t : Time T) : flowCurve T Φ f hODE x t = Φ (t, x) := rfl

theorem flowCurve_fixedPoint (T : ℝ) (hT : 0 ≤ T) (Φ : ℝ × E → E)
    (f : E → E) (hf : Continuous f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (x : E) :
    picardMap T hT f hf (x, flowCurve T Φ f hODE x) = flowCurve T Φ f hODE x := by
  ext t
  change x + (∫ s in (0 : ℝ)..(t : ℝ),
    extendCurve T hT (superposition f hf (flowCurve T Φ f hODE x)) s) = Φ (t, x)
  have hcon : Continuous (fun s => f (Φ (s, x))) := hf.comp
    (continuous_iff_continuousAt.mpr (fun s => (hODE s x).continuousAt))
  have heq : (∫ s in (0 : ℝ)..(t : ℝ),
      extendCurve T hT (superposition f hf (flowCurve T Φ f hODE x)) s) =
      ∫ s in (0 : ℝ)..(t : ℝ), f (Φ (s, x)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsT : s ∈ Time T := by
      apply Set.uIcc_subset_Icc (by constructor <;> linarith) t.property hs
    simp only [extendCurve, projIcc_of_mem _ hsT, superposition, ContinuousMap.coe_mk,
      flowCurve]
  rw [heq, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hODE s x) (hcon.intervalIntegrable _ _), hinit]
  abel

/-- Genuine C¹ initial-data dependence of the actual ODE trajectories on
a short compact time interval, derived from C¹ of the primitive force and
its global Lipschitz bound. In particular neither a differentiable flow nor
a variational equation is a premise. -/
theorem flowCurve_contDiff_short [ProperSpace E]
    (T : ℝ) (hT : 0 ≤ T) (Φ : ℝ × E → E) (f : E → E) (hf : ContDiff ℝ 1 f)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (hshort : T * (L : ℝ) < 1)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) :
    ContDiff ℝ 1 (flowCurve T Φ f hODE) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  exact fixedPoint_contDiffAt _ _ (⟨T, hT⟩ * L) (by exact_mod_cast hshort)
    (picardMap_lipschitz T hT f hf.continuous L hLip)
    (flowCurve_fixedPoint T hT Φ f hf.continuous hODE hinit) x
    (picardMap_contDiff T hT f hf).contDiffAt

/-- The time scale is an ordinary parameter. The path domain stays fixed,
so evaluation is a fixed continuous linear map. -/
def scaledPicardMap (f : E → E) (hf : Continuous f)
    (p : (ℝ × E) × C(Time 1, E)) : C(Time 1, E) :=
  ContinuousMap.const (Time 1) p.1.2 + p.1.1 • volterra 1 (by norm_num)
    (superposition f hf p.2)

theorem scaledPicardMap_contDiff [ProperSpace E] (f : E → E) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (scaledPicardMap f hf.continuous) :=
  ((ContinuousLinearMap.const ℝ (Time 1) : E →L[ℝ] C(Time 1, E)).contDiff.comp
    (contDiff_snd.comp contDiff_fst)).add
    ((contDiff_fst.comp contDiff_fst).smul
      ((volterra 1 (by norm_num)).contDiff.comp
        ((superposition_contDiff f hf).comp contDiff_snd)))

theorem scaledPicardMap_lipschitz (f : E → E) (hf : Continuous f)
    (L : ℝ≥0) (hLip : LipschitzWith L f) (q : ℝ × E) (c : ℝ≥0)
    (hqc : |q.1| * (L : ℝ) ≤ c) :
    LipschitzWith c (fun v => scaledPicardMap f hf (q, v)) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [scaledPicardMap, dist_eq_norm, add_sub_add_left_eq_sub,
    ← smul_sub, norm_smul, Real.norm_eq_abs, ← map_sub]
  calc
    |q.1| * ‖volterra 1 (by norm_num) (superposition f hf v - superposition f hf w)‖
        ≤ |q.1| * (1 * ‖superposition f hf v - superposition f hf w‖) :=
      mul_le_mul_of_nonneg_left (volterra_norm_le 1 (by norm_num) _) (abs_nonneg _)
    _ ≤ |q.1| * (L * ‖v - w‖) := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_left
        ((superposition_lipschitz (Time 1) f hf L hLip).norm_sub_le v w) (abs_nonneg _)
    _ ≤ c * ‖v - w‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hqc (norm_nonneg _)

theorem scaled_trajectory_hasDerivAt (Φ : ℝ × E → E) (f : E → E)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (q : ℝ × E) (τ : ℝ) :
    HasDerivAt (fun s => Φ (q.1 * s, q.2)) (q.1 • f (Φ (q.1 * τ, q.2))) τ := by
  simpa only [mul_one, Function.comp_def] using (hODE (q.1 * τ) q.2).scomp τ
    ((hasDerivAt_id τ).const_mul q.1)

def scaledFlowCurve (Φ : ℝ × E → E) (f : E → E)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (q : ℝ × E) : C(Time 1, E) :=
  ⟨fun τ => Φ (q.1 * τ, q.2),
    (continuous_iff_continuousAt.mpr (fun τ =>
      (scaled_trajectory_hasDerivAt Φ f hODE q τ).continuousAt)).comp continuous_subtype_val⟩

theorem scaledFlowCurve_fixedPoint (Φ : ℝ × E → E) (f : E → E) (hf : Continuous f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (q : ℝ × E) :
    scaledPicardMap f hf (q, scaledFlowCurve Φ f hODE q) = scaledFlowCurve Φ f hODE q := by
  ext τ
  change q.2 + q.1 • (∫ s in (0 : ℝ)..(τ : ℝ),
    extendCurve 1 (by norm_num) (superposition f hf (scaledFlowCurve Φ f hODE q)) s) =
      Φ (q.1 * τ, q.2)
  have hcon : Continuous (fun s => q.1 • f (Φ (q.1 * s, q.2))) :=
    continuous_const.smul (hf.comp (continuous_iff_continuousAt.mpr
      (fun s => (scaled_trajectory_hasDerivAt Φ f hODE q s).continuousAt)))
  rw [← intervalIntegral.integral_smul]
  have heq : (∫ s in (0 : ℝ)..(τ : ℝ), q.1 •
      extendCurve 1 (by norm_num) (superposition f hf (scaledFlowCurve Φ f hODE q)) s) =
      ∫ s in (0 : ℝ)..(τ : ℝ), q.1 • f (Φ (q.1 * s, q.2)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hsT : s ∈ Time 1 :=
      Set.uIcc_subset_Icc (by constructor <;> norm_num) τ.property hs
    simp only [extendCurve, projIcc_of_mem _ hsT, superposition, ContinuousMap.coe_mk,
      scaledFlowCurve]
  rw [heq, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => scaled_trajectory_hasDerivAt Φ f hODE q s) (hcon.intervalIntegrable _ _)]
  simp only [mul_zero, hinit, add_sub_cancel]

/-- Joint C¹ dependence on time and initial data is derived from the
actual ODE, for every short time satisfying `|t|L<1`. -/
theorem flow_contDiffAt_short [ProperSpace E] (Φ : ℝ × E → E)
    (f : E → E) (hf : ContDiff ℝ 1 f) (L : ℝ≥0) (hLip : LipschitzWith L f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (q : ℝ × E) (hshort : |q.1| * (L : ℝ) < 1) :
    ContDiffAt ℝ 1 Φ q := by
  let c : ℝ≥0 := ⟨(|q.1| * (L : ℝ) + 1) / 2, by positivity⟩
  have hc : c < 1 := by change (|q.1| * (L : ℝ) + 1) / 2 < 1; linarith
  have hlt : |q.1| * (L : ℝ) < c := by change _ < (_ + 1) / 2; linarith
  have hnear : ∀ᶠ p : ℝ × E in 𝓝 q, |p.1| * (L : ℝ) < c :=
    ((continuous_fst.abs.mul_const (L : ℝ)).continuousAt).eventually_lt continuousAt_const hlt
  have hLip' : ∀ᶠ p in 𝓝 q,
      LipschitzWith c (fun v => scaledPicardMap f hf.continuous (p, v)) := by
    filter_upwards [hnear] with p hp
    exact scaledPicardMap_lipschitz f hf.continuous L hLip p c hp.le
  have hcurve := fixedPoint_contDiffAt_of_eventually
    (scaledPicardMap f hf.continuous) (scaledFlowCurve Φ f hODE) q c hc hLip'
    (scaledFlowCurve_fixedPoint Φ f hf.continuous hODE hinit)
    (scaledPicardMap_contDiff f hf).contDiffAt
  have hfinal := ((ContinuousMap.evalCLM ℝ (⟨1, by constructor <;> norm_num⟩ : Time 1) :
    C(Time 1, E) →L[ℝ] E).contDiff.contDiffAt).comp q hcurve
  simpa only [Function.comp_def, ContinuousMap.evalCLM_apply, scaledFlowCurve,
    ContinuousMap.coe_mk, mul_one] using hfinal

/-- The global solution property and Lipschitz uniqueness imply the
semigroup identity; it is not an axiom of the supplied trajectories. -/
theorem flow_add (Φ : ℝ × E → E) (f : E → E)
    (L : ℝ≥0) (hLip : LipschitzWith L f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t s : ℝ) (x : E) :
    Φ (t + s, x) = Φ (s, Φ (t, x)) := by
  have hshift (s : ℝ) : HasDerivAt (fun u => Φ (t + u, x))
      (f (Φ (t + s, x))) s := by
    simpa only [zero_add, one_smul, Function.comp_def] using (hODE (t + s) x).scomp s
      ((hasDerivAt_const s t).add (hasDerivAt_id s))
  have h := ODE_solution_unique_univ (v := fun _ => f) (s := fun _ => Set.univ)
    (K := L) (t₀ := (0 : ℝ))
    (fun _ => hLip.lipschitzOnWith)
    (fun u => ⟨hshift u, Set.mem_univ _⟩)
    (fun u => ⟨hODE u (Φ (t, x)), Set.mem_univ _⟩)
    (by simp only [add_zero, hinit])
  exact congrFun h s

/-- C¹ of every fixed-time map follows by splitting an arbitrary time
into sufficiently small pieces and using the derived semigroup identity. -/
theorem flow_slice_contDiff [ProperSpace E] (Φ : ℝ × E → E)
    (f : E → E) (hf : ContDiff ℝ 1 f) (L : ℝ≥0) (hLip : LipschitzWith L f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) :
    ContDiff ℝ 1 (fun x => Φ (t, x)) := by
  have hsmall (s : ℝ) (hs : |s| * (L : ℝ) < 1) :
      ContDiff ℝ 1 (fun x => Φ (s, x)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (flow_contDiffAt_short Φ f hf L hLip hODE hinit (s, x) hs).comp x
      (contDiffAt_const.prodMk contDiffAt_id)
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (|t| * (L : ℝ)))
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_of_lt ((le_max_left _ _).trans_lt hn))
  have hnL : |t| * (L : ℝ) < n := (le_max_right _ _).trans_lt hn
  let s := t / n
  have hs : |s| * (L : ℝ) < 1 := by
    dsimp [s]
    rw [abs_div, abs_of_pos hn0, div_mul_eq_mul_div, div_lt_one hn0]
    exact hnL
  have hind (k : ℕ) : ContDiff ℝ 1 (fun x => Φ ((k : ℝ) * s, x)) := by
    induction k with
    | zero =>
        have heq : (fun x : E => Φ (((0 : ℕ) : ℝ) * s, x)) = id := by
          funext x
          change Φ (((0 : ℕ) : ℝ) * s, x) = x
          simpa only [Nat.cast_zero, zero_mul] using hinit x
        rw [heq]
        exact contDiff_id
    | succ k ih =>
        have hc := (hsmall s hs).comp ih
        convert hc using 1
        ext x
        simp only [Function.comp_def]
        rw [← flow_add Φ f L hLip hODE hinit]
        apply congrArg (fun u : ℝ => Φ (u, x))
        push_cast
        ring
  have htime : (n : ℝ) * s = t := by dsimp [s]; field_simp
  simpa only [htime] using hind n

/-- Genuine joint C¹ dependence of globally defined ODE trajectories,
from only a C¹ globally Lipschitz primitive force and the actual ODE. -/
theorem flow_contDiff_of_globalLip [ProperSpace E] (Φ : ℝ × E → E)
    (f : E → E) (hf : ContDiff ℝ 1 f) (L : ℝ≥0) (hLip : LipschitzWith L f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) : ContDiff ℝ 1 Φ := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  have hinner : ContDiff ℝ 1 (fun p : ℝ × E => (p.1 - q.1, Φ (q.1, p.2))) :=
    (contDiff_fst.sub contDiff_const).prodMk
      ((flow_slice_contDiff Φ f hf L hLip hODE hinit q.1).comp contDiff_snd)
  have hout := flow_contDiffAt_short Φ f hf L hLip hODE hinit
    (0, Φ (q.1, q.2)) (by simp)
  have hfinal : ContDiffAt ℝ 1 (fun p : ℝ × E => Φ (p.1 - q.1, Φ (q.1, p.2))) q := by
    have hout' : ContDiffAt ℝ 1 Φ (q.1 - q.1, Φ (q.1, q.2)) := by
      simpa only [sub_self] using hout
    exact hout'.comp q hinner.contDiffAt
  convert hfinal using 1
  ext p
  rw [← flow_add Φ f L hLip hODE hinit]
  apply congrArg (fun u : ℝ => Φ (u, p.2))
  ring

end TimeCurves




section Volume
open PBGSO.ContinuousVolume
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Continuous volume preservation with the C¹ regularity of the flow
actually derived from a globally Lipschitz C¹ primitive vector field. -/
theorem phase_flow_fderiv_det_one_globalLip
    (F : (ι → ℝ) → (ι → ℝ)) (hF : ContDiff ℝ 1 F)
    (Φ : ℝ × Phase ι → Phase ι) (L : ℝ≥0)
    (hLip : LipschitzWith L (phaseField F))
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (phaseField F (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : Phase ι) :
    (fderiv ℝ (fun y => Φ (t, y)) x).det = 1 :=
  phase_flow_fderiv_det_one_C1 F hF Φ
    (flow_contDiff_of_globalLip Φ (phaseField F) (phaseField_contDiff F hF) L hLip hODE hinit)
    hODE hinit t x

end Volume

end PBGSO.FlowDifferentiability
