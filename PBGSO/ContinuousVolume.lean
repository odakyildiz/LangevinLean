import PBGSO.Volume
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Tactic

/-!
# Continuous volume: Jacobi's identity and the interwoven drift

This file proves the determinant evolution from the actual matrix
variational equation, rather than assuming determinant preservation.
The full source lemma additionally requires differentiability in initial
data for globally defined C¹ ODE flows. Mathlib's ODE API does not currently
provide that theorem. Any extra flow regularity used below is explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators Topology
namespace PBGSO
namespace ContinuousVolume

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant is a continuous multilinear map of its matrix rows. -/
def detRows : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ where
  toMultilinearMap := (Matrix.detRowAlternating : (ι → ℝ) [⋀^ι]→ₗ[ℝ] ℝ).toMultilinearMap
  cont := continuous_id.matrix_det

@[simp] theorem detRows_apply (A : Matrix ι ι ℝ) : detRows A = A.det := rfl

/-- Row replacement gives Jacobi's identity without assuming that `J` is
invertible. This includes singular matrices and zero-dimensional spaces. -/
theorem detRows_linearDeriv_mul (A J : Matrix ι ι ℝ) :
    (detRows.linearDeriv J) (A * J) = A.trace * J.det := by
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  change (∑ i, (J.updateRow i ((A * J) i)).det) = _
  have hrow (i : ι) : (A * J) i = ∑ k, A i k • J k := by
    ext j
    simp [Matrix.mul_apply]
  simp_rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  rw [← Finset.sum_mul]
  rfl

/-- Jacobi's formula along a genuine matrix trajectory satisfying the
variational ODE `J'=A J`. -/
theorem hasDerivAt_det_of_variational {J : ℝ → Matrix ι ι ℝ}
    {A : Matrix ι ι ℝ} {t : ℝ} (hJ : HasDerivAt J (A * J t) t) :
    HasDerivAt (fun s => (J s).det) (A.trace * (J t).det) t := by
  have h := (detRows.hasFDerivAt (J t)).comp_hasDerivAt t hJ
  simpa only [Function.comp_def, detRows_apply, detRows_linearDeriv_mul] using h

/-- A trace-free variational equation preserves its initial determinant.
The differential equation and initial Jacobian are inputs; no determinant
identity or volume assertion is assumed. -/
theorem det_eq_initial_of_variational (J A : ℝ → Matrix ι ι ℝ)
    (hJ : ∀ t, HasDerivAt J (A t * J t) t)
    (htrace : ∀ t, (A t).trace = 0) (t : ℝ) : (J t).det = (J 0).det := by
  have hd (s : ℝ) : HasDerivAt (fun r => (J r).det) 0 s := by
    simpa only [htrace s, zero_mul] using hasDerivAt_det_of_variational (hJ s)
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0

/-- Velocity and position coordinates of the complete parameter/particle
state. The index set can include both parameter and all particle indices. -/
abbrev Phase (ι : Type*) := (ι ⊕ ι) → ℝ

def positionProjection : Phase ι →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (Sum.inr i))

/-- The A/B force-free-friction vector field, with independent optimiser
and sampler forces combined in `F`. No common potential is assumed. -/
def phaseField (F : (ι → ℝ) → (ι → ℝ)) (z : Phase ι) : Phase ι :=
  Sum.elim (fun i => -F (positionProjection z) i) (fun i => z (Sum.inl i))

/-- Its derivative has zero diagonal blocks and arbitrary off-diagonal
force derivative. -/
def phaseFieldDerivative (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Phase ι →L[ℝ] Phase ι :=
  ContinuousLinearMap.pi (Sum.elim
    (fun i => -((ContinuousLinearMap.proj i).comp (L.comp positionProjection)))
    (fun i => ContinuousLinearMap.proj (Sum.inl i)))

theorem phaseField_hasFDerivAt (F : (ι → ℝ) → (ι → ℝ)) (z : Phase ι)
    (hF : DifferentiableAt ℝ F (positionProjection z)) :
    HasFDerivAt (phaseField F) (phaseFieldDerivative (fderiv ℝ F (positionProjection z))) z := by
  apply hasFDerivAt_pi.2
  intro k
  cases k with
  | inl i =>
    exact (((ContinuousLinearMap.proj i).hasFDerivAt.comp z
      (hF.hasFDerivAt.comp z positionProjection.hasFDerivAt)).neg)
  | inr i => exact (ContinuousLinearMap.proj (Sum.inl i) : Phase ι →L[ℝ] ℝ).hasFDerivAt

/-- Coordinate matrix of an actual Fréchet derivative in the standard
basis. Its determinant is the Euclidean Jacobian determinant. -/
def derivativeMatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L : (κ → ℝ) →L[ℝ] (κ → ℝ)) : Matrix κ κ ℝ :=
  fun i j => L (Pi.single j 1) i

theorem derivativeMatrix_mul {κ : Type*} [Fintype κ] [DecidableEq κ]
    (L K : (κ → ℝ) →L[ℝ] (κ → ℝ)) :
    derivativeMatrix (L.comp K) = derivativeMatrix L * derivativeMatrix K := by
  ext i j
  have hvec : K (Pi.single j 1) = ∑ k : κ, K (Pi.single j 1) k • Pi.single k (1 : ℝ) := by
    exact pi_eq_sum_univ' _
  change L (K (Pi.single j 1)) i = ∑ k, _
  rw [hvec, map_sum]
  simp [derivativeMatrix, Finset.sum_apply, map_smul, mul_comm]

/-- The actual A/B drift has divergence zero. This is derived from its
coordinate formula and the force derivative; it is not an assumption. -/
theorem phaseField_trace_zero (F : (ι → ℝ) → (ι → ℝ)) (z : Phase ι)
    (hF : DifferentiableAt ℝ F (positionProjection z)) :
    (derivativeMatrix (fderiv ℝ (phaseField F) z)).trace = 0 := by
  rw [(phaseField_hasFDerivAt F z hF).fderiv]
  simp [derivativeMatrix, phaseFieldDerivative, positionProjection,
    Matrix.trace, Matrix.diag, Fintype.sum_sum_type]
  change (∑ i : ι, (fderiv ℝ F (positionProjection z)) 0 i) = 0
  simp

section SmoothFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The joint derivative in a spatial direction is the actual derivative
of the corresponding fixed-time flow map. -/
theorem spatial_hasFDerivAt (Φ : ℝ × E → E) (hΦ : Differentiable ℝ Φ)
    (t : ℝ) (x : E) :
    HasFDerivAt (fun y => Φ (t, y))
      ((fderiv ℝ Φ (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
  exact (hΦ (t, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))

/-- The time component of the joint derivative is obtained from the ODE
itself by uniqueness of the derivative. -/
theorem joint_time_derivative (Φ : ℝ × E → E) (f : E → E)
    (hΦ : Differentiable ℝ Φ)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (t : ℝ) (x : E) : fderiv ℝ Φ (t, x) (1, 0) = f (Φ (t, x)) := by
  have hd := (hΦ (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact hd.unique (hode t x)

/-- Mixed derivatives of a C² joint flow turn its original ODE into the
spatial variational equation. The variational equation is proved here,
not added as an assumption. -/
theorem mixed_flow_variational (Φ : ℝ × E → E) (f : E → E)
    (hΦ : ContDiff ℝ 2 Φ) (hf : Differentiable ℝ f)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (t : ℝ) (x v : E) :
    fderiv ℝ (fderiv ℝ Φ) (t, x) (1, 0) (0, v) =
      fderiv ℝ f (Φ (t, x)) (fderiv ℝ Φ (t, x) (0, v)) := by
  have hdΦ : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsec : HasFDerivAt (fun y : E => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ E) x :=
    (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
  have hl := ((hD (t, x)).hasFDerivAt.comp x hsec).clm_apply
    (hasFDerivAt_const ((1 : ℝ), (0 : E)) x)
  have hr := (hf (Φ (t, x))).hasFDerivAt.comp x (spatial_hasFDerivAt Φ hdΦ t x)
  have heq : (fun y : E => fderiv ℝ Φ (t, y) (1, 0)) =
      (fun y : E => f (Φ (t, y))) :=
    funext (joint_time_derivative Φ f hdΦ hode t)
  simp only [Function.comp_def] at hl hr
  rw [heq] at hl
  have he := congrArg (fun L : E →L[ℝ] E => L v) (hl.unique hr)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.inr_apply, add_zero,
    ContinuousLinearMap.flip_apply] at he
  have hsym : IsSymmSndFDerivAt ℝ Φ (t, x) :=
    (hΦ.contDiffAt (x := (t, x))).isSymmSndFDerivAt (by norm_num)
  simp only [map_zero, zero_add] at he
  exact (hsym.eq (1, 0) (0, v)).trans he

end SmoothFlow

section MatrixFlow
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The spatial Jacobian of the joint flow, in the standard basis. -/
def flowJacobian (Φ : ℝ × (κ → ℝ) → (κ → ℝ)) (t : ℝ) (x : κ → ℝ) : Matrix κ κ ℝ :=
  fun i j => fderiv ℝ Φ (t, x) (0, Pi.single j 1) i

/-- The matrix used above is exactly the derivative of the fixed-time
flow map, so its determinant is the genuine flow Jacobian determinant. -/
theorem flowJacobian_eq_derivativeMatrix (Φ : ℝ × (κ → ℝ) → (κ → ℝ))
    (hΦ : Differentiable ℝ Φ) (t : ℝ) (x : κ → ℝ) :
    flowJacobian Φ t x = derivativeMatrix (fderiv ℝ (fun y => Φ (t, y)) x) := by
  rw [(spatial_hasFDerivAt Φ hΦ t x).fderiv]
  rfl

theorem linearMap_eval_eq_sum (L : (κ → ℝ) →L[ℝ] (κ → ℝ)) (v : κ → ℝ) (i : κ) :
    L v i = ∑ j, derivativeMatrix L i j * v j := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  rw [map_sum]
  simp [derivativeMatrix, Finset.sum_apply, mul_comm]

/-- The true spatial Jacobian satisfies the matrix variational ODE. It is
derived from the C² joint flow and the original vector-field ODE. -/
theorem flowJacobian_hasDeriv (Φ : ℝ × (κ → ℝ) → (κ → ℝ)) (f : (κ → ℝ) → (κ → ℝ))
    (hΦ : ContDiff ℝ 2 Φ) (hf : Differentiable ℝ f)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (t : ℝ) (x : κ → ℝ) :
    HasDerivAt (fun s => flowJacobian Φ s x)
      (derivativeMatrix (fderiv ℝ f (Φ (t, x))) * flowJacobian Φ t x) t := by
  have hD : Differentiable ℝ (fderiv ℝ Φ) :=
    (hΦ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have htime := (hD (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hcol := htime.clm_apply (hasDerivAt_const t ((0 : ℝ), Pi.single j (1 : ℝ)))
  have hi := (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hcol
  simp only [Function.comp_def, ContinuousLinearMap.proj_apply, map_zero, add_zero] at hi
  rw [mixed_flow_variational Φ f hΦ hf hode t x (Pi.single j 1)] at hi
  change HasDerivAt (fun s => flowJacobian Φ s x i j) _ t at hi
  convert hi using 1
  exact (linearMap_eval_eq_sum (fderiv ℝ f (Φ (t, x)))
    (fderiv ℝ Φ (t, x) (0, Pi.single j 1)) i).symm

theorem flowJacobian_initial (Φ : ℝ × (κ → ℝ) → (κ → ℝ))
    (hΦ : Differentiable ℝ Φ) (hinit : ∀ x, Φ (0, x) = x) (x : κ → ℝ) :
    flowJacobian Φ 0 x = 1 := by
  rw [flowJacobian_eq_derivativeMatrix Φ hΦ]
  have he : (fun y => Φ (0, y)) = id := funext hinit
  rw [he, fderiv_id]
  ext i j
  simp [derivativeMatrix, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem derivativeMatrix_det (L : (κ → ℝ) →L[ℝ] (κ → ℝ)) :
    (derivativeMatrix L).det = L.det := by
  change (LinearMap.toMatrix' L.toLinearMap).det = L.toLinearMap.det
  exact LinearMap.det_toMatrix' _

/-- Continuous Jacobian preservation for an actual C² joint flow of the
interwoven A/B vector field. The force is arbitrary differentiable and need
not be conservative. The extra joint-flow C² hypothesis is explicit; its
derivation from the source's C¹ force/global-flow assumptions is separate. -/
theorem phase_flowJacobian_det_one
    (F : (ι → ℝ) → (ι → ℝ)) (hF : Differentiable ℝ F)
    (Φ : ℝ × Phase ι → Phase ι) (hΦ : ContDiff ℝ 2 Φ)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (phaseField F (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : Phase ι) :
    (flowJacobian Φ t x).det = 1 := by
  have hf : Differentiable ℝ (phaseField F) := fun z =>
    (phaseField_hasFDerivAt F z (hF _)).differentiableAt
  have hJ := flowJacobian_hasDeriv Φ (phaseField F) hΦ hf hode
  have htrace (s : ℝ) :
      (derivativeMatrix (fderiv ℝ (phaseField F) (Φ (s, x)))).trace = 0 :=
    phaseField_trace_zero F (Φ (s, x)) (hF _)
  have h := det_eq_initial_of_variational (fun s => flowJacobian Φ s x)
    (fun s => derivativeMatrix (fderiv ℝ (phaseField F) (Φ (s, x))))
    (fun s => hJ s x) htrace t
  rw [flowJacobian_initial Φ (hΦ.differentiable (by norm_num)) hinit x, Matrix.det_one] at h
  exact h

/-- The continuous determinant statement in the source lemma, under the
explicit stronger joint-flow C² regularity. Its conclusion uses the actual
Fréchet derivative of the fixed-time flow. -/
theorem phase_flow_fderiv_det_one
    (F : (ι → ℝ) → (ι → ℝ)) (hF : Differentiable ℝ F)
    (Φ : ℝ × Phase ι → Phase ι) (hΦ : ContDiff ℝ 2 Φ)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (phaseField F (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : Phase ι) :
    (fderiv ℝ (fun y => Φ (t, y)) x).det = 1 := by
  rw [← derivativeMatrix_det,
    ← flowJacobian_eq_derivativeMatrix Φ (hΦ.differentiable (by norm_num))]
  exact phase_flowJacobian_det_one F hF Φ hΦ hode hinit t x

end MatrixFlow

section COneFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

/-- The spatial part of the actual derivative of a joint map. -/
def jointSpatialDerivative (G : ℝ × E → E) (p : ℝ × E) : E →L[ℝ] E :=
  (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ ℝ E)

theorem jointSpatialDerivative_continuous (G : ℝ × E → E) (hG : ContDiff ℝ 1 G) :
    Continuous (jointSpatialDerivative G) :=
  (hG.continuous_fderiv (by norm_num)).clm_comp continuous_const

/-- Differentiate a C¹ joint map under a finite time integral. The uniform
derivative dominator is proved by compactness of the time interval times a
closed ball, rather than supplied as a hypothesis. -/
theorem integral_spatial_hasFDerivAt (G : ℝ × E → E) (hG : ContDiff ℝ 1 G)
    (a b : ℝ) (x : E) :
    HasFDerivAt (fun y => ∫ s in a..b, G (s, y))
      (∫ s in a..b, jointSpatialDerivative G (s, x)) x := by
  have hD := jointSpatialDerivative_continuous G hG
  have hcompact : IsCompact (uIcc a b ×ˢ Metric.closedBall x 1) :=
    isCompact_uIcc.prod (isCompact_closedBall x 1)
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hD.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall x 1) (bound := fun _ => M)
    (Metric.closedBall_mem_nhds x zero_lt_one)
  · exact Filter.Eventually.of_forall (fun y =>
      (hG.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self)
  · exact (hG.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  · exact (hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  · apply Filter.Eventually.of_forall
    intro s hs y hy
    exact hM (s, y) ⟨⟨hs.1.le, hs.2⟩, hy⟩
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro s hs y hy
    exact spatial_hasFDerivAt G (hG.differentiable (by norm_num)) s y

/-- The integral ODE follows from the original time derivative and initial
condition by the fundamental theorem of calculus. -/
theorem flow_integral_identity (Φ : ℝ × E → E) (f : E → E)
    (hΦ : Continuous Φ) (hf : Continuous f)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : E) :
    Φ (t, x) = x + ∫ s in 0..t, f (Φ (s, x)) := by
  have hc : Continuous (fun s : ℝ => f (Φ (s, x))) :=
    hf.comp (hΦ.comp (continuous_id.prodMk continuous_const))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hode s x) (hc.intervalIntegrable 0 t)
  rw [hinit] at he
  rw [he]
  abel

/-- Differentiating the actual integral ODE in its initial value proves
the spatial integral equation for a C¹ joint flow. -/
theorem spatial_derivative_integral_identity (Φ : ℝ × E → E) (f : E → E)
    (hΦ : ContDiff ℝ 1 Φ) (hf : ContDiff ℝ 1 f)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : E) :
    jointSpatialDerivative Φ (t, x) = ContinuousLinearMap.id ℝ E +
      ∫ s in 0..t, jointSpatialDerivative (fun p => f (Φ p)) (s, x) := by
  have hleft := spatial_hasFDerivAt Φ (hΦ.differentiable (by norm_num)) t x
  have hright := (hasFDerivAt_id x).add
    (integral_spatial_hasFDerivAt (fun p => f (Φ p)) (hf.comp hΦ) 0 t x)
  have heq : (fun y => Φ (t, y)) =
      (fun y => y + ∫ s in 0..t, f (Φ (s, y))) :=
    funext (flow_integral_identity Φ f hΦ.continuous hf.continuous hode hinit t)
  rw [heq] at hleft
  exact hleft.unique hright

/-- The true spatial derivative satisfies the variational ODE with only
C¹ flow and C¹ vector-field regularity. Differentiation under the time
integral and the fundamental theorem of calculus prove this equation. -/
theorem jointSpatialDerivative_hasDeriv_C1 (Φ : ℝ × E → E) (f : E → E)
    (hΦ : ContDiff ℝ 1 Φ) (hf : ContDiff ℝ 1 f)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : E) :
    HasDerivAt (fun s => jointSpatialDerivative Φ (s, x))
      ((fderiv ℝ f (Φ (t, x))).comp (jointSpatialDerivative Φ (t, x))) t := by
  let G : ℝ × E → E := fun p => f (Φ p)
  have hG : ContDiff ℝ 1 G := hf.comp hΦ
  have hD : Continuous (fun s => jointSpatialDerivative G (s, x)) :=
    (jointSpatialDerivative_continuous G hG).comp (continuous_id.prodMk continuous_const)
  have hFTC := (hasDerivAt_const t (ContinuousLinearMap.id ℝ E)).add
    (intervalIntegral.integral_hasDerivAt_right (hD.intervalIntegrable 0 t)
      (hD.stronglyMeasurableAtFilter volume (𝓝 t)) hD.continuousAt)
  have heq : (fun s => jointSpatialDerivative Φ (s, x)) =
      (fun s => ContinuousLinearMap.id ℝ E + ∫ r in 0..s, jointSpatialDerivative G (r, x)) :=
    funext (fun s => spatial_derivative_integral_identity Φ f hΦ hf hode hinit s x)
  change HasDerivAt
    (fun s => ContinuousLinearMap.id ℝ E + ∫ r in 0..s, jointSpatialDerivative G (r, x))
    (0 + jointSpatialDerivative G (t, x)) t at hFTC
  rw [← heq] at hFTC
  have hchain : fderiv ℝ G (t, x) =
      (fderiv ℝ f (Φ (t, x))).comp (fderiv ℝ Φ (t, x)) :=
    (((hf.differentiable (by norm_num)) _).hasFDerivAt.comp (t, x)
      (((hΦ.differentiable (by norm_num)) _).hasFDerivAt)).fderiv
  simpa only [zero_add, jointSpatialDerivative, hchain, ContinuousLinearMap.comp_assoc] using hFTC

end COneFlow

section COneMatrixFlow
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The actual standard-basis Jacobian satisfies its matrix variational
equation for a C¹ joint flow of a C¹ vector field. -/
theorem flowJacobian_hasDeriv_C1 (Φ : ℝ × (κ → ℝ) → (κ → ℝ))
    (f : (κ → ℝ) → (κ → ℝ)) (hΦ : ContDiff ℝ 1 Φ) (hf : ContDiff ℝ 1 f)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : κ → ℝ) :
    HasDerivAt (fun s => flowJacobian Φ s x)
      (derivativeMatrix (fderiv ℝ f (Φ (t, x))) * flowJacobian Φ t x) t := by
  have hJ := jointSpatialDerivative_hasDeriv_C1 Φ f hΦ hf hode hinit t x
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hcol := hJ.clm_apply (hasDerivAt_const t (Pi.single j (1 : ℝ)))
  have hi := (ContinuousLinearMap.proj i : (κ → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hcol
  simp only [Function.comp_def, ContinuousLinearMap.proj_apply, map_zero, add_zero,
    jointSpatialDerivative, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at hi
  change HasDerivAt (fun s => flowJacobian Φ s x i j) _ t at hi
  convert hi using 1
  exact (linearMap_eval_eq_sum (fderiv ℝ f (Φ (t, x)))
    (fderiv ℝ Φ (t, x) (0, Pi.single j 1)) i).symm

/-- C¹ regularity of the arbitrary coupled position force gives C¹
regularity of the actual interwoven A/B vector field. -/
theorem phaseField_contDiff (F : (ι → ℝ) → (ι → ℝ)) (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (phaseField F) := by
  apply contDiff_pi.2
  intro j
  cases j with
  | inl i =>
      exact ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.comp
        (hF.comp positionProjection.contDiff)).neg
  | inr i =>
      exact (ContinuousLinearMap.proj (Sum.inl i) : Phase ι →L[ℝ] ℝ).contDiff

/-- The continuous Jacobian determinant theorem for an actual C¹ joint
flow of the source's C¹ force field. The spatial variational equation is
derived by differentiation under its actual integral ODE. -/
theorem phase_flowJacobian_det_one_C1
    (F : (ι → ℝ) → (ι → ℝ)) (hF : ContDiff ℝ 1 F)
    (Φ : ℝ × Phase ι → Phase ι) (hΦ : ContDiff ℝ 1 Φ)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (phaseField F (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : Phase ι) :
    (flowJacobian Φ t x).det = 1 := by
  have hJ := flowJacobian_hasDeriv_C1 Φ (phaseField F) hΦ (phaseField_contDiff F hF) hode hinit
  have htrace (s : ℝ) :
      (derivativeMatrix (fderiv ℝ (phaseField F) (Φ (s, x)))).trace = 0 :=
    phaseField_trace_zero F (Φ (s, x)) ((hF.differentiable (by norm_num)) _)
  have h := det_eq_initial_of_variational (fun s => flowJacobian Φ s x)
    (fun s => derivativeMatrix (fderiv ℝ (phaseField F) (Φ (s, x))))
    (fun s => hJ s x) htrace t
  rw [flowJacobian_initial Φ (hΦ.differentiable (by norm_num)) hinit x, Matrix.det_one] at h
  exact h

/-- C¹-flow version of the source continuous volume lemma, stated with
the genuine derivative of the fixed-time flow. A global C¹ joint flow is
explicitly supplied; its smooth dependence from C¹ vector-field regularity
and globally existing individual trajectories is a separate obligation. -/
theorem phase_flow_fderiv_det_one_C1
    (F : (ι → ℝ) → (ι → ℝ)) (hF : ContDiff ℝ 1 F)
    (Φ : ℝ × Phase ι → Phase ι) (hΦ : ContDiff ℝ 1 Φ)
    (hode : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (phaseField F (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : Phase ι) :
    (fderiv ℝ (fun y => Φ (t, y)) x).det = 1 := by
  rw [← derivativeMatrix_det,
    ← flowJacobian_eq_derivativeMatrix Φ (hΦ.differentiable (by norm_num))]
  exact phase_flowJacobian_det_one_C1 F hF Φ hΦ hode hinit t x

end COneMatrixFlow

end ContinuousVolume
end PBGSO
