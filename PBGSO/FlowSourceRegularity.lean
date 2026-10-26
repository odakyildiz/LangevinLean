import PBGSO.FlowDifferentiability
import PBGSO.FlowLocalization
import PBGSO.GlobalODE

/-! # Source C¹ flow regularity by compact orbit localization

The original field needs only C¹ regularity. Global Lipschitz constants are
constructed for compact cutoffs. Equality with the source trajectories is
proved by ODE uniqueness and a compact-open tube argument.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Set Filter Metric
open scoped Topology NNReal ContDiff
namespace PBGSO.FlowSourceRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Finite-time uniqueness for a primitive C¹ vector field. The needed
Lipschitz bound is derived on a compact ball containing both trajectories. -/
theorem trajectories_unique_Icc (f : E → E) (hf : ContDiff ℝ 1 f)
    (a b t₀ : ℝ) (ht₀ : t₀ ∈ Ioo a b) (u v : ℝ → E)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hu' : ∀ t ∈ Ioo a b, HasDerivAt u (f (u t)) t)
    (hv' : ∀ t ∈ Ioo a b, HasDerivAt v (f (v t)) t)
    (heq : u t₀ = v t₀) : EqOn u v (Icc a b) := by
  obtain ⟨Cu, hCu⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  obtain ⟨Cv, hCv⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  let R := max Cu Cv
  obtain ⟨L, hL⟩ := (hf.contDiffOn (s := closedBall (0 : E) R)).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have humem (t : ℝ) (ht : t ∈ Ioo a b) : u t ∈ closedBall (0 : E) R := by
    simpa only [mem_closedBall, dist_zero_right] using
      (hCu t (Ioo_subset_Icc_self ht)).trans (le_max_left Cu Cv)
  have hvmem (t : ℝ) (ht : t ∈ Ioo a b) : v t ∈ closedBall (0 : E) R := by
    simpa only [mem_closedBall, dist_zero_right] using
      (hCv t (Ioo_subset_Icc_self ht)).trans (le_max_right Cu Cv)
  exact ODE_solution_unique_of_mem_Icc (v := fun _ => f)
    (s := fun _ => closedBall (0 : E) R) (fun _ _ => hL) ht₀
    hu hu' humem hv hv' hvmem heq

/-- The only construction interface here is existence of actual global
trajectories for globally Lipschitz C¹ cutoff fields. It contains no
continuity or differentiability assertion about their solution selector.
The final source theorem discharges this interface by a global Picard
construction. -/
theorem flow_contDiff_of_cutoff_solutions
    (hExists : ∀ (g : E → E) (L : ℝ≥0), ContDiff ℝ 1 g → LipschitzWith L g →
      ∃ Ψ : ℝ × E → E,
        (∀ t x, HasDerivAt (fun s => Ψ (s, x)) (g (Ψ (t, x))) t) ∧
        (∀ x, Ψ (0, x) = x))
    (Φ : ℝ × E → E) (f : E → E) (hf : ContDiff ℝ 1 f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) : ContDiff ℝ 1 Φ := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  let a := min 0 q.1 - 1
  let b := max 0 q.1 + 1
  have hzero : (0 : ℝ) ∈ Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [min_le_left (0 : ℝ) q.1, le_max_left (0 : ℝ) q.1]
  have hq : q.1 ∈ Ioo a b := by
    constructor <;> dsimp [a, b] <;> linarith [min_le_right (0 : ℝ) q.1, le_max_right (0 : ℝ) q.1]
  have htime (x : E) : Continuous (fun t => Φ (t, x)) :=
    continuous_iff_continuousAt.mpr (fun t => (hODE t x).continuousAt)
  let K := (fun t => Φ (t, q.2)) '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image (htime q.2)
  obtain ⟨g, L, U, hU, hKU, hgf, hg, hLip, _⟩ :=
    exists_global_lipschitz_C1_cutoff f hf K hK
  obtain ⟨Ψ, hΨODE, hΨinit⟩ := hExists g L hg hLip
  have hΨ : ContDiff ℝ 1 Ψ := FlowDifferentiability.flow_contDiff_of_globalLip
    Ψ g hg L hLip hΨODE hΨinit
  have hEqbase : EqOn (fun t => Ψ (t, q.2)) (fun t => Φ (t, q.2)) (Icc a b) := by
    apply ODE_solution_unique_of_mem_Icc (v := fun _ => g) (s := fun _ => Set.univ)
      (K := L) (fun _ _ => hLip.lipschitzOnWith) hzero
      (fun t _ => (hΨODE t q.2).continuousAt.continuousWithinAt)
      (fun t _ => hΨODE t q.2) (fun _ _ => Set.mem_univ _)
      (htime q.2).continuousOn
      (fun t ht => ?_) (fun _ _ => Set.mem_univ _) (by rw [hΨinit, hinit])
    rw [hgf (hKU (mem_image_of_mem _ (Ioo_subset_Icc_self ht)))]
    exact hODE t q.2
  let curried : C(E, C(ℝ, E)) :=
    (⟨fun p : E × ℝ => Ψ (p.2, p.1), hΨ.continuous.comp continuous_swap⟩ :
      C(E × ℝ, E)).curry
  have hbase : MapsTo (curried q.2) (Icc a b) U := by
    intro t ht
    change Ψ (t, q.2) ∈ U
    have heqpoint : Ψ (t, q.2) = Φ (t, q.2) := hEqbase ht
    rw [heqpoint]
    exact hKU (mem_image_of_mem _ ht)
  have htube : ∀ᶠ x in 𝓝 q.2, MapsTo (curried x) (Icc a b) U :=
    (curried.continuous.tendsto q.2).eventually
      (ContinuousMap.eventually_mapsTo isCompact_Icc hU hbase)
  have hEqnear : ∀ᶠ x in 𝓝 q.2,
      EqOn (fun t => Φ (t, x)) (fun t => Ψ (t, x)) (Icc a b) := by
    filter_upwards [htube] with x hx
    apply trajectories_unique_Icc f hf a b 0 hzero _ _ (htime x).continuousOn
      (fun t _ => (hΨODE t x).continuousAt.continuousWithinAt)
      (fun t _ => hODE t x) (fun t ht => ?_) (by rw [hinit, hΨinit])
    have hmem : Ψ (t, x) ∈ U := hx (Ioo_subset_Icc_self ht)
    rw [← hgf hmem]
    exact hΨODE t x
  have hEqlocal : Φ =ᶠ[𝓝 q] Ψ := by
    filter_upwards [continuousAt_fst.eventually (isOpen_Ioo.mem_nhds hq),
      continuousAt_snd.eventually hEqnear] with p hp hx
    exact hx (Ioo_subset_Icc_self hp)
  exact hΨ.contDiffAt.congr_of_eventuallyEq hEqlocal

/-- Source smooth-dependence theorem. A finite-dimensional primitive C¹
field and globally defined actual individual trajectories imply joint C¹
regularity of the flow. All cutoff trajectory existence is constructed by
global Picard iteration; no solution-map regularity is assumed. -/
theorem flow_contDiff (Φ : ℝ × E → E) (f : E → E) (hf : ContDiff ℝ 1 f)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) : ContDiff ℝ 1 Φ := by
  apply flow_contDiff_of_cutoff_solutions _ Φ f hf hODE hinit
  intro g L _ hLip
  obtain ⟨Ψ, hΨinit, hΨODE⟩ := PBGSO.exists_global_ode_flow g L hLip
  exact ⟨Ψ, hΨODE, hΨinit⟩

section Volume
open PBGSO.ContinuousVolume
variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- Liouville preservation for an arbitrary finite-dimensional divergence
free C¹ primitive field with actual globally defined trajectories. Both
smooth dependence and the variational equation are derived. -/
theorem divergenceFree_flow_fderiv_det_one
    (f : (κ → ℝ) → (κ → ℝ)) (hf : ContDiff ℝ 1 f)
    (hdiv : ∀ x, (derivativeMatrix (fderiv ℝ f x)).trace = 0)
    (Φ : ℝ × (κ → ℝ) → (κ → ℝ))
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (f (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : κ → ℝ) :
    (fderiv ℝ (fun y => Φ (t, y)) x).det = 1 := by
  have hΦ := flow_contDiff Φ f hf hODE hinit
  rw [← derivativeMatrix_det,
    ← flowJacobian_eq_derivativeMatrix Φ (hΦ.differentiable (by norm_num))]
  have hJ := flowJacobian_hasDeriv_C1 Φ f hΦ hf hODE hinit
  have h := det_eq_initial_of_variational (fun s => flowJacobian Φ s x)
    (fun s => derivativeMatrix (fderiv ℝ f (Φ (s, x))))
    (fun s => hJ s x) (fun s => hdiv (Φ (s, x))) t
  rw [flowJacobian_initial Φ (hΦ.differentiable (by norm_num)) hinit x, Matrix.det_one] at h
  exact h

/-- The source continuous volume lemma from its primitive assumptions:
C¹ of the arbitrary joint force and globally defined original A/B ODE
trajectories. There is no supplied flow-regularity, variational-equation,
Lipschitz, or determinant-preservation premise. -/
theorem phase_flow_fderiv_det_one_source
    (F : (ι → ℝ) → (ι → ℝ)) (hF : ContDiff ℝ 1 F)
    (Φ : ℝ × Phase ι → Phase ι)
    (hODE : ∀ t x, HasDerivAt (fun s => Φ (s, x)) (phaseField F (Φ (t, x))) t)
    (hinit : ∀ x, Φ (0, x) = x) (t : ℝ) (x : Phase ι) :
    (fderiv ℝ (fun y => Φ (t, y)) x).det = 1 :=
  phase_flow_fderiv_det_one_C1 F hF Φ
    (flow_contDiff Φ (phaseField F) (phaseField_contDiff F hF) hODE hinit)
    hODE hinit t x

end Volume

end PBGSO.FlowSourceRegularity
