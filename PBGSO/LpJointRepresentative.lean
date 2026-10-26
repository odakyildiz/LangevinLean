import PBGSO.LpIntegralSections
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Actual joint representatives for Bochner L¹ families of L² variables

The representative is constructed from literal finite-valued time families,
completed in product L¹. Joint measurability of unrestricted point evaluation
on L² is neither assumed nor used. Section equality follows from actual L²
convergence, product-a.e. subsequence convergence and uniqueness in measure.
The finite time measure and probability-space assumptions are explicit.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace PBGSO.LpJointRepresentative
variable {T Ω R : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  (μ : Measure T) [IsFiniteMeasure μ] (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Literal joint realization of a finite-valued family of L² variables. -/
def simpleRaw (S : SimpleFunc T (Lp R 2 Q)) : T × Ω → R := fun p => S p.1 p.2

theorem simpleRaw_stronglyMeasurable (S : SimpleFunc T (Lp R 2 Q)) :
    StronglyMeasurable (simpleRaw Q S) := by
  classical
  induction S using SimpleFunc.induction' with
  | const v => exact (Lp.stronglyMeasurable v).comp_snd
  | @pcw f g s hs hf hg =>
    have hm : StronglyMeasurable ((Prod.fst ⁻¹' s).piecewise (simpleRaw Q f) (simpleRaw Q g)) :=
      hf.piecewise (hs.preimage measurable_fst) hg
    convert hm using 1
    funext p
    by_cases hp : p.1 ∈ s <;> simp [simpleRaw, hp]

theorem simpleRaw_integrable (S : SimpleFunc T (Lp R 2 Q)) :
    Integrable (simpleRaw Q S) (μ.prod Q) := by
  have h := LpIntegralSections.integrable_restrict_prod Q μ S
    (S.integrable_of_isFiniteMeasure) (fun t ω => S t ω)
    (simpleRaw_stronglyMeasurable Q S).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => Filter.EventuallyEq.rfl))
    Set.univ MeasurableSet.univ (measure_ne_top Q Set.univ)
  rw [Measure.restrict_univ] at h
  exact h

def simpleLift (S : SimpleFunc T (Lp R 2 Q)) : Lp R 1 (μ.prod Q) :=
  (memLp_one_iff_integrable.mpr (simpleRaw_integrable μ Q S)).toLp _

theorem simpleLift_coe (S : SimpleFunc T (Lp R 2 Q)) :
    simpleLift μ Q S =ᵐ[μ.prod Q] simpleRaw Q S :=
  MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr (simpleRaw_integrable μ Q S))

/-- A fixed finite bound for the probability-space embedding L²→L¹. -/
def embeddingConstant : ℝ :=
  ‖LpIntegralSections.setIntegralCLM (R := ℝ) Q Set.univ MeasurableSet.univ
    (measure_ne_top Q Set.univ)‖

theorem simpleLift_dist_le (S V : SimpleFunc T (Lp R 2 Q)) :
    dist (simpleLift μ Q S) (simpleLift μ Q V) ≤
      embeddingConstant Q * ∫ t, ‖S t - V t‖ ∂μ := by
  rw [dist_eq_norm, L1.norm_eq_integral_norm]
  have hraw : (fun p => ‖(simpleLift μ Q S - simpleLift μ Q V) p‖) =ᵐ[μ.prod Q]
      (fun p => ‖simpleRaw Q S p - simpleRaw Q V p‖) := by
    filter_upwards [Lp.coeFn_sub (simpleLift μ Q S) (simpleLift μ Q V),
      simpleLift_coe μ Q S, simpleLift_coe μ Q V] with p hp hS hV
    simp only [hp, Pi.sub_apply, hS, hV]
  rw [integral_congr_ae hraw]
  have hfub := integral_prod (fun p => ‖simpleRaw Q S p - simpleRaw Q V p‖)
    (((simpleRaw_integrable μ Q S).sub (simpleRaw_integrable μ Q V)).norm)
  rw [hfub]
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _
  · exact ((S.integrable_of_isFiniteMeasure.sub V.integrable_of_isFiniteMeasure).norm.const_mul _)
  · apply Filter.Eventually.of_forall
    intro t
    have he : (fun ω => (S t - V t) ω) =ᵐ[Q] (fun ω => S t ω - V t ω) :=
      Lp.coeFn_sub (S t) (V t)
    change (∫ ω, ‖S t ω - V t ω‖ ∂Q) ≤ _
    have hi := integral_congr_ae (he.fun_comp norm)
    change (∫ ω, ‖(S t - V t) ω‖ ∂Q) = (∫ ω, ‖S t ω - V t ω‖ ∂Q) at hi
    rw [← hi]
    simpa only [embeddingConstant, Measure.restrict_univ] using
      LpIntegralSections.integral_norm_le (R := R) Q Set.univ MeasurableSet.univ
        (measure_ne_top Q Set.univ) (S t - V t)


def simpleTimeLift (S : SimpleFunc T (Lp R 2 Q)) : Lp (Lp R 2 Q) 1 μ :=
  (memLp_one_iff_integrable.mpr S.integrable_of_isFiniteMeasure).toLp _

theorem simpleTimeLift_dist (S V : SimpleFunc T (Lp R 2 Q)) :
    dist (simpleTimeLift μ Q S) (simpleTimeLift μ Q V) = ∫ t, ‖S t - V t‖ ∂μ := by
  rw [dist_eq_norm, L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (simpleTimeLift μ Q S) (simpleTimeLift μ Q V),
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr (S.integrable_of_isFiniteMeasure (μ := μ))),
    MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr (V.integrable_of_isFiniteMeasure (μ := μ)))] with t ht hS hV
  rw [ht]
  change ‖simpleTimeLift μ Q S t - simpleTimeLift μ Q V t‖ = _
  change simpleTimeLift μ Q S t = S t at hS
  change simpleTimeLift μ Q V t = V t at hV
  rw [hS, hV]

/-- A Bochner L¹ family of L² random variables has an actual jointly
strongly measurable, product-integrable representative. No pointwise evaluation
of the whole L² space is assumed measurable. -/
theorem exists_joint_representative (F : T → Lp R 2 Q) (hF : Integrable F μ) :
    ∃ g : T → Ω → R,
      StronglyMeasurable (Function.uncurry g) ∧
      Integrable (Function.uncurry g) (μ.prod Q) ∧
      ∀ᵐ t ∂μ, g t =ᵐ[Q] F t := by
  borelize ↥(Lp R 2 Q)
  let V : Lp (Lp R 2 Q) 1 μ := (memLp_one_iff_integrable.mpr hF).toLp _
  have hVm : Measurable V := (Lp.stronglyMeasurable V).measurable
  let : TopologicalSpace.SeparableSpace (Set.range V ∪ {0} : Set (Lp R 2 Q)) :=
    StronglyMeasurable.separableSpace_range_union_singleton (Lp.stronglyMeasurable V)
  let S : ℕ → SimpleFunc T (Lp R 2 Q) := fun n =>
    SimpleFunc.approxOn V hVm (Set.range V ∪ {0}) 0 (by simp) n
  have hpoint (t : T) : Tendsto (fun n => S n t) atTop (𝓝 (V t)) :=
    SimpleFunc.tendsto_approxOn (s := Set.range V ∪ {0}) (y₀ := 0) (x := t)
      hVm (Set.mem_union_right _ (Set.mem_singleton 0))
      (subset_closure (Set.mem_union_left _ (Set.mem_range_self t)))
  have htime : Tendsto (fun n => simpleTimeLift μ Q (S n)) atTop (𝓝 V) := by
    have hv := SimpleFunc.tendsto_approxOn_range_Lp (p := 1) (by norm_num) hVm (Lp.memLp V)
    simpa only [simpleTimeLift, S, Lp.toLp_coeFn] using hv
  have hc : CauchySeq (fun n => simpleLift μ Q (S n)) := by
    have ht := htime.cauchySeq
    rw [cauchySeq_iff_tendsto_dist_atTop_0] at ht ⊢
    have hb (p : ℕ × ℕ) :
        dist (simpleLift μ Q (S p.1)) (simpleLift μ Q (S p.2)) ≤
          embeddingConstant Q * dist (simpleTimeLift μ Q (S p.1)) (simpleTimeLift μ Q (S p.2)) := by
      rw [simpleTimeLift_dist]
      exact simpleLift_dist_le μ Q (S p.1) (S p.2)
    have hz : Tendsto (fun p : ℕ × ℕ => embeddingConstant Q *
        dist (simpleTimeLift μ Q (S p.1)) (simpleTimeLift μ Q (S p.2))) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul ht)
    exact squeeze_zero (fun _ => dist_nonneg) hb hz
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hc
  have hm : TendstoInMeasure (μ.prod Q) (fun n => simpleRaw Q (S n)) atTop G := by
    apply TendstoInMeasure.congr (fun n => simpleLift_coe μ Q (S n)) Filter.EventuallyEq.rfl
    exact tendstoInMeasure_of_tendsto_Lp hG
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hrows : ∀ᵐ t ∂μ, ∀ᵐ ω ∂Q,
      Tendsto (fun n => S (ns n) t ω) atTop (𝓝 (G (t, ω))) :=
    Measure.ae_ae_of_ae_prod hae
  refine ⟨fun t ω => G (t, ω), Lp.stronglyMeasurable G,
    memLp_one_iff_integrable.mp (Lp.memLp G), ?_⟩
  filter_upwards [hrows, MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hF)] with t ht hFt
  have hLp : Tendsto (fun n => S (ns n) t) atTop (𝓝 (V t)) :=
    (hpoint t).comp hns.tendsto_atTop
  have hraw := tendstoInMeasure_of_tendsto_ae
    (fun n => (Lp.stronglyMeasurable (S (ns n) t)).aestronglyMeasurable) ht
  have heq := tendstoInMeasure_ae_unique hraw (tendstoInMeasure_of_tendsto_Lp hLp)
  exact heq.trans (by rw [hFt])


/-- A chosen actual joint representative, constructed through simple functions
and completion, for an arbitrary Bochner L¹ family of L² random variables. -/
def jointRepresentative (F : T → Lp R 2 Q) (hF : Integrable F μ) : T → Ω → R :=
  Classical.choose (exists_joint_representative μ Q F hF)

theorem jointRepresentative_stronglyMeasurable (F : T → Lp R 2 Q) (hF : Integrable F μ) :
    StronglyMeasurable (Function.uncurry (jointRepresentative μ Q F hF)) :=
  (Classical.choose_spec (exists_joint_representative μ Q F hF)).1

theorem jointRepresentative_integrable (F : T → Lp R 2 Q) (hF : Integrable F μ) :
    Integrable (Function.uncurry (jointRepresentative μ Q F hF)) (μ.prod Q) :=
  (Classical.choose_spec (exists_joint_representative μ Q F hF)).2.1

theorem jointRepresentative_section (F : T → Lp R 2 Q) (hF : Integrable F μ) :
    ∀ᵐ t ∂μ, jointRepresentative μ Q F hF t =ᵐ[Q] F t :=
  (Classical.choose_spec (exists_joint_representative μ Q F hF)).2.2

/-- All actual time-set integrals of the joint representative represent the
corresponding L² Bochner integrals. The exceptional spatial set may depend on
that time set; a simultaneous continuous version is a further process result. -/
theorem jointRepresentative_setIntegral (F : T → Lp R 2 Q) (hF : Integrable F μ)
    (s : Set T) :
    (∫ t in s, F t ∂μ) =ᵐ[Q]
      (fun ω => ∫ t in s, jointRepresentative μ Q F hF t ω ∂μ) := by
  apply LpIntegralSections.integral_coe_ae Q (μ.restrict s) F hF.integrableOn
    (jointRepresentative μ Q F hF)
  · exact (jointRepresentative_stronglyMeasurable μ Q F hF).aestronglyMeasurable.mono_measure
      (Measure.prod_mono Measure.restrict_le_self le_rfl)
  · exact ae_restrict_of_ae (jointRepresentative_section μ Q F hF)

end PBGSO.LpJointRepresentative
