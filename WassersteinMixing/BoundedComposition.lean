import WassersteinMixing.SemigroupContinuity

/-! # Bounded observable composition without a stationary approximation law

Euler states need not have the target law. Bounded continuous observables
nevertheless converge in `L²` when the states converge in measure, by a
subsequence and dominated-convergence argument.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction
namespace WassersteinMixing

variable {𝕜 E H Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
  [NormedAddCommGroup E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- Actual bounded observable composition at an arbitrary square-integrable
state; no stationary law is required. -/
def boundedComposition (X : Lp E 2 Q) (φ : E →ᵇ H) : Lp H 2 Q :=
  (MemLp.of_bound (φ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable X))
    ‖φ‖ (Eventually.of_forall fun ω ↦ φ.norm_coe_le_norm (X ω))).toLp (fun ω ↦ φ (X ω))

theorem boundedComposition_coe (X : Lp E 2 Q) (φ : E →ᵇ H) :
    boundedComposition Q X φ =ᵐ[Q] fun ω ↦ φ (X ω) :=
  MemLp.coeFn_toLp _

include 𝕜 in
private theorem boundedComposition_sub_norm_sq (X Y : Lp E 2 Q) (φ : E →ᵇ H) :
    ‖boundedComposition Q X φ - boundedComposition Q Y φ‖ ^ 2 =
      ∫ ω, ‖φ (X ω) - φ (Y ω)‖ ^ 2 ∂Q := by
  rw [StationaryObservables.lp_norm_sq_eq_integral (𝕜 := 𝕜) Q]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (boundedComposition Q X φ) (boundedComposition Q Y φ),
    boundedComposition_coe Q X φ, boundedComposition_coe Q Y φ] with ω hsub hx hy
  simp only [hsub, Pi.sub_apply, hx, hy]

include 𝕜 in
/-- Convergence in measure of arbitrary states gives strong `L²` convergence
of every bounded continuous observable. -/
theorem boundedComposition_tendsto_inMeasure {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (X : I → Lp E 2 Q) (Y : Lp E 2 Q)
    (hlim : TendstoInMeasure Q (fun i ω ↦ X i ω) l Y) (φ : E →ᵇ H) :
    Tendsto (fun i ↦ boundedComposition Q (X i) φ) l (𝓝 (boundedComposition Q Y φ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hae⟩ := (hlim.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hmeas : ∀ᶠ n : ℕ in atTop,
      AEStronglyMeasurable (fun ω ↦ ‖φ (X (ns (ms n)) ω) - φ (Y ω)‖ ^ 2) Q := by
    exact Eventually.of_forall fun n ↦
      ((φ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)).sub
        (φ.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable _))).norm.pow 2
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂Q,
      ‖‖φ (X (ns (ms n)) ω) - φ (Y ω)‖ ^ 2‖ ≤ (2 * ‖φ‖) ^ 2 := by
    exact Eventually.of_forall fun n ↦ Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have ht := (norm_sub_le (φ (X (ns (ms n)) ω)) (φ (Y ω))).trans
        (add_le_add (φ.norm_coe_le_norm _) (φ.norm_coe_le_norm _))
      exact pow_le_pow_left₀ (norm_nonneg _) (by linarith [ht]) 2
  have hpoint : ∀ᵐ ω ∂Q, Tendsto
      (fun n ↦ ‖φ (X (ns (ms n)) ω) - φ (Y ω)‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hae] with ω hω
    simpa only [Function.comp_def, sub_self, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (((φ.continuous.tendsto (Y ω)).comp hω).sub_const (φ (Y ω))).norm.pow 2
  have hi := tendsto_integral_filter_of_dominated_convergence
    (fun _ : Ω ↦ (2 * ‖φ‖) ^ 2) hmeas hbound (integrable_const _) hpoint
  have hn : Tendsto (fun n ↦ ‖boundedComposition Q (X (ns (ms n))) φ -
      boundedComposition Q Y φ‖ ^ 2) atTop (𝓝 0) := by
    simpa only [boundedComposition_sub_norm_sq (𝕜 := 𝕜), integral_zero] using hi
  have hs := (Real.continuous_sqrt.tendsto 0).comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

include 𝕜 in
/-- Strong state convergence is a sufficient special case. -/
theorem boundedComposition_tendsto {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (X : I → Lp E 2 Q) (Y : Lp E 2 Q) (hlim : Tendsto X l (𝓝 Y)) (φ : E →ᵇ H) :
    Tendsto (fun i ↦ boundedComposition Q (X i) φ) l (𝓝 (boundedComposition Q Y φ)) :=
  boundedComposition_tendsto_inMeasure (𝕜 := 𝕜) Q X Y (tendstoInMeasure_of_tendsto_Lp hlim) φ

end WassersteinMixing
