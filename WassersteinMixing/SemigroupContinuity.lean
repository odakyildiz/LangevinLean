import WassersteinMixing.Semigroup
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Strong continuity of stationary observable evaluations

Continuity of the underlying random state in `L²`, together with its common
stationary law, implies strong continuity for every target `L²` observable.
Bounded continuous observables are handled by a subsequence and dominated
convergence argument; density and the evaluation isometries give the full result.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace WassersteinMixing.StationaryObservables

variable {𝕜 E F Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  (μ : Measure E) (Q : Measure Ω)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- A proved vanishing mean coupling distance gives convergence in measure.
This applies directly to the actual MALA rejection estimate. -/
theorem tendstoInMeasure_of_integral_norm_sub {I : Type*} {l : Filter I}
    (X : I → Ω → E) (Y : Ω → E)
    (hint : ∀ i, Integrable (fun ω ↦ X i ω - Y ω) Q)
    (hlim : Tendsto (fun i ↦ ∫ ω, ‖X i ω - Y ω‖ ∂Q) l (𝓝 0)) :
    TendstoInMeasure Q X l Y := by
  have heq (i : I) : eLpNorm (X i - Y) 1 Q =
      ENNReal.ofReal (∫ ω, ‖X i ω - Y ω‖ ∂Q) := by
    change eLpNorm (fun ω ↦ X i ω - Y ω) 1 Q = _
    rw [eLpNorm_one_eq_lintegral_enorm (hint i).aestronglyMeasurable,
      ofReal_integral_norm_eq_lintegral_enorm (hint i)]
  have he : Tendsto (fun i ↦ eLpNorm (X i - Y) 1 Q) l (𝓝 0) := by
    simpa only [heq, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto 0 |>.comp hlim
  exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) he

/-- Evaluation of observables at a random state with the exact target law. -/
def evaluation (X : Lp E 2 Q) (hX : Q.map X = μ) : Lp F 2 μ →ₗᵢ[𝕜] Lp F 2 Q :=
  Lp.compMeasurePreservingₗᵢ 𝕜 X ⟨(Lp.stronglyMeasurable X).measurable, hX⟩

include 𝕜 in
omit [CompleteSpace F] in
/-- Parseval's integral identity for the norm of an actual `L²` vector. -/
theorem lp_norm_sq_eq_integral (Z : Lp F 2 Q) :
    ‖Z‖ ^ 2 = ∫ ω, ‖Z ω‖ ^ 2 ∂Q := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def]
  change (RCLike.reCLM : 𝕜 →L[ℝ] ℝ) (∫ a, inner 𝕜 (Z a) (Z a) ∂Q) = _
  rw [← (RCLike.reCLM : 𝕜 →L[ℝ] ℝ).integral_comp_comm (L2.integrable_inner Z Z)]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω ↦ (norm_sq_eq_re_inner (𝕜 := 𝕜) (Z ω)).symm

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]

omit [CompleteSpace F] [IsProbabilityMeasure Q] in
private theorem evaluation_bcf_coe (X : Lp E 2 Q) (hX : Q.map X = μ)
    (φ : E →ᵇ F) :
    evaluation (𝕜 := 𝕜) μ Q X hX (BoundedContinuousFunction.toLp 2 μ 𝕜 φ)
      =ᵐ[Q] fun ω ↦ φ (X ω) := by
  have hx : MeasurePreserving X Q μ := ⟨(Lp.stronglyMeasurable X).measurable, hX⟩
  exact (Lp.coeFn_compMeasurePreserving _ hx).trans
    (hx.quasiMeasurePreserving.ae_eq_comp (BoundedContinuousFunction.coeFn_toLp 2 μ 𝕜 φ))

omit [CompleteSpace F] [IsProbabilityMeasure Q] in
private theorem evaluation_bcf_norm_sq (X Y : Lp E 2 Q)
    (hX : Q.map X = μ) (hY : Q.map Y = μ) (φ : E →ᵇ F) :
    ‖evaluation (𝕜 := 𝕜) μ Q X hX (BoundedContinuousFunction.toLp 2 μ 𝕜 φ) -
      evaluation (𝕜 := 𝕜) μ Q Y hY (BoundedContinuousFunction.toLp 2 μ 𝕜 φ)‖ ^ 2 =
      ∫ ω, ‖φ (X ω) - φ (Y ω)‖ ^ 2 ∂Q := by
  rw [lp_norm_sq_eq_integral (𝕜 := 𝕜) Q]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub
    (evaluation (𝕜 := 𝕜) μ Q X hX (BoundedContinuousFunction.toLp 2 μ 𝕜 φ))
    (evaluation (𝕜 := 𝕜) μ Q Y hY (BoundedContinuousFunction.toLp 2 μ 𝕜 φ)),
    evaluation_bcf_coe (𝕜 := 𝕜) μ Q X hX φ,
    evaluation_bcf_coe (𝕜 := 𝕜) μ Q Y hY φ] with ω hsub hx hy
  simp only [hsub, Pi.sub_apply, hx, hy]

omit [CompleteSpace F] in
/-- Strong convergence of the states gives strong convergence of every
bounded continuous observable, without any global uniform-continuity assumption. -/
theorem evaluation_bcf_tendsto_inMeasure {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (X : I → Lp E 2 Q) (Y : Lp E 2 Q) (hX : ∀ i, Q.map (X i) = μ)
    (hY : Q.map Y = μ)
    (hlim : TendstoInMeasure Q (fun i ω ↦ X i ω) l Y) (φ : E →ᵇ F) :
    Tendsto (fun i ↦ evaluation (𝕜 := 𝕜) μ Q (X i) (hX i)
      (BoundedContinuousFunction.toLp 2 μ 𝕜 φ)) l
      (𝓝 (evaluation (𝕜 := 𝕜) μ Q Y hY (BoundedContinuousFunction.toLp 2 μ 𝕜 φ))) := by
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
  have hn : Tendsto (fun n ↦ ‖evaluation (𝕜 := 𝕜) μ Q (X (ns (ms n))) (hX _)
      (BoundedContinuousFunction.toLp 2 μ 𝕜 φ) -
      evaluation (𝕜 := 𝕜) μ Q Y hY (BoundedContinuousFunction.toLp 2 μ 𝕜 φ)‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [evaluation_bcf_norm_sq, integral_zero] using hi
  have hs := (Real.continuous_sqrt.tendsto 0).comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

omit [CompleteSpace F] in
/-- Stationarity and state continuity imply strong continuity for every `L²`
observable. No regularity or boundedness assumption on the observable remains. -/
theorem evaluation_tendsto_inMeasure [NormedSpace ℝ F] [μ.WeaklyRegular] {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (X : I → Lp E 2 Q) (Y : Lp E 2 Q)
    (hX : ∀ i, Q.map (X i) = μ) (hY : Q.map Y = μ)
    (hlim : TendstoInMeasure Q (fun i ω ↦ X i ω) l Y) (f : Lp F 2 μ) :
    Tendsto (fun i ↦ evaluation (𝕜 := 𝕜) μ Q (X i) (hX i) f) l
      (𝓝 (evaluation (𝕜 := 𝕜) μ Q Y hY f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hdense : DenseRange (BoundedContinuousFunction.toLp 2 μ 𝕜 :
      (E →ᵇ F) →L[𝕜] Lp F 2 μ) :=
    BoundedContinuousFunction.toLp_denseRange F μ 𝕜 (by norm_num)
  obtain ⟨φ, hφ⟩ := hdense.exists_dist_lt f (by linarith : 0 < ε / 3)
  have ht := evaluation_bcf_tendsto_inMeasure (𝕜 := 𝕜) μ Q X Y hX hY hlim φ
  have he := (Metric.tendsto_nhds.mp ht) (ε / 3) (by linarith)
  filter_upwards [he] with i hi
  let φLp := BoundedContinuousFunction.toLp 2 μ 𝕜 φ
  let ex := evaluation (𝕜 := 𝕜) (F := F) μ Q (X i) (hX i)
  let ey := evaluation (𝕜 := 𝕜) (F := F) μ Q Y hY
  have htri : dist (ex f) (ey f) ≤
      dist f φLp + dist (ex φLp) (ey φLp) + dist φLp f := by
    calc
      _ ≤ dist (ex f) (ex φLp) + dist (ex φLp) (ey f) := dist_triangle _ _ _
      _ ≤ dist (ex f) (ex φLp) +
          (dist (ex φLp) (ey φLp) + dist (ey φLp) (ey f)) :=
        by linarith [dist_triangle (ex φLp) (ey φLp) (ey f)]
      _ = _ := by rw [ex.isometry.dist_eq, ey.isometry.dist_eq]; ring
  change dist (ex f) (ey f) < ε
  change dist (ex φLp) (ey φLp) < ε / 3 at hi
  change dist f φLp < ε / 3 at hφ
  rw [dist_comm φLp f] at htri
  linarith

omit [CompleteSpace F] in
/-- `L²` state convergence is a sufficient special case of convergence in measure. -/
theorem evaluation_bcf_tendsto {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (X : I → Lp E 2 Q) (Y : Lp E 2 Q) (hX : ∀ i, Q.map (X i) = μ)
    (hY : Q.map Y = μ) (hlim : Tendsto X l (𝓝 Y)) (φ : E →ᵇ F) :
    Tendsto (fun i ↦ evaluation (𝕜 := 𝕜) μ Q (X i) (hX i)
      (BoundedContinuousFunction.toLp 2 μ 𝕜 φ)) l
      (𝓝 (evaluation (𝕜 := 𝕜) μ Q Y hY (BoundedContinuousFunction.toLp 2 μ 𝕜 φ))) :=
  evaluation_bcf_tendsto_inMeasure μ Q X Y hX hY (tendstoInMeasure_of_tendsto_Lp hlim) φ

omit [CompleteSpace F] in
/-- `L²` continuity of stationary states implies strong observable continuity. -/
theorem evaluation_tendsto [NormedSpace ℝ F] [μ.WeaklyRegular] {I : Type*} {l : Filter I}
    [l.IsCountablyGenerated] (X : I → Lp E 2 Q) (Y : Lp E 2 Q)
    (hX : ∀ i, Q.map (X i) = μ) (hY : Q.map Y = μ)
    (hlim : Tendsto X l (𝓝 Y)) (f : Lp F 2 μ) :
    Tendsto (fun i ↦ evaluation (𝕜 := 𝕜) μ Q (X i) (hX i) f) l
      (𝓝 (evaluation (𝕜 := 𝕜) μ Q Y hY f)) :=
  evaluation_tendsto_inMeasure μ Q X Y hX hY (tendstoInMeasure_of_tendsto_Lp hlim) f

end WassersteinMixing.StationaryObservables
