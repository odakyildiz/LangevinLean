import PBGSO.MartingaleUniformLimit
import PBGSO.MartingaleCountableMaximal
import Mathlib.Analysis.Normed.Group.Completeness

/-! # Continuous martingale versions from actual L² convergence
Doob's countable maximal inequality and a fast terminal-L² subsequence
supply the summable tail probabilities required by Borel-Cantelli.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.ContinuousMartingaleCompletion
variable {Ω H : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ℝ≥0 mΩ)

abbrev Window (T : ℝ≥0) := Set.Iic T

/-- An actual square-integrable martingale obeys the dense-observation
maximal bound in norm form. The terminal energy bound is the sole input. -/
theorem maximal_norm_measure_le (X : ℝ≥0 → Ω → H) (hX : Martingale X F Q)
    (h2 : ∀ t, MemLp (X t) 2 Q) (τ : ℕ → ℝ≥0) (T : ℝ≥0) (hτ : ∀ n, τ n ≤ T)
    (δ b : ℝ) (hδ : 0 < δ) (_hb : 0 ≤ b)
    (hE : (∫ ω, ‖X T ω‖ ^ 2 ∂Q) ≤ δ ^ 2 * b) :
    Q {ω | ∃ n, δ ≤ ‖X (τ n) ω‖} ≤ ENNReal.ofReal b := by
  let a : ℝ≥0 := ⟨δ ^ 2, sq_nonneg δ⟩
  have hm := MartingaleMaximalL2.maximal_countable Q F X hX h2 τ T hτ a
  have he : {ω | ∃ n, δ ≤ ‖X (τ n) ω‖} = {ω | ∃ n, (a : ℝ) ≤ ‖X (τ n) ω‖ ^ 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    apply exists_congr
    intro n
    exact (sq_le_sq₀ hδ.le (norm_nonneg _)).symm
  have ha : (a : ℝ≥0∞) = ENNReal.ofReal (δ ^ 2) := ENNReal.coe_nnreal_eq a
  rw [ha, ← he] at hm
  apply (ENNReal.mul_le_mul_iff_left (by positivity : ENNReal.ofReal (δ ^ 2) ≠ 0)
    ENNReal.ofReal_ne_top).mp
  calc
    Q {ω | ∃ n, δ ≤ ‖X (τ n) ω‖} * ENNReal.ofReal (δ ^ 2) =
      ENNReal.ofReal (δ ^ 2) * Q {ω | ∃ n, δ ≤ ‖X (τ n) ω‖} := mul_comm _ _
    _ ≤ ENNReal.ofReal (∫ ω, ‖X T ω‖ ^ 2 ∂Q) := hm
    _ ≤ ENNReal.ofReal (δ ^ 2 * b) := ENNReal.ofReal_le_ofReal hE
    _ = ENNReal.ofReal b * ENNReal.ofReal (δ ^ 2) := by
      rw [ENNReal.ofReal_mul (sq_nonneg δ), mul_comm]

/-- Summable terminal-L² difference bounds imply uniform convergence and
continuous limit paths on the full time interval, not merely at sampled times. -/
theorem ae_uniform_of_terminal_bounds (f : ℕ → ℝ≥0 → Ω → H)
    (hf : ∀ n, Martingale (f n) F Q) (h2 : ∀ n t, MemLp (f n t) 2 Q)
    (T : ℝ≥0) (δ b : ℕ → ℝ) (hδ : ∀ n, 0 < δ n) (hsδ : Summable δ)
    (hb : ∀ n, 0 ≤ b n) (hsb : Summable b)
    (hE : ∀ n, (∫ ω, ‖f (n + 1) T ω - f n T ω‖ ^ 2 ∂Q) ≤ (δ n) ^ 2 * b n)
    (hc : ∀ᵐ ω ∂Q, ∀ n, Continuous (fun t => f n t ω)) :
    ∀ᵐ ω ∂Q, TendstoUniformly (fun n (t : Window T) => f n t.val ω)
      (fun t => MartingaleUniformLimit.seriesLimit (fun n (t : Window T) => f n t.val) t ω) atTop ∧
      Continuous (fun t : Window T =>
        MartingaleUniformLimit.seriesLimit (fun n (t : Window T) => f n t.val) t ω) := by
  letI : Nonempty (Window T) := ⟨⟨0, by change (0 : ℝ≥0) ≤ T; exact zero_le⟩⟩
  obtain ⟨τ, hτ⟩ := TopologicalSpace.exists_dense_seq (Window T)
  have hm (n : ℕ) :
      Q {ω | ∃ t ∈ Set.range τ, δ n ≤ ‖f (n + 1) t.val ω - f n t.val ω‖} ≤ ENNReal.ofReal (b n) := by
    have hd := maximal_norm_measure_le Q F (f (n + 1) - f n) ((hf (n + 1)).sub (hf n))
      (fun t => (h2 (n + 1) t).sub (h2 n t)) (fun k => (τ k).val) T (fun k => (τ k).property)
      (δ n) (b n) (hδ n) (hb n) (hE n)
    convert hd using 2
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_range, Pi.sub_apply]
    aesop
  have hbad : (∑' n, Q {ω | ∃ t ∈ Set.range τ, δ n ≤ ‖f (n + 1) t.val ω - f n t.val ω‖}) ≠ ∞ :=
    ne_top_of_le_ne_top hsb.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hm)
  exact MartingaleUniformLimit.ae_uniform_seriesLimit Q (fun n (t : Window T) => f n t.val)
    (Set.range τ) hτ δ hsδ hbad (hc.mono (fun ω hω n => (hω n).comp continuous_subtype_val))

/-- Terminal L² Cauchy convergence alone supplies a fast subsequence with a
simultaneous continuous uniformly convergent sample-path limit. -/
theorem exists_uniform_subsequence (f : ℕ → ℝ≥0 → Ω → H)
    (hf : ∀ n, Martingale (f n) F Q) (h2 : ∀ n t, MemLp (f n t) 2 Q)
    (T : ℝ≥0) (hcau : CauchySeq (fun n => (h2 n T).toLp (f n T)))
    (hc : ∀ᵐ ω ∂Q, ∀ n, Continuous (fun t => f n t ω)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂Q, TendstoUniformly (fun n (t : Window T) => f (φ n) t.val ω)
        (fun t => MartingaleUniformLimit.seriesLimit (fun n (t : Window T) => f (φ n) t.val) t ω) atTop ∧
        Continuous (fun t : Window T =>
          MartingaleUniformLimit.seriesLimit (fun n (t : Window T) => f (φ n) t.val) t ω) := by
  obtain ⟨φ, hφ, hdist⟩ := Metric.exists_subseq_bounded_of_cauchySeq
    (fun n => (h2 n T).toLp (f n T)) hcau (fun n => (1 / (4 : ℝ)) ^ n) (fun n => by positivity)
  refine ⟨φ, hφ, ?_⟩
  apply ae_uniform_of_terminal_bounds Q F (fun n => f (φ n)) (fun n => hf (φ n))
    (fun n t => h2 (φ n) t) T (fun n => (1 / (2 : ℝ)) ^ n) (fun n => (1 / (4 : ℝ)) ^ n)
    (fun n => by positivity) summable_geometric_two (fun n => by positivity)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  · intro n
    let A := (h2 (φ (n + 1)) T).toLp (f (φ (n + 1)) T)
    let B := (h2 (φ n) T).toLp (f (φ n) T)
    have he : (∫ ω, ‖f (φ (n + 1)) T ω - f (φ n) T ω‖ ^ 2 ∂Q) = ‖A - B‖ ^ 2 := by
      rw [ProximalLangevin.lp_norm_sq_eq_integral]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub A B, (h2 (φ (n + 1)) T).coeFn_toLp,
        (h2 (φ n) T).coeFn_toLp] with ω hab ha hb
      change A ω = _ at ha
      change B ω = _ at hb
      rw [hab, Pi.sub_apply, ha, hb]
    rw [he]
    have hd := (hdist n (φ (n + 1)) (hφ.monotone (Nat.le_succ n))).le
    rw [dist_eq_norm] at hd
    have hp : ((1 / (2 : ℝ)) ^ n) ^ 2 = (1 / (4 : ℝ)) ^ n := by
      rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    rw [hp]
    exact (pow_le_pow_left₀ (norm_nonneg _) hd 2).trans_eq (pow_two _)
  · exact hc.mono (fun ω hω n => hω (φ n))

end PBGSO.ContinuousMartingaleCompletion
