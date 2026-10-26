import PBGSO.DyadicPastSamples
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Adapted

/-! # Genuine countable-horizon gluing of continuous process versions
Fixed-time identities on countably many dyadic points and path continuity
derive simultaneous overlap. The global process uses a deterministic horizon
larger than its current time, preserving actual adaptation.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace PBGSO.ContinuousVersionGlue

def gridTime (n k : ℕ) : ℝ≥0 := k / (2 : ℝ≥0) ^ n

def pastTime (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (DyadicInterpolation.leftTime (2 ^ n) (t : ℝ)).toNNReal

theorem pastTime_eq_grid (n : ℕ) (t : ℝ≥0) :
    pastTime n t = gridTime n (DyadicInterpolation.leftIndex (2 ^ n) (t : ℝ)) := by
  apply NNReal.eq
  change ((DyadicInterpolation.leftTime (2 ^ n) (t : ℝ)).toNNReal : ℝ) = _
  rw [Real.coe_toNNReal _ (DyadicInterpolation.leftTime_nonneg _ _)]
  simp only [gridTime, DyadicInterpolation.leftTime, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_pow, NNReal.coe_ofNat, Nat.cast_pow, Nat.cast_ofNat]

theorem pastTime_le (n : ℕ) (t : ℝ≥0) : pastTime n t ≤ t := by
  apply NNReal.coe_le_coe.mp
  rw [pastTime, Real.coe_toNNReal _ (DyadicInterpolation.leftTime_nonneg _ _)]
  exact DyadicInterpolation.leftTime_le _ (by positivity) _ t.coe_nonneg

theorem pastTime_tendsto (t : ℝ≥0) : Tendsto (fun n => pastTime n t) atTop (𝓝 t) := by
  have h := (continuous_real_toNNReal.tendsto (t : ℝ)).comp
    (DyadicInterpolation.leftTime_dyadic_tendsto _ t.coe_nonneg)
  simpa only [Real.toNNReal_coe, Function.comp_def, pastTime] using h

variable {R : Type*} [MetricSpace R]

/-- Continuous paths agreeing on the actual dyadic grid agree on every
point of their common closed horizon. -/
theorem eq_on_overlap_of_grid (u v : ℝ≥0 → R) (a b : ℝ≥0)
    (hu : ContinuousOn u (Iic a)) (hv : ContinuousOn v (Iic b))
    (hgrid : ∀ n k, gridTime n k ≤ a → gridTime n k ≤ b →
      u (gridTime n k) = v (gridTime n k))
    (t : ℝ≥0) (hta : t ≤ a) (htb : t ≤ b) : u t = v t := by
  have hseq (c : ℝ≥0) (htc : t ≤ c) :
      Tendsto (fun n => pastTime n t) atTop (𝓝[Iic c] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨pastTime_tendsto t,
      Filter.Eventually.of_forall (fun n => (pastTime_le n t).trans htc)⟩
  have hU := (hu t hta).tendsto.comp (hseq a hta)
  have hV := (hv t htb).tendsto.comp (hseq b htb)
  have he : ∀ n, u (pastTime n t) = v (pastTime n t) := by
    intro n
    rw [pastTime_eq_grid]
    exact hgrid _ _ (by rw [← pastTime_eq_grid]; exact (pastTime_le n t).trans hta)
      (by rw [← pastTime_eq_grid]; exact (pastTime_le n t).trans htb)
  exact tendsto_nhds_unique hU (hV.congr (fun n => (he n).symm))

def horizon (n : ℕ) : ℝ≥0 := n + 1

def horizonIndex (t : ℝ≥0) : ℕ := Nat.ceil (t : ℝ)

theorem horizon_exceeds (t : ℝ≥0) : t < horizon (horizonIndex t) := by
  change (t : ℝ) < (Nat.ceil (t : ℝ) : ℝ) + 1
  exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)

def globalVersion {Ω : Type*} (W : ℕ → ℝ≥0 → Ω → R) (t : ℝ≥0) (ω : Ω) : R :=
  W (horizonIndex t) t ω

variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
  (B : ℝ≥0 → Ω → R) (W : ℕ → ℝ≥0 → Ω → R)
  (hW : ∀ n t, t ≤ horizon n → W n t =ᵐ[Q] B t)
  (hc : ∀ n, ∀ᵐ ω ∂Q, ContinuousOn (fun t => W n t ω) (Iic (horizon n)))

include hW in
theorem globalVersion_ae (t : ℝ≥0) : globalVersion W t =ᵐ[Q] B t :=
  hW _ _ (horizon_exceeds t).le

include hW hc in
theorem ae_overlap : ∀ᵐ ω ∂Q, ∀ n m t,
    t ≤ horizon n → t ≤ horizon m → W n t ω = W m t ω := by
  have hgrid : ∀ᵐ ω ∂Q, ∀ n m i k,
      gridTime i k ≤ horizon n → gridTime i k ≤ horizon m →
      W n (gridTime i k) ω = W m (gridTime i k) ω := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro k
    by_cases hn : gridTime i k ≤ horizon n
    · by_cases hm : gridTime i k ≤ horizon m
      · exact ((hW n _ hn).trans (hW m _ hm).symm).mono (fun ω he _ _ => he)
      · exact Filter.Eventually.of_forall (fun _ _ he => False.elim (hm he))
    · exact Filter.Eventually.of_forall (fun _ he _ => False.elim (hn he))
  filter_upwards [hgrid, ae_all_iff.mpr hc] with ω hg hcont
  intro n m t htn htm
  exact eq_on_overlap_of_grid (fun s => W n s ω) (fun s => W m s ω)
    _ _ (hcont n) (hcont m) (hg n m) t htn htm

include hW hc in
theorem globalVersion_continuous : ∀ᵐ ω ∂Q, Continuous (fun t => globalVersion W t ω) := by
  filter_upwards [ae_overlap Q B W hW hc, ae_all_iff.mpr hc] with ω he hcont
  have hg (n : ℕ) : ContinuousOn (fun t => globalVersion W t ω) (Iic (horizon n)) := by
    apply (hcont n).congr
    intro t ht
    exact he (horizonIndex t) n t (horizon_exceeds t).le ht
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hg (horizonIndex t) t (horizon_exceeds t).le).continuousAt
    (Iic_mem_nhds (horizon_exceeds t))

theorem globalVersion_stronglyAdapted (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hA : ∀ n, StronglyAdapted F (W n)) : StronglyAdapted F (globalVersion W) :=
  fun t => hA (horizonIndex t) t

end PBGSO.ContinuousVersionGlue
