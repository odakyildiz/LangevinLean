import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod

set_option linter.style.header false

/-! # Metropolis invariance by accepted-flow symmetry

The accepted joint measure has equal first and second marginals by detailed
balance. The rejected measure stays at its first coordinate. Their sum
therefore preserves the initial marginal. This is a measure identity, with
no infinitesimal-invariance or forward-equation uniqueness premise.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace ULA

variable {H : Type*} [MeasurableSpace H]

def acceptedFlow (ν : Measure (H × H)) (a : H × H → ℝ) : Measure (H × H) :=
  ν.withDensity (fun p ↦ ENNReal.ofReal (a p))

def rejectedFlow (ν : Measure (H × H)) (a : H × H → ℝ) : Measure (H × H) :=
  ν.withDensity (fun p ↦ ENNReal.ofReal (1 - a p))

def metropolisOutput (ν : Measure (H × H)) (a : H × H → ℝ) : Measure H :=
  (acceptedFlow ν a).map Prod.snd + (rejectedFlow ν a).map Prod.fst

theorem acceptedFlow_add_rejectedFlow (ν : Measure (H × H)) (a : H × H → ℝ)
    (ha : Measurable a) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1) :
    acceptedFlow ν a + rejectedFlow ν a = ν := by
  unfold acceptedFlow rejectedFlow
  rw [← withDensity_add_left ha.ennreal_ofReal]
  have hw : (fun p ↦ ENNReal.ofReal (a p) + ENNReal.ofReal (1 - a p)) = 1 := by
    funext p
    rw [← ENNReal.ofReal_add (ha0 p) (sub_nonneg.mpr (ha1 p))]
    simp
  change ν.withDensity (fun p ↦ ENNReal.ofReal (a p) + ENNReal.ofReal (1 - a p)) = ν
  rw [hw, withDensity_one]

theorem marginals_eq_of_swap_invariant (ν : Measure (H × H))
    (hsym : ν.map Prod.swap = ν) : ν.map Prod.snd = ν.map Prod.fst := by
  calc
    ν.map Prod.snd = (ν.map Prod.swap).map Prod.fst := by
      rw [Measure.map_map measurable_fst measurable_swap]
      rfl
    _ = ν.map Prod.fst := by rw [hsym]

/-- Detailed balance of the accepted flow implies exact invariance of the
Metropolis step, with all rejection mass retained at the current state. -/
theorem metropolisOutput_eq_initial (ν : Measure (H × H)) (a : H × H → ℝ)
    (ha : Measurable a) (ha0 : ∀ p, 0 ≤ a p) (ha1 : ∀ p, a p ≤ 1)
    (hbalance : (acceptedFlow ν a).map Prod.swap = acceptedFlow ν a) :
    metropolisOutput ν a = ν.map Prod.fst := by
  rw [metropolisOutput, marginals_eq_of_swap_invariant _ hbalance,
    ← Measure.map_add _ _ measurable_fst,
    acceptedFlow_add_rejectedFlow ν a ha ha0 ha1]

/-- A weight depending only on a measurable image commutes with pushforward. -/
theorem map_weighted_comp {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (f : A → B) (hf : Measurable f)
    (w : B → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, ← lintegral_indicator (hf hs),
    ← lintegral_indicator hs, lintegral_map (hw.indicator hs) hf]
  apply lintegral_congr
  intro a
  rfl

/-- Densities commute with an explicit measurable change of coordinates. -/
theorem map_weighted_comp_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (e : A ≃ᵐ B) (w : B → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (w ∘ e)).map e = (μ.map e).withDensity w :=
  map_weighted_comp μ e e.measurable w hw

def metropolisAcceptance (w : H × H → ℝ) (p : H × H) : ℝ :=
  min 1 (w p.swap / w p)

theorem weight_mul_metropolisAcceptance (w : H × H → ℝ) (hw : ∀ p, 0 < w p)
    (p : H × H) : w p * metropolisAcceptance w p = min (w p) (w p.swap) := by
  rw [metropolisAcceptance, mul_min_of_nonneg 1 (w p.swap / w p) (hw p).le, mul_one]
  congr 1
  field_simp [(hw p).ne']

/-- The accepted flow has the symmetric density min(w(x,y),w(y,x)). -/
theorem acceptedFlow_density (base : Measure (H × H)) (w : H × H → ℝ)
    (hw : Measurable w) (hw0 : ∀ p, 0 < w p) :
    acceptedFlow (base.withDensity (fun p ↦ ENNReal.ofReal (w p)))
        (metropolisAcceptance w) =
      base.withDensity (fun p ↦ ENNReal.ofReal (min (w p) (w p.swap))) := by
  have ha : Measurable (metropolisAcceptance w) := by
    exact measurable_const.min ((hw.comp measurable_swap).div hw)
  unfold acceptedFlow
  rw [← withDensity_mul base hw.ennreal_ofReal ha.ennreal_ofReal]
  congr 1
  funext p
  change ENNReal.ofReal (w p) * ENNReal.ofReal (metropolisAcceptance w p) = _
  rw [← ENNReal.ofReal_mul (hw0 p).le, weight_mul_metropolisAcceptance w hw0 p]

/-- For a symmetric base measure and positive proposal-joint density, the
ordinary Metropolis ratio proves detailed balance and exact invariance. -/
theorem metropolisOutput_density_eq_initial
    (base : Measure (H × H)) (hbase : base.map Prod.swap = base)
    (w : H × H → ℝ) (hw : Measurable w) (hw0 : ∀ p, 0 < w p) :
    metropolisOutput (base.withDensity (fun p ↦ ENNReal.ofReal (w p)))
      (metropolisAcceptance w) =
        (base.withDensity (fun p ↦ ENNReal.ofReal (w p))).map Prod.fst := by
  have ha : Measurable (metropolisAcceptance w) :=
    measurable_const.min ((hw.comp measurable_swap).div hw)
  apply metropolisOutput_eq_initial _ _ ha
    (fun p ↦ le_min (by norm_num) (div_pos (hw0 p.swap) (hw0 p)).le)
    (fun _ ↦ min_le_left _ _)
  rw [acceptedFlow_density base w hw hw0]
  let v : H × H → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (min (w p) (w p.swap))
  have hv : Measurable v := (hw.min (hw.comp measurable_swap)).ennreal_ofReal
  have hs : v ∘ (MeasurableEquiv.prodComm : (H × H) ≃ᵐ (H × H)) = v := by
    funext p
    change ENNReal.ofReal (min (w p.swap) (w p.swap.swap)) =
      ENNReal.ofReal (min (w p) (w p.swap))
    rw [Prod.swap_swap, min_comm]
  have hm := map_weighted_comp_equiv base
    (MeasurableEquiv.prodComm : (H × H) ≃ᵐ (H × H)) v hv
  change (base.withDensity (v ∘ (MeasurableEquiv.prodComm : (H × H) ≃ᵐ (H × H)))).map Prod.swap =
    (base.map Prod.swap).withDensity v at hm
  rw [hs, hbase] at hm
  exact hm

end ULA
