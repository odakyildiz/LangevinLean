import PBGSO.LpContinuousVersion
import PBGSO.AdditiveWeakRealization
import PBGSO.IntegralAdaptation

/-! # Continuous path realization of the actual additive mean-field solution

Only the raw additive input's actual joint measurability, per-time L² identity
and almost-sure path continuity are additional. The primitive force bounds,
actual complete integral equation and continuous optimiser derive all drift
regularity/realization inputs to the path-version theorem.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace PBGSO
variable {Ω A Z G : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

theorem LipschitzDynamics.sampler_uncurry_lipschitz (L : LipschitzDynamics A Z G) :
    LipschitzWith (2 * L.samplerLip) (Function.uncurry L.sampler) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [dist_eq_norm]
  have hp := L.sampler_parameter p.1 q.1 p.2
  have hx := (L.sampler_state q.1).norm_sub_le p.2 q.2
  have hs := norm_sub_le_norm_sub_add_norm_sub
    (L.sampler p.1 p.2) (L.sampler q.1 p.2) (L.sampler q.1 q.2)
  have ho : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
  have hz : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
  change ‖L.sampler p.1 p.2 - L.sampler q.1 q.2‖ ≤ (2 * (L.samplerLip : ℝ)) * ‖p - q‖
  nlinarith [mul_le_mul_of_nonneg_left ho L.samplerLip.coe_nonneg,
    mul_le_mul_of_nonneg_left hz L.samplerLip.coe_nonneg]

/-- A simultaneous continuous sampler version of the actual constructed
mean-field integral trajectory. The literal sampler drift and original input
appear in the pathwise equation, on one full-measure event for all horizon
times. No jointly measurable drift version is an input. -/
theorem IsGlobalAdditiveIntegralSolution.exists_continuous_sampler_version
    (L : LipschitzDynamics A Z G) (Y : ℝ → A × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q)
    (HY : IsGlobalAdditiveIntegralSolution Q L Y B)
    (T : ℝ) (hT : 0 ≤ T) (b : ℝ → Ω → Z)
    (hb : StronglyMeasurable (Function.uncurry b))
    (hbEq : ∀ t ∈ Icc 0 T, b t =ᵐ[Q] B t)
    (hbCont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => b t ω) (Icc 0 T)) :
    ∃ u : ℝ → Ω → Z,
      StronglyMeasurable (Function.uncurry u) ∧
      (∀ t ∈ Icc 0 T, u t =ᵐ[Q] (Y t).2) ∧
      ∀ᵐ ω ∂Q,
        ContinuousOn (fun t => u t ω) (Icc 0 T) ∧
        u 0 ω = (Y 0).2 ω ∧
        ∀ t ∈ Icc 0 T,
          u t ω - u 0 ω = (∫ s in 0..t, L.sampler (Y s).1 (u s ω)) + b t ω := by
  let F : ℝ → Lp Z 2 Q := fun t => (L.field Q (Y t)).2
  have hFcont : Continuous F := ((L.field_lipschitz Q).continuous.comp HY.continuous).snd
  have hFi : IntegrableOn F (Icc 0 T) := hFcont.integrableOn_Icc
  have hf : Continuous (fun p : ℝ × Z => L.sampler (Y p.1).1 p.2) :=
    L.sampler_uncurry_lipschitz.continuous.comp
      ((HY.continuous.fst.comp continuous_fst).prodMk continuous_snd)
  have hfield (t : ℝ) (_ht : t ∈ Icc 0 T) :
      F t =ᵐ[Q] (fun ω => L.sampler (Y t).1 ((Y t).2 ω)) :=
    liftMap_coe Q (L.sampler (Y t).1) (L.sampler_state (Y t).1) (Y t).2
  have heq (t : ℝ) (ht : t ∈ Icc 0 T) :
      (Y t).2 - (Y 0).2 = (∫ s in 0..t, F s) + B t := by
    let sndL : A × Lp Z 2 Q →L[ℝ] Lp Z 2 Q := ContinuousLinearMap.snd ℝ A (Lp Z 2 Q)
    have hi : IntervalIntegrable (fun s => L.field Q (Y s)) volume 0 t :=
      ((L.field_lipschitz Q).continuous.comp HY.continuous).intervalIntegrable 0 t
    have hh := congrArg sndL (HY.equation t ht.1)
    rw [map_sub, map_add, ← sndL.intervalIntegral_comp_comm hi] at hh
    exact hh
  exact LpContinuousVersion.exists_continuous_integral_version Q T hT
    (fun t => (Y t).2) F B hFi b hb hbEq hbCont
    (fun t z => L.sampler (Y t).1 z) hf hfield heq
end PBGSO
