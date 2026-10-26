import PBGSO.IntegralModulus

/-! # Finite-horizon regularity uniform over the numerical mesh

The state and actual drift radii are derived from compactness of the continuous
integral trajectory. Brownian increments then give one square-root modulus for
all subintervals of length at most one in the fixed horizon. These constants
are independent of the number and width of the mesh intervals; no moment or
modulus inequality is supplied as a process hypothesis.
-/
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO

variable {Ω I E : Type*} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (Q : Measure Ω)

/-- Actual Brownian-driven integral trajectories have mesh-uniform state,
drift and square-root increment bounds on any fixed finite horizon. -/
theorem exists_brownian_mesh_regularity
    (f : Lp E 2 Q → Lp E 2 Q) (L : ℝ≥0) (hf : LipschitzWith L f)
    (Y : ℝ → Lp E 2 Q) (hY : Continuous Y)
    (K : EuclideanSpace ℝ I →L[ℝ] E)
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, ProbabilityTheory.IsPreBrownianReal (W i) Q)
    (T : ℝ) (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 =
      (∫ r in 0..t, f (Y r)) + samplerBrownianInput Q K W hW 0 t) :
    ∃ P G R : ℝ, 0 ≤ P ∧ 0 ≤ G ∧ 0 ≤ R ∧
      (∀ t ∈ Icc 0 T, ‖Y t‖ ≤ P ∧ ‖f (Y t)‖ ≤ G) ∧
      ∀ a s : ℝ, 0 ≤ a → 0 ≤ s → s ≤ 1 → a + s ≤ T →
        ‖Y (a + s) - Y a‖ ≤ R * Real.sqrt s ∧
          ‖f (Y (a + s)) - f (Y a)‖ ≤ (L : ℝ) * R * Real.sqrt s := by
  obtain ⟨P, hP0, hP⟩ := exists_drift_radius id continuous_id Y hY T
  obtain ⟨G, hG0, hG⟩ := exists_drift_radius f hf.continuous Y hY T
  let Ξ : ℝ := ‖K‖ * Real.sqrt (2 * (Fintype.card I : ℝ))
  refine ⟨P, G, G + Ξ, hP0, hG0, by dsimp [Ξ]; positivity, ?_, ?_⟩
  · intro t ht
    exact ⟨hP t ht, hG t ht⟩
  · intro a s ha hs hs1 haT
    have hnoise : ‖samplerBrownianInput Q K W hW 0 (a + s) -
        samplerBrownianInput Q K W hW 0 a‖ ≤ Ξ * Real.sqrt s := by
      rw [samplerBrownianInput_segment]
      exact samplerBrownianInput_bound Q K W hW a s ha hs
    have hinc := integral_segment_sqrt_modulus f Y (samplerBrownianInput Q K W hW 0)
      T a s G Ξ (hf.continuous.comp hY) ha hs hs1 haT hG0 heq hG hnoise
    refine ⟨hinc, ?_⟩
    exact (hf.norm_sub_le _ _).trans (by
      calc
        _ ≤ (L : ℝ) * ((G + Ξ) * Real.sqrt s) := mul_le_mul_of_nonneg_left hinc L.coe_nonneg
        _ = _ := by ring)

end PBGSO
