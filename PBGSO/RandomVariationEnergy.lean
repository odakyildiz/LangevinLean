import PBGSO.StrongMartingaleRadius
import PBGSO.RandomVariationRealization
import PBGSO.PathwiseMartingaleEnergy
import PBGSO.PathwiseDriftFubini

/-! # Expected energy from original raw finite-variation equations
The actual raw equation, an actual L² martingale and a pathwise variation cap
construct all auxiliary L² primitives and the square-integrable path radius.
No time-L¹(L²) drift or maximal-moment conclusion is a premise.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal RealInnerProductSpace InnerProductSpace
namespace PBGSO.RandomVariationEnergy
open QuadraticMartingale RandomVariationRealization
variable {Ω Z : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [MeasurableSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (F : Filtration ℝ mΩ)
  (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
include hW

/-- The original raw integral equation derives its exact expected quadratic
energy. The finite path variation cap is the one provided by actual stopping;
the path radius and primitive L² variables are constructed within the proof. -/
theorem quadratic_balance (T : ℝ≥0) (x b m : ℝ → Ω → Z)
    (h2x : ∀ t, MemLp (x t) 2 Q) (h2m : ∀ t, MemLp (m t) 2 Q)
    (hadapt : ∀ t ∈ Icc 0 (T : ℝ), AEStronglyMeasurable[F t] (x t) Q)
    (hmart : Martingale m F Q)
    (hbx : StronglyMeasurable (Function.uncurry b)) (B : Ω → ℝ) (hB : MemLp B 2 Q)
    (hxcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)))
    (hmcont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => m t ω) (Icc 0 (T : ℝ)))
    (hpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ B ω ∧
      ∀ t ∈ Icc 0 (T : ℝ), x t ω = x 0 ω + (∫ r in 0..t, b r ω) + m t ω) :
    Integrable (fun ω => ∫ r in 0..(T : ℝ), ⟪x r ω, W (b r ω)⟫_ℝ) Q ∧
    (∫ ω, ⟪x T ω, W (x T ω)⟫_ℝ ∂Q) = (∫ ω, ⟪x 0 ω, W (x 0 ω)⟫_ℝ ∂Q) +
      2 * (∫ ω, (∫ r in 0..(T : ℝ), ⟪x r ω, W (b r ω)⟫_ℝ) ∂Q) +
      (∫ ω, ⟪m T ω, W (m T ω)⟫_ℝ ∂Q) := by
  let X (t : ℝ) := (h2x t).toLp (x t)
  let N (t : ℝ) := (h2m t).toLp (m t)
  have hVpaths : ∀ᵐ ω ∂Q, IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ B ω := hpaths.mono (fun _ h => ⟨h.1, h.2.1⟩)
  let V := primitiveLp Q T b hbx B hB hVpaths
  have hX (t : ℝ) : x t =ᵐ[Q] X t := (h2x t).coeFn_toLp.symm
  have hN (t : ℝ) : m t =ᵐ[Q] N t := (h2m t).coeFn_toLp.symm
  have hV (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
      (fun ω => ∫ r in 0..t, b r ω) =ᵐ[Q] V t :=
    (primitiveLp_ae Q T b hbx B hB hVpaths t ht).symm
  have hdecomp (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : X t = X 0 + V t + N t := by
    apply Lp.ext
    filter_upwards [hX t, hX 0, hV t ht, hN t, hpaths,
      Lp.coeFn_add (X 0) (V t), Lp.coeFn_add (X 0 + V t) (N t)]
      with ω hx hz hv hn hp ha hb
    rw [hb, Pi.add_apply, ha, Pi.add_apply, ← hx, ← hz, ← hv, ← hn]
    exact hp.2.2 t ht
  have hN0 : N 0 = 0 := by
    apply Lp.ext
    filter_upwards [hN 0, hpaths, Lp.coeFn_zero Z 2 Q] with ω hn hp hzero
    have hh := hp.2.2 0 ⟨le_rfl, T.coe_nonneg⟩
    simp only [intervalIntegral.integral_same, add_zero] at hh
    have he : x 0 ω + 0 = x 0 ω + m 0 ω := by simpa only [add_zero] using hh
    have hmzero : m 0 ω = 0 := (add_left_cancel he).symm
    rw [← hn, hmzero, hzero]
    rfl
  have ha (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : AEStronglyMeasurable[F t] (X t) Q :=
    (hadapt t ht).congr (hX t)
  obtain ⟨R, hRm, hR0, hR2, hRB, hRbound⟩ := DoobStrongL2.exists_continuous_radius Q F m
    hmart h2m (Icc 0 (T : ℝ)) ⟨0, le_rfl, T.coe_nonneg⟩ T (fun _ ht => ht.2) hmcont
  let C (ω : Ω) := ‖x 0 ω‖ + ‖B ω‖ + R ω
  have hC2 : MemLp C 2 Q := ((h2x 0).norm.add hB.norm).add hR2
  have hCi : Integrable (fun ω => C ω ^ 2) Q := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hC2.aestronglyMeasurable).mp hC2
  have hpC : ∀ᵐ ω ∂Q, ContinuousOn (fun t => x t ω) (Icc 0 (T : ℝ)) ∧
      ContinuousOn (fun t => m t ω) (Icc 0 (T : ℝ)) ∧
      IntervalIntegrable (fun r => b r ω) volume 0 (T : ℝ) ∧ 0 ≤ C ω ∧
      (∀ t ∈ Icc 0 (T : ℝ), ‖x t ω‖ ≤ C ω ∧ ‖m t ω‖ ≤ C ω) ∧
      (∫ r in 0..(T : ℝ), ‖b r ω‖) ≤ C ω := by
    filter_upwards [hxcont, hmcont, hpaths, hRbound] with ω hx hm hp hr
    have hCnon : 0 ≤ C ω := by
      exact add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (hR0 ω)
    refine ⟨hx, hm, hp.1, hCnon, ?_, ?_⟩
    · intro t ht
      have hv := (BoundedVariationRealization.primitive_norm_le T (fun r => b r ω) hp.1 t ht).trans hp.2.1 |>.trans (le_abs_self _)
      constructor
      · rw [hp.2.2 t ht]
        apply (norm_add_le _ _).trans
        dsimp [C]
        linarith [norm_add_le (x 0 ω) (∫ r in 0..t, b r ω), hr t ht]
      · exact (hr t ht).trans (by dsimp [C]; linarith [norm_nonneg (x 0 ω), hR0 ω, le_abs_self (B ω), abs_nonneg (B ω)])
    · exact hp.2.1.trans (by dsimp [C]; linarith [norm_nonneg (x 0 ω), hR0 ω, le_abs_self (B ω), abs_nonneg (B ω)])
  obtain ⟨hi, he⟩ := PathwiseMartingaleEnergy.quadratic_balance Q F W hW T X V N x b m C
    hmart hN hX hV hN0 hdecomp ha hCi hpC
  have hpairX (t : ℝ) : weightedPairing Q W (X t) (X t) =
      ∫ ω, ⟪x t ω, W (x t ω)⟫_ℝ ∂Q := by
    rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hX t] with ω hω
    rw [← hω]
  have hpairN (t : ℝ) : weightedPairing Q W (N t) (N t) =
      ∫ ω, ⟪m t ω, W (m t ω)⟫_ℝ ∂Q := by
    rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hN t] with ω hω
    rw [← hω]
  refine ⟨hi, ?_⟩
  simpa only [hpairX, hpairN] using he

end PBGSO.RandomVariationEnergy
