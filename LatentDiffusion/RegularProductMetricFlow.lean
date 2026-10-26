import LatentDiffusion.RegularMetricFlow
import LatentDiffusion.RegularTransport

set_option linter.style.header false

/-! # The actual normalized finite-data metric speed

The Hilbert realization contains the deterministic parameter and all latent
characteristics scaled by `sqrt(1/M)`.  Its norm is the paper's normalized
quadratic product cost.  Actual optimal anchors identify the product distance,
and actual characteristic derivatives determine the speed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

namespace LatentDiffusion.RegularProductMetricFlow

variable {M : ℕ} {Ω : Fin M → Type*} [∀ m, MeasurableSpace (Ω m)]
  {P Z : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (Q m)]

abbrev LiftSpace := WithLp 2 (P × PiLp 2 (fun m ↦ Lp Z 2 (Q m)))

def lift (a : P) (Y : ∀ m, Lp Z 2 (Q m)) : LiftSpace (P := P) (Z := Z) Q :=
  WithLp.toLp 2 (a, WithLp.toLp 2 (fun m ↦ Real.sqrt (M : ℝ)⁻¹ • Y m))

theorem lift_sub (a b : P) (Y W : ∀ m, Lp Z 2 (Q m)) :
    lift Q a Y - lift Q b W = lift Q (a - b) (fun m ↦ Y m - W m) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · apply WithLp.ofLp_injective 2
    funext m
    change Real.sqrt (M : ℝ)⁻¹ • Y m - Real.sqrt (M : ℝ)⁻¹ • W m =
      Real.sqrt (M : ℝ)⁻¹ • (Y m - W m)
    rw [smul_sub]

theorem lift_norm_sq (a : P) (Y : ∀ m, Lp Z 2 (Q m)) :
    ‖lift Q a Y‖ ^ 2 = ‖a‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m, ‖Y m‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖a‖ ^ 2 + ‖(WithLp.toLp 2 (fun m ↦ Real.sqrt (M : ℝ)⁻¹ • Y m) :
    PiLp 2 (fun m ↦ Lp Z 2 (Q m)))‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (inv_nonneg.mpr (Nat.cast_nonneg M))]
  rw [Finset.mul_sum]

/-- The actual normalized product metric to fixed probability-law targets. -/
def distance (a : ℝ → P) (Y : ℝ → ∀ m, Lp Z 2 (Q m))
    (astar : P) (target : Fin M → Measure Z) (t : ℝ) : ℝ :=
  Real.sqrt (‖a t - astar‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m,
    ULA.wasserstein2Real ((Q m).map (Y t m)) (target m) ^ 2)

theorem distance_eq_anchor_norm
    (a : ℝ → P) (Y : ℝ → ∀ m, Lp Z 2 (Q m)) (astar : P)
    (target : Fin M → Measure Z)
    (anchor : ∀ t m, RegularMetricFlow.OptimalAnchor (Q m) (Y t m) (target m))
    (t : ℝ) :
    distance Q a Y astar target t =
      ‖lift Q (a t) (Y t) - lift Q astar (fun m ↦ (anchor t m).value)‖ := by
  rw [lift_sub, ← Real.sqrt_sq (norm_nonneg _), lift_norm_sq]
  unfold distance
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [(anchor t m).distance_eq]

/-- Coupling each characteristic with the fixed target anchors bounds the
actual product distance by the Hilbert cost to those anchors. -/
theorem distance_le_anchor_norm
    (a : ℝ → P) (Y : ℝ → ∀ m, Lp Z 2 (Q m)) (astar : P)
    (target : Fin M → Measure Z)
    (anchor : ∀ t m, RegularMetricFlow.OptimalAnchor (Q m) (Y t m) (target m))
    (s t : ℝ) :
    distance Q a Y astar target s ≤
      ‖lift Q (a s) (Y s) - lift Q astar (fun m ↦ (anchor t m).value)‖ := by
  rw [lift_sub, ← Real.sqrt_sq (norm_nonneg _), lift_norm_sq]
  unfold distance
  apply Real.sqrt_le_sqrt
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg M))
  apply Finset.sum_le_sum
  intro m _
  have h := ULA.wasserstein2_le_Lp_cost_real (Q m) (Y s m) (anchor t m).value
  rw [(anchor t m).law] at h
  exact (sq_le_sq₀ ENNReal.toReal_nonneg (norm_nonneg _)).mpr h

theorem distance_increment_le
    (a : ℝ → P) (Y : ℝ → ∀ m, Lp Z 2 (Q m)) (astar : P)
    (target : Fin M → Measure Z)
    (anchor : ∀ t m, RegularMetricFlow.OptimalAnchor (Q m) (Y t m) (target m))
    (s t : ℝ) :
    distance Q a Y astar target s - distance Q a Y astar target t ≤
      ‖lift Q (a s) (Y s) - lift Q (a t) (Y t)‖ := by
  have hs := distance_le_anchor_norm Q a Y astar target anchor s t
  have ht := distance_eq_anchor_norm Q a Y astar target anchor t
  have htri : ‖lift Q (a s) (Y s) - lift Q astar (fun m ↦ (anchor t m).value)‖ ≤
      ‖lift Q (a s) (Y s) - lift Q (a t) (Y t)‖+
        ‖lift Q (a t) (Y t) - lift Q astar (fun m ↦ (anchor t m).value)‖ := by
    calc
      _ = ‖(lift Q (a s) (Y s) - lift Q (a t) (Y t))+
          (lift Q (a t) (Y t) - lift Q astar (fun m ↦ (anchor t m).value))‖ := by
        congr 1
        abel
      _ ≤ _ := norm_add_le _ _
  linarith

theorem distance_abs_increment_le
    (a : ℝ → P) (Y : ℝ → ∀ m, Lp Z 2 (Q m)) (astar : P)
    (target : Fin M → Measure Z)
    (anchor : ∀ t m, RegularMetricFlow.OptimalAnchor (Q m) (Y t m) (target m))
    (s t : ℝ) :
    |distance Q a Y astar target s - distance Q a Y astar target t| ≤
      ‖lift Q (a s) (Y s) - lift Q (a t) (Y t)‖ := by
  refine abs_le.mpr ⟨?_, distance_increment_le Q a Y astar target anchor s t⟩
  have h := distance_increment_le Q a Y astar target anchor t s
  rw [norm_sub_rev] at h
  linarith

/-- Derivatives of all physical coordinates construct the derivative of the
normalized Hilbert realization. No metric derivative is assumed. -/
theorem lift_hasDerivAt
    (a : ℝ → P) (Y : ℝ → ∀ m, Lp Z 2 (Q m)) (t : ℝ)
    (adot : P) (v : ∀ m, Lp Z 2 (Q m))
    (ha : HasDerivAt a adot t) (hY : ∀ m, HasDerivAt (fun s ↦ Y s m) (v m) t) :
    HasDerivAt (fun s ↦ lift Q (a s) (Y s)) (lift Q adot v) t := by
  have hpi : HasDerivAt
      (fun s m ↦ Real.sqrt (M : ℝ)⁻¹ • Y s m)
      (fun m ↦ Real.sqrt (M : ℝ)⁻¹ • v m) t :=
    hasDerivAt_pi.mpr (fun m ↦ by
      convert (hY m).const_smul (Real.sqrt (M : ℝ)⁻¹) using 1)
  have hl := (PiLp.continuousLinearEquiv 2 ℝ (fun m ↦ Lp Z 2 (Q m))).symm
    |>.hasFDerivAt.comp_hasDerivAt t hpi
  have hj := (WithLp.prodContinuousLinearEquiv 2 ℝ P
    (PiLp 2 (fun m ↦ Lp Z 2 (Q m)))).symm.hasFDerivAt.comp_hasDerivAt t (ha.prodMk hl)
  exact hj

/-- Corrected source metric-speed statement for the full normalized product:
the actual upper right slope is bounded by the root parameter/latent kinetic
energy. At distance zero this Dini statement remains valid. -/
theorem distance_right_slope
    (a : ℝ → P) (Y : ℝ → ∀ m, Lp Z 2 (Q m)) (astar : P)
    (target : Fin M → Measure Z)
    (anchor : ∀ t m, RegularMetricFlow.OptimalAnchor (Q m) (Y t m) (target m))
    (t : ℝ) (adot : P) (v : ∀ m, Lp Z 2 (Q m))
    (ha : HasDerivAt a adot t) (hY : ∀ m, HasDerivAt (fun s ↦ Y s m) (v m) t)
    (r : ℝ) (hr : Real.sqrt (‖adot‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m, ‖v m‖ ^ 2) < r) :
    ∀ᶠ s in 𝓝[>] t, slope (distance Q a Y astar target) t s < r := by
  have hnorm : ‖lift Q adot v‖ =
      Real.sqrt (‖adot‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m, ‖v m‖ ^ 2) := by
    rw [← lift_norm_sq Q adot v, Real.sqrt_sq (norm_nonneg _)]
  have h : HasDerivWithinAt (fun s ↦ lift Q (a s) (Y s)) (lift Q adot v) (Ici t) t :=
    (lift_hasDerivAt Q a Y t adot v ha hY).hasDerivWithinAt
  have hs := (h.mono Ioi_subset_Ici_self).limsup_norm_slope_le (hnorm ▸ hr)
  filter_upwards [hs, self_mem_nhdsWithin] with s hs hst
  have hi := distance_increment_le Q a Y astar target anchor s t
  rw [slope_def_field]
  have hpos : 0 < s - t := sub_pos.mpr hst
  simp only [Real.norm_eq_abs, abs_of_pos hpos] at hs
  have hscaled := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hpos.le)
  simpa only [Real.norm_eq_abs, abs_of_pos hpos, div_eq_inv_mul]
    using hscaled.trans_lt hs

/-- Integrating the constructed Hilbert characteristic derivative gives the
integrated metric-speed estimate for the actual normalized product distance.
The integrability hypothesis concerns the physical coordinate velocities,
rather than any supplied transport or metric-speed inequality. -/
theorem distance_integral_bound
    (a adot : ℝ → P) (Y v : ℝ → ∀ m, Lp Z 2 (Q m)) (astar : P)
    (target : Fin M → Measure Z)
    (anchor : ∀ t m, RegularMetricFlow.OptimalAnchor (Q m) (Y t m) (target m))
    (s t : ℝ) (hst : s ≤ t)
    (ha : ∀ u ∈ uIcc s t, HasDerivAt a (adot u) u)
    (hY : ∀ u ∈ uIcc s t, ∀ m, HasDerivAt (fun r ↦ Y r m) (v u m) u)
    (hv : IntervalIntegrable (fun u ↦ lift Q (adot u) (v u)) volume s t) :
    |distance Q a Y astar target t - distance Q a Y astar target s| ≤
      ∫ u in s..t, Real.sqrt (‖adot u‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m, ‖v u m‖ ^ 2) := by
  have hderiv : ∀ u ∈ uIcc s t,
      HasDerivAt (fun r ↦ lift Q (a r) (Y r)) (lift Q (adot u) (v u)) u :=
    fun u hu ↦ lift_hasDerivAt Q a Y u (adot u) (v u) (ha u hu) (hY u hu)
  calc
    _ ≤ ‖lift Q (a t) (Y t) - lift Q (a s) (Y s)‖ :=
      distance_abs_increment_le Q a Y astar target anchor t s
    _ = ‖∫ u in s..t, lift Q (adot u) (v u)‖ := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hv]
    _ ≤ ∫ u in s..t, ‖lift Q (adot u) (v u)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hst
    _ = _ := by
      congr 1
      funext u
      rw [← lift_norm_sq Q (adot u) (v u), Real.sqrt_sq (norm_nonneg _)]

/-- At times where the ordinary right derivative exists, the Dini estimate
implies the source derivative inequality for the full product metric. -/
theorem distance_derivative_le
    (a : ℝ → P) (Y : ℝ → ∀ m, Lp Z 2 (Q m)) (astar : P)
    (target : Fin M → Measure Z)
    (anchor : ∀ t m, RegularMetricFlow.OptimalAnchor (Q m) (Y t m) (target m))
    (t : ℝ) (adot : P) (v : ∀ m, Lp Z 2 (Q m))
    (ha : HasDerivAt a adot t) (hY : ∀ m, HasDerivAt (fun s ↦ Y s m) (v m) t)
    (derivative : ℝ)
    (hd : HasDerivWithinAt (distance Q a Y astar target) derivative (Ici t) t) :
    derivative ≤ Real.sqrt (‖adot‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m, ‖v m‖ ^ 2) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hb := distance_right_slope Q a Y astar target anchor t adot v ha hY
    (Real.sqrt (‖adot‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m, ‖v m‖ ^ 2) + ε) (by linarith)
  have hlim : Tendsto (slope (distance Q a Y astar target) t) (𝓝[>] t) (𝓝 derivative) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : t ∉ Ioi t)).mp
      (hd.mono Ioi_subset_Ici_self)
  exact le_of_tendsto hlim (hb.mono fun _ h ↦ h.le)

/-- The derivative of the characteristic realizes the physical velocity;
its L² norm is the actual law integral of the squared velocity field. -/
theorem velocity_norm_sq
    (Y v : ∀ m, Lp Z 2 (Q m)) (field : Fin M → Z → Z)
    (hmeas : ∀ m, Measurable (field m))
    (hvelocity : ∀ m, (v m : Ω m → Z) =ᵐ[Q m]
      (fun ω ↦ -(field m ((Y m) ω)))) (m : Fin M) :
    ‖v m‖ ^ 2 = ∫ z, ‖field m z‖ ^ 2 ∂(Q m).map (Y m) := by
  rw [ProximalLangevin.lp_norm_sq_eq_integral]
  have hmap := integral_map (Lp.aestronglyMeasurable (Y m)).aemeasurable
    ((hmeas m).norm.pow_const 2).aestronglyMeasurable
  rw [hmap]
  apply integral_congr_ae
  filter_upwards [hvelocity m] with ω hω
  simp only [hω, norm_neg]

/-- Exact identification of product kinetic energy with the source Fisher
information, with the parameter force averaged before squaring. -/
theorem kinetic_energy_eq_fisher
    (Y v : ∀ m, Lp Z 2 (Q m)) (field : Fin M → Z → Z) (force adot : P)
    (hadot : adot = -force) (hmeas : ∀ m, Measurable (field m))
    (hvelocity : ∀ m, (v m : Ω m → Z) =ᵐ[Q m]
      (fun ω ↦ -(field m ((Y m) ω)))) :
    ‖adot‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m, ‖v m‖ ^ 2 =
      ‖force‖ ^ 2 + (M : ℝ)⁻¹ * ∑ m,
        ∫ z, ‖field m z‖ ^ 2 ∂(Q m).map (Y m) := by
  rw [hadot, norm_neg]
  congr 2
  apply Finset.sum_congr rfl
  intro m _
  exact velocity_norm_sq Q Y v field hmeas hvelocity m

end LatentDiffusion.RegularProductMetricFlow
