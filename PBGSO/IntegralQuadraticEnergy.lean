import PBGSO.QuadraticMartingale
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Quadratic energy with integrable time coefficients
No pointwise time derivative or continuous drift is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace InnerProductSpace
namespace PBGSO.IntegralQuadraticEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Domination of all increments by an absolutely continuous scalar curve. -/
theorem absolutelyContinuous_of_dist_le {f : ℝ → E} {g : ℝ → ℝ} {a b : ℝ}
    (hg : AbsolutelyContinuousOnInterval g a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ dist (g x) (g y)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hg ⊢
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := hg ε hε
  refine ⟨δ, hδ, fun S hS hsum => ?_⟩
  apply lt_of_le_of_lt _ (hd S hS hsum)
  apply Finset.sum_le_sum
  intro i hi
  exact h _ (hS.1 i hi).1 _ (hS.1 i hi).2

/-- The indefinite Bochner integral is absolutely continuous in every
complete real Banach space; only time L¹ integrability is needed. -/
theorem integral_absolutelyContinuous (b : ℝ → E) {a t : ℝ}
    (hb : IntervalIntegrable b volume a t) :
    AbsolutelyContinuousOnInterval (fun r => ∫ s in a..r, b s) a t := by
  apply absolutelyContinuous_of_dist_le
    (hb.norm.absolutelyContinuousOnInterval_intervalIntegral (by simp : a ∈ uIcc a t))
  intro x hx y hy
  have hx' : IntervalIntegrable b volume a x := hb.mono_set' (by grind [uIoc, uIcc])
  have hy' : IntervalIntegrable b volume a y := hb.mono_set' (by grind [uIoc, uIcc])
  rw [dist_eq_norm, Real.dist_eq,
    intervalIntegral.integral_interval_sub_left hx' hy',
    intervalIntegral.integral_interval_sub_left hx'.norm hy'.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

theorem bilinear_continuous_integrable (B : E →L[ℝ] E →L[ℝ] ℝ)
    (u b : ℝ → E) {a t : ℝ} (hu : ContinuousOn u (uIcc a t))
    (hb : IntervalIntegrable b volume a t) :
    IntervalIntegrable (fun r => B (u r) (b r)) volume a t := by
  rw [intervalIntegrable_iff] at hb ⊢
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hu
  apply (hb.norm.const_mul (‖B‖ * C)).mono'
  · exact B.continuous₂.comp_aestronglyMeasurable
      (((hu.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc).prodMk
      hb.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
    exact (B.le_opNorm₂ _ _).trans (by gcongr; exact hC r (uIoc_subset_uIcc hr))

/-- Time L² integrability implies time L¹ integrability of any bounded
bilinear quadratic, including every weighted diffusion column energy. -/
theorem quadratic_time_integrable (B : E →L[ℝ] E →L[ℝ] ℝ)
    (f : ℝ → E) {a t : ℝ} (hf : MemLp f 2 (volume.restrict (uIoc a t))) :
    IntervalIntegrable (fun r => B (f r) (f r)) volume a t := by
  rw [intervalIntegrable_iff]
  have hs := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  apply (hs.const_mul ‖B‖).mono'
  · exact B.continuous₂.comp_aestronglyMeasurable (hf.aestronglyMeasurable.prodMk hf.aestronglyMeasurable)
  · filter_upwards with r
    simpa only [pow_two, mul_assoc] using B.le_opNorm₂ (f r) (f r)

/-- An arbitrary continuous bilinear quadratic is Lipschitz on each ball. -/
theorem quadratic_lipschitzOn_ball (B : E →L[ℝ] E →L[ℝ] ℝ) (R : ℝ≥0) :
    LipschitzOnWith (2 * ‖B‖₊ * R) (fun x => B x x) (closedBall (0 : E) R) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx' : ‖x‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hx
  have hy' : ‖y‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hy
  have he : B x x - B y y = B (x-y) x + B y (x-y) := by
    simp only [map_sub, sub_apply]; ring
  simp only [dist_eq_norm]
  rw [he]
  calc
    _ ≤ ‖B (x-y) x‖ + ‖B y (x-y)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖x-y‖ * ‖x‖ + ‖B‖ * ‖y‖ * ‖x-y‖ := add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ (2 * (‖B‖₊ : ℝ) * R) * ‖x-y‖ := by
      simp only [coe_nnnorm]
      nlinarith [mul_le_mul_of_nonneg_left hx' (mul_nonneg (norm_nonneg B) (norm_nonneg (x-y))),
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy' (norm_nonneg B)) (norm_nonneg (x-y))]

theorem quadratic_absolutelyContinuous (B : E →L[ℝ] E →L[ℝ] ℝ)
    (u : ℝ → E) {a t : ℝ} (hu : AbsolutelyContinuousOnInterval u a t) :
    AbsolutelyContinuousOnInterval (fun r => B (u r) (u r)) a t := by
  obtain ⟨C, hC⟩ := hu.exists_bound
  let R : ℝ≥0 := ⟨max C 0, le_max_right C 0⟩
  apply (quadratic_lipschitzOn_ball B R).comp_absolutelyContinuousOnInterval _ hu
  intro r hr
  rw [mem_closedBall, dist_zero_right]
  change ‖u r‖ ≤ (R : ℝ)
  exact (hC r hr).trans (le_max_left C 0)

/-- Deterministic finite-variation quadratic identity for merely Bochner
integrable drift. The derivative exists only almost everywhere. -/
theorem integral_quadratic (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (b : ℝ → E) {a t : ℝ}
    (hb : IntervalIntegrable b volume a t) :
    B (∫ r in a..t, b r) (∫ r in a..t, b r) =
      2 * ∫ r in a..t, B (∫ s in a..r, b s) (b r) := by
  let A := fun r => ∫ s in a..r, b s
  have hA := integral_absolutelyContinuous b hb
  have hQ := quadratic_absolutelyContinuous B A hA
  have hd : ∀ᵐ r, r ∈ uIcc a t →
      HasDerivAt (fun s => B (A s) (A s)) (2 * B (A r) (b r)) r := by
    filter_upwards [hb.ae_hasDerivAt_integral] with r hr hrt
    have hh := (PBGSO.quadratic_hasFDerivAt B (A r)).comp_hasDerivAt r (hr hrt a (by simp))
    convert hh using 1 <;> try rfl
    change 2 * B (A r) (b r) = B (A r) (b r) + B (b r) (A r)
    rw [hB (b r) (A r)]
    ring
  have he := hQ.integral_deriv_eq_sub
  have heq : (∫ r in a..t, deriv (fun s => B (A s) (A s)) r) =
      ∫ r in a..t, 2 * B (A r) (b r) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with r hr hrt
    exact (hr (uIoc_subset_uIcc hrt)).deriv
  rw [heq, intervalIntegral.integral_const_mul] at he
  simpa [A] using he.symm

/-- Exact quadratic balance from adapted drift orthogonality and actual
noise isometry. Neither the balance nor its derivative is an assumption. -/
theorem quadratic_balance (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (X b M : ℝ → E) (q : ℝ → ℝ)
    {T : ℝ} (hT : 0 ≤ T) (hb : IntervalIntegrable b volume 0 T)
    (hq : IntervalIntegrable q volume 0 T) (hX : ContinuousOn X (Icc 0 T))
    (heq : ∀ r ∈ Icc 0 T, X r = X 0 + (∫ s in 0..r, b s) + M r)
    (horth0 : B (X 0) (M T) = 0)
    (horthb : ∀ r ∈ Ioc 0 T, B (b r) (M T - M r) = 0)
    (hiso : B (M T) (M T) = ∫ r in 0..T, q r) :
    B (X T) (X T) = B (X 0) (X 0) +
      ∫ r in 0..T, 2 * B (X r) (b r) + q r := by
  let A := fun r => ∫ s in 0..r, b s
  have hA := integral_absolutelyContinuous b hb
  have hX' : ContinuousOn X (uIcc 0 T) := by simpa [uIcc_of_le hT] using hX
  have hM : ContinuousOn M (uIcc 0 T) := by
    apply ((hX'.sub continuousOn_const).sub hA.continuousOn).congr
    intro r hr
    have hh := heq r (by simpa [uIcc_of_le hT] using hr)
    dsimp [A]
    rw [hh]
    abel
  have hxb := bilinear_continuous_integrable B X b hX' hb
  have hab := bilinear_continuous_integrable B A b hA.continuousOn hb
  have hmb := bilinear_continuous_integrable B M b hM hb
  have h0b : IntervalIntegrable (fun r => B (X 0) (b r)) volume 0 T :=
    bilinear_continuous_integrable B (fun _ => X 0) b continuousOn_const hb
  have hcross : B (A T) (M T) = ∫ r in 0..T, B (M r) (b r) := by
    change B.flip (M T) (∫ r in 0..T, b r) = _
    rw [← (B.flip (M T)).intervalIntegral_comp_comm hb]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r hr
    have hh := horthb r (by simpa [uIoc_of_le hT] using hr)
    rw [map_sub] at hh
    change B (b r) (M T) = B (M r) (b r)
    rw [sub_eq_zero.mp hh, hB]
  have hwork : (∫ r in 0..T, B (X r) (b r)) =
      B (X 0) (A T) + (∫ r in 0..T, B (A r) (b r)) +
      (∫ r in 0..T, B (M r) (b r)) := by
    rw [← (B (X 0)).intervalIntegral_comp_comm hb,
      ← intervalIntegral.integral_add h0b hab,
      ← intervalIntegral.integral_add (h0b.add hab) hmb]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r hr
    rw [heq r (by simpa [uIcc_of_le hT] using uIoc_subset_uIcc hr)]
    simp only [map_add, add_apply]
    rfl
  have hAt := integral_quadratic B hB b hb
  change B (A T) (A T) = _ at hAt
  rw [intervalIntegral.integral_add (hxb.const_mul 2) hq,
    intervalIntegral.integral_const_mul, hwork]
  rw [congrArg (fun x => B x x) (heq T ⟨hT, le_rfl⟩)]
  change B (X 0 + A T + M T) (X 0 + A T + M T) = _
  simp only [map_add, add_apply]
  rw [hB (A T) (X 0), hB (M T) (X 0), hB (M T) (A T), horth0, hAt, hcross, hiso]
  ring

/-- Integral Gronwall with merely L¹-time work. Absolute continuity and
an integrating factor are derived from the actual integral equation. -/
theorem integral_gronwall (e w : ℝ → ℝ) {T c : ℝ} (hT : 0 ≤ T)
    (hw : IntervalIntegrable w volume 0 T)
    (he : ∀ r ∈ Icc 0 T, e r = e 0 + ∫ s in 0..r, w s)
    (hle : ∀ᵐ r ∂volume.restrict (Ioc 0 T), w r ≤ c * e r) :
    e T ≤ Real.exp (c * T) * e 0 := by
  let F := fun r => e 0 + ∫ s in 0..r, w s
  let g := fun r => Real.exp (-c * r) * F r
  have hF : AbsolutelyContinuousOnInterval F 0 T :=
    (contDiff_const.contDiffOn.absolutelyContinuousOnInterval (f := fun _ : ℝ => e 0)).add
      (hw.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hexp : ContDiff ℝ 1 (fun r : ℝ => Real.exp (-c * r)) := by fun_prop
  have hg : AbsolutelyContinuousOnInterval g 0 T :=
    hexp.contDiffOn.absolutelyContinuousOnInterval.fun_mul hF
  have hder : ∀ᵐ r ∂volume.restrict (Ioc 0 T), deriv g r ≤ 0 := by
    filter_upwards [ae_restrict_of_ae hw.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Ioc, hle] with r hr hrt hle
    have hrt' : r ∈ uIcc 0 T := by simp only [uIcc_of_le hT]; exact Ioc_subset_Icc_self hrt
    have hFder : HasDerivAt F (w r) r := (hr hrt' 0 (by simp)).const_add (e 0)
    have hExpder := ((hasDerivAt_id r).const_mul (-c)).exp
    have hgd := hExpder.mul hFder
    have hFr : F r = e r := (he r (Ioc_subset_Icc_self hrt)).symm
    change HasDerivAt g _ r at hgd
    rw [hgd.deriv]
    dsimp only [id_eq] at *
    rw [hFr]
    nlinarith [Real.exp_pos (-c * r)]
  have hneg : (∫ r in 0..T, deriv g r) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hT]
    exact integral_nonpos_of_ae hder
  rw [hg.integral_deriv_eq_sub] at hneg
  have hmain : Real.exp (-c * T) * e T ≤ e 0 := by
    have hFT : F T = e T := (he T ⟨hT, le_rfl⟩).symm
    simpa [g, F, hFT] using hneg
  have hinv : Real.exp (c * T) * Real.exp (-c * T) = 1 := by
    rw [← Real.exp_add, show c * T + -c * T = 0 by ring, Real.exp_zero]
  calc
    e T = Real.exp (c * T) * (Real.exp (-c * T) * e T) := by rw [← mul_assoc, hinv, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmain (Real.exp_nonneg _)

section Martingale
open PBGSO.QuadraticMartingale
variable {Ω Z I : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [Fintype I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- Orthogonality at one time needs adaptedness only at that time. -/
theorem martingale_orthogonal_at (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (U : Lp Z 2 Q) (M : ℝ → Lp Z 2 Q) (m : ℝ → Ω → Z)
    (hm : Martingale m ℱ Q) (hrep : ∀ r, m r =ᵐ[Q] M r)
    {s t : ℝ} (hst : s ≤ t) (hU : AEStronglyMeasurable[ℱ s] U Q) :
    weightedPairing Q W U (M t - M s) = 0 := by
  classical
  let V : ℝ → Lp Z 2 Q := fun r => if r = s then U else 0
  have hV (r : ℝ) : AEStronglyMeasurable[ℱ r] (V r) Q := by
    by_cases hr : r = s
    · subst r; simpa [V] using hU
    · have hz : AEStronglyMeasurable[ℱ r] (0 : Lp Z 2 Q) Q :=
        (aestronglyMeasurable_zero : AEStronglyMeasurable[ℱ r] (0 : Ω → Z) Q).congr (Lp.coeFn_zero Z 2 Q).symm
      simpa [V, hr] using hz
  simpa [V] using martingale_weighted_increment_orthogonal Q ℱ W hW V M m hm hrep hV s t hst

/-- Exact expected quadratic balance for actual martingale residuals with
Bochner L¹-time L² drift and integrable diffusion energy. Coefficients need
no pointwise time derivative or time continuity. Adaptedness and isometry
are stochastic inputs, while the full energy balance is proved. -/
theorem expected_energy_integral (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (X b : ℝ → Lp Z 2 Q) (σ : ℝ → I → Lp Z 2 Q)
    {T : ℝ} (hT : 0 ≤ T) (hX : ContinuousOn X (Icc 0 T))
    (hb : IntervalIntegrable b volume 0 T)
    (hσ : IntervalIntegrable (diffusionEnergy Q W σ) volume 0 T)
    (m : ℝ → Ω → Z) (hm : Martingale m ℱ Q)
    (hrep : ∀ r, m r =ᵐ[Q] martingaleResidual Q X b r)
    (hX0 : AEStronglyMeasurable[ℱ 0] (X 0) Q)
    (hbAdapt : ∀ r ∈ Ioc 0 T, AEStronglyMeasurable[ℱ r] (b r) Q)
    (hIsometry : weightedPairing Q W (martingaleResidual Q X b T)
      (martingaleResidual Q X b T) = ∫ r in 0..T, diffusionEnergy Q W σ r) :
    weightedPairing Q W (X T) (X T) = weightedPairing Q W (X 0) (X 0) +
      ∫ r in 0..T, 2 * weightedPairing Q W (X r) (b r) + diffusionEnergy Q W σ r := by
  have hzero : martingaleResidual Q X b 0 = 0 := by simp [martingaleResidual]
  apply quadratic_balance (weightedPairing Q W) (weightedPairing_symmetric Q W hW)
    X b (martingaleResidual Q X b) (diffusionEnergy Q W σ) hT hb hσ hX
    (fun r _ => martingaleResidual_decomposition Q X b r)
  · simpa only [hzero, sub_zero] using martingale_orthogonal_at Q ℱ W hW (X 0)
      (martingaleResidual Q X b) m hm hrep hT hX0
  · intro r hr
    exact martingale_orthogonal_at Q ℱ W hW (b r) (martingaleResidual Q X b) m hm hrep
      hr.2 (hbAdapt r hr)
  · exact hIsometry

/-- Almost-everywhere drift/diffusion dissipation yields contraction of the
actual martingale-driven expected energy. Its integral balance is derived
above, so no energy inequality or derivative is assumed. -/
theorem expected_energy_decay (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (X b : ℝ → Lp Z 2 Q) (σ : ℝ → I → Lp Z 2 Q)
    {T ρ : ℝ} (hT : 0 ≤ T) (hX : ContinuousOn X (Icc 0 T))
    (hb : IntervalIntegrable b volume 0 T)
    (hσ : IntervalIntegrable (diffusionEnergy Q W σ) volume 0 T)
    (m : ℝ → Ω → Z) (hm : Martingale m ℱ Q)
    (hrep : ∀ r, m r =ᵐ[Q] martingaleResidual Q X b r)
    (hX0 : AEStronglyMeasurable[ℱ 0] (X 0) Q)
    (hbAdapt : ∀ r ∈ Ioc 0 T, AEStronglyMeasurable[ℱ r] (b r) Q)
    (hIsometry : ∀ t ∈ Icc 0 T,
      weightedPairing Q W (martingaleResidual Q X b t) (martingaleResidual Q X b t) =
        ∫ r in 0..t, diffusionEnergy Q W σ r)
    (hDiss : ∀ᵐ r ∂volume.restrict (Ioc 0 T),
      2 * weightedPairing Q W (X r) (b r) + diffusionEnergy Q W σ r ≤
        (-2 * ρ) * weightedPairing Q W (X r) (X r)) :
    weightedPairing Q W (X T) (X T) ≤
      Real.exp (-2 * ρ * T) * weightedPairing Q W (X 0) (X 0) := by
  apply integral_gronwall (fun r => weightedPairing Q W (X r) (X r))
    (fun r => 2 * weightedPairing Q W (X r) (b r) + diffusionEnergy Q W σ r) hT
  · apply IntervalIntegrable.add _ hσ
    exact (bilinear_continuous_integrable (weightedPairing Q W) X b
      (by simpa [uIcc_of_le hT] using hX) hb).const_mul 2
  · intro r hr
    apply expected_energy_integral Q ℱ W hW X b σ hr.1
      (hX.mono (Icc_subset_Icc le_rfl hr.2))
      (hb.mono_set' (by simp only [uIoc_of_le hr.1, uIoc_of_le hT]; exact Ioc_subset_Ioc_right hr.2))
      (hσ.mono_set' (by simp only [uIoc_of_le hr.1, uIoc_of_le hT]; exact Ioc_subset_Ioc_right hr.2))
      m hm hrep hX0 (fun s hs => hbAdapt s (Ioc_subset_Ioc_right hr.2 hs))
      (hIsometry r hr)
  · exact hDiss

end Martingale
end PBGSO.IntegralQuadraticEnergy
