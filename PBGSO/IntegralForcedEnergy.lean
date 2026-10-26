import PBGSO.IntegralQuadraticEnergy
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Forced quadratic energy with a.e. time dissipation
The regularized square-root comparison uses absolute continuity and an
actual integral energy equation; no pointwise derivative is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal
namespace PBGSO.IntegralForcedEnergy
open IntegralQuadraticEnergy

/-- Gronwall for absolutely continuous scalar curves and an a.e. derivative
inequality, proved through the integral fundamental theorem. -/
theorem ac_gronwall (e : ℝ → ℝ) {T c : ℝ} (hT : 0 ≤ T)
    (he : AbsolutelyContinuousOnInterval e 0 T)
    (hd : ∀ᵐ r ∂volume.restrict (Ioc 0 T), deriv e r ≤ c * e r) :
    e T ≤ Real.exp (c * T) * e 0 := by
  apply integral_gronwall e (deriv e) hT he.intervalIntegrable_deriv
  · intro r hr
    have hh := (he.mono (by
      rw [uIcc_of_le hr.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl hr.2)).integral_deriv_eq_sub
    rw [hh]
    ring
  · exact hd

/-- A positive regularization of the square root preserves absolute
continuity. The local Lipschitz constant is derived on the actual compact
range; it is not an extra assumption. -/
theorem regularized_sqrt_ac (f : ℝ → ℝ) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hpos : ∀ r ∈ Icc 0 T, 0 ≤ f r) :
    AbsolutelyContinuousOnInterval (fun r => Real.sqrt (f r + ε ^ 2)) 0 T := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  let R := max C 0 + ε ^ 2
  have hsqrt : ContDiffOn ℝ 1 Real.sqrt (Icc (ε ^ 2) R) :=
    contDiffOn_id.sqrt (fun x hx => ne_of_gt ((sq_pos_of_pos hε).trans_le hx.1))
  obtain ⟨L, hL⟩ := hsqrt.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => ε ^ 2) 0 T :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  apply hL.comp_absolutelyContinuousOnInterval _ (hf.add hc)
  intro r hr
  have hr' : r ∈ Icc 0 T := by simpa [uIcc_of_le hT] using hr
  change ε ^ 2 ≤ f r + ε ^ 2 ∧ f r + ε ^ 2 ≤ R
  constructor
  · linarith [hpos r hr']
  · have hh := (le_abs_self (f r)).trans (hC r hr)
    dsimp [R]
    linarith [le_max_left C 0]

/-- The exact forced-energy square-root bound from merely a.e. dissipation.
The initial energy vanishes and the forcing radius is c. -/
theorem forced_energy_bound (e w : ℝ → ℝ) {T ρ c : ℝ}
    (hT : 0 ≤ T) (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hw : IntervalIntegrable w volume 0 T)
    (he : ∀ r ∈ Icc 0 T, e r = e 0 + ∫ s in 0..r, w s)
    (hE : ∀ r ∈ Icc 0 T, 0 ≤ e r) (hzero : e 0 = 0)
    (hdiss : ∀ᵐ r ∂volume.restrict (Ioc 0 T),
      w r ≤ -2 * ρ * e r + 2 * c * Real.sqrt (e r)) :
    Real.sqrt (e T) ≤ c / ρ * (1 - Real.exp (-ρ * T)) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let F := fun r => e 0 + ∫ s in 0..r, w s
  have hF : AbsolutelyContinuousOnInterval F 0 T :=
    (contDiff_const.contDiffOn.absolutelyContinuousOnInterval (f := fun _ : ℝ => e 0)).add
      (hw.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hFe (r : ℝ) (hr : r ∈ Icc 0 T) : F r = e r := (he r hr).symm
  have hFpos : ∀ r ∈ Icc 0 T, 0 ≤ F r := fun r hr => hFe r hr ▸ hE r hr
  let u := fun r => Real.sqrt (F r + ε ^ 2)
  let uprime := fun r => w r / (2 * u r)
  let C := (c + ρ * ε) / ρ
  have hu := regularized_sqrt_ac F hT hε hF hFpos
  have hC : AbsolutelyContinuousOnInterval (fun _ : ℝ => C) 0 T :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hup (r : ℝ) (hr : r ∈ Icc 0 T) : 0 < u r :=
    Real.sqrt_pos.mpr (by nlinarith [hFpos r hr])
  have husq (r : ℝ) (hr : r ∈ Icc 0 T) : u r ^ 2 = F r + ε ^ 2 :=
    Real.sq_sqrt (by nlinarith [hFpos r hr])
  have hεu (r : ℝ) (hr : r ∈ Icc 0 T) : ε ≤ u r := by
    nlinarith [husq r hr, hFpos r hr, (hup r hr).le]
  have hsqrt (r : ℝ) (hr : r ∈ Icc 0 T) : Real.sqrt (e r) ≤ u r := by
    apply Real.sqrt_le_sqrt
    rw [hFe r hr]
    nlinarith
  have hder : ∀ᵐ r ∂volume.restrict (Ioc 0 T),
      deriv (fun s => u s - C) r ≤ -ρ * (u r - C) := by
    filter_upwards [ae_restrict_of_ae hw.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Ioc, hdiss] with r hr hrt hdiss
    have hrt' : r ∈ Icc 0 T := Ioc_subset_Icc_self hrt
    have hrt'' : r ∈ uIcc 0 T := by simpa [uIcc_of_le hT] using hrt'
    have hFd : HasDerivAt F (w r) r := (hr hrt'' 0 (by simp)).const_add (e 0)
    have hud : HasDerivAt u (uprime r) r := by
      exact (hFd.add_const (ε ^ 2)).sqrt (ne_of_gt (by nlinarith [hFpos r hrt']))
    rw [(hud.sub_const C).deriv]
    have hb : uprime r ≤ -ρ * u r + (c + ρ * ε) := by
      apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) (hup r hrt'))).mpr
      have hm := mul_le_mul_of_nonneg_left (hsqrt r hrt') (by positivity : 0 ≤ 2 * c)
      have hreg := mul_nonneg (by positivity : 0 ≤ 2 * ρ * ε) (sub_nonneg.mpr (hεu r hrt'))
      have heq := husq r hrt'
      rw [hFe r hrt'] at heq
      nlinarith
    have hρC : ρ * C = c + ρ * ε := by dsimp [C]; field_simp
    nlinarith
  have hgr := ac_gronwall (fun r => u r - C) hT (hu.sub hC) hder
  have hu0 : u 0 = ε := by simp [u, F, hzero, Real.sqrt_sq hε.le]
  rw [hu0] at hgr
  have hFT : F T = e T := hFe T ⟨hT, le_rfl⟩
  have heq : Real.exp (-ρ * T) * (ε - C) + C =
      c / ρ * (1 - Real.exp (-ρ * T)) + ε := by
    dsimp [C]
    field_simp
    ring
  have hbound : u T ≤ c / ρ * (1 - Real.exp (-ρ * T)) + ε := by
    rw [← heq]
    linarith
  exact (hsqrt T ⟨hT, le_rfl⟩).trans hbound

end PBGSO.IntegralForcedEnergy
