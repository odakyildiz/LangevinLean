import LatentDiffusion.SourceResults
import LatentDiffusion.RegularMetricFlow
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option linter.style.header false

/-! # From extended LSI to finite flow length and Talagrand

The implication uses the actual flow's energy dissipation and upper-right
metric-speed estimate. It requires no geodesic convexity hypothesis. Those
two flow identities are supplied by the separate density/PDE and coupling
theorems when this real-analysis result is specialized to the source model.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace LatentDiffusion.RegularTalagrand

theorem energy_nonincreasing
    (E I : ℝ → ℝ) (hcont : ContinuousOn E (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt E (-I t) (Ici t) t)
    (hI : ∀ t, 0 ≤ t → 0 ≤ I t) (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    E t ≤ E s := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := fun u ↦ -I u) (δ := E s) (K := 0) (ε := 0)
    (hcont.mono (fun u hu ↦ hs.trans hu.1))
    (fun u hu r hr ↦ (hderiv u (hs.trans hu.1)).liminf_right_slope_le hr)
    (le_refl _) (fun u hu ↦ by simpa using neg_nonpos.mpr (hI u (hs.trans hu.1)))
    t (show t ∈ Icc s t from ⟨hst, le_rfl⟩)
  simpa only [gronwallBound_K0, zero_mul, add_zero] using h

/-- At zero energy the nonnegative dissipating energy stays zero to the right,
so its square root has right derivative zero even though sqrt is singular. -/
theorem sqrt_energy_hasDerivWithinAt
    (E I : ℝ → ℝ) (hcont : ContinuousOn E (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt E (-I t) (Ici t) t)
    (hE : ∀ t, 0 ≤ t → 0 ≤ E t) (hI : ∀ t, 0 ≤ t → 0 ≤ I t)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u ↦ Real.sqrt (E u))
      (if E t = 0 then 0 else -I t / (2 * Real.sqrt (E t))) (Ici t) t ∧
      (E t = 0 → I t = 0) := by
  by_cases hz : E t = 0
  · have heq (u : ℝ) (hu : u ∈ Ici t) : E u = 0 := by
      apply le_antisymm
      · simpa only [hz] using energy_nonincreasing E I hcont hderiv hI t u ht hu
      · exact hE u (ht.trans hu)
    have hd0 : HasDerivWithinAt E 0 (Ici t) t :=
      (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr heq hz
    have hzI : I t = 0 := by
      have ha := (hderiv t ht).derivWithin (uniqueDiffWithinAt_Ici t)
      have hb := hd0.derivWithin (uniqueDiffWithinAt_Ici t)
      linarith
    constructor
    · simp only [hz, ↓reduceIte]
      apply (hasDerivWithinAt_const t (Ici t) (0 : ℝ)).congr
      · intro u hu
        simp [heq u hu]
      · simp [hz]
    · exact fun _ ↦ hzI
  · exact ⟨by simpa only [hz, ↓reduceIte] using (hderiv t ht).sqrt hz,
      fun h ↦ (hz h).elim⟩

/-- Extended LSI controls the square-root energy's dissipation by the metric
speed. The zero-energy case is handled by the preceding right-constancy proof. -/
theorem sqrt_energy_speed_bound
    {E I rho : ℝ} (hrho : 0 < rho) (hE : 0 ≤ E) (hI : 0 ≤ I)
    (hlsi : 2 * rho * E ≤ I) (hzero : E = 0 → I = 0) :
    Real.sqrt (2 * rho) * Real.sqrt I +
      2 * (if E = 0 then 0 else -I / (2 * Real.sqrt E)) ≤ 0 := by
  by_cases hz : E = 0
  · simp [hz, hzero hz]
  · have hEp : 0 < E := lt_of_le_of_ne hE (Ne.symm hz)
    have hsE : 0 < Real.sqrt E := Real.sqrt_pos.mpr hEp
    have hroot : Real.sqrt (2 * rho) * Real.sqrt E ≤ Real.sqrt I := by
      rw [← Real.sqrt_mul (by linarith : 0 ≤ 2 * rho)]
      exact Real.sqrt_le_sqrt hlsi
    have hmult := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg I)
    rw [mul_assoc, Real.mul_self_sqrt hI] at hmult
    simp only [hz, ↓reduceIte]
    apply (mul_le_mul_iff_left₀ hsE).mp
    have hcancel : (2 * (-I / (2 * Real.sqrt E))) * Real.sqrt E = -I := by
      field_simp
    rw [add_mul, hcancel, zero_mul]
    nlinarith [hmult]

/-- Adding a differentiable scalar correction to an upper-right slope bound
preserves the bound. The result is stronger than the liminf input to Grönwall. -/
theorem upper_slope_add
    (D G : ℝ → ℝ) (t L g : ℝ)
    (hD : ∀ r, L < r → ∀ᶠ u in 𝓝[>] t, slope D t u < r)
    (hG : HasDerivWithinAt G g (Ici t) t) :
    ∀ r, L + g < r → ∀ᶠ u in 𝓝[>] t, slope (fun s ↦ D s + G s) t u < r := by
  intro r hr
  let ε := (r - (L + g)) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hlim : Tendsto (slope G t) (𝓝[>] t) (𝓝 g) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : t ∉ Ioi t)).mp
      (hG.mono Ioi_subset_Ici_self)
  filter_upwards [hD (L + ε) (by linarith),
    hlim.eventually (Iio_mem_nhds (show g < g + ε by linarith)),
    self_mem_nhdsWithin] with u huD huG htu
  have heq : slope (fun s ↦ D s + G s) t u = slope D t u + slope G t u := by
    simp only [slope_def_field]
    ring
  rw [heq]
  dsimp [ε] at huD huG
  linarith

/-- Finite remaining flow length: the product of sqrt(2 rho) with any distance
increment is paid for by the drop of twice the square-root energy. -/
theorem distance_energy_drop
    (D E I : ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hDcont : ContinuousOn D (Ici 0)) (hEcont : ContinuousOn E (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt E (-I t) (Ici t) t)
    (hE : ∀ t, 0 ≤ t → 0 ≤ E t) (hI : ∀ t, 0 ≤ t → 0 ≤ I t)
    (hlsi : ∀ t, 0 ≤ t → 2 * rho * E t ≤ I t)
    (hspeed : ∀ t, 0 ≤ t → ∀ r, Real.sqrt (I t) < r →
      ∀ᶠ u in 𝓝[>] t, slope D t u < r)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.sqrt (2 * rho) * (D t - D s) ≤
      2 * (Real.sqrt (E s) - Real.sqrt (E t)) := by
  let A := Real.sqrt (2 * rho)
  have hA : 0 < A := Real.sqrt_pos.mpr (by linarith)
  let G : ℝ → ℝ := fun u ↦ 2 * Real.sqrt (E u)
  let F : ℝ → ℝ := fun u ↦ A * D u + G u
  let J : ℝ → ℝ := fun u ↦
    A * Real.sqrt (I u) + 2 * (if E u = 0 then 0 else -I u / (2 * Real.sqrt (E u)))
  have hFcont : ContinuousOn F (Ici 0) :=
    (continuousOn_const.mul hDcont).add
      (continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hEcont))
  have hFspeed : ∀ u, 0 ≤ u → ∀ r, J u < r →
      ∀ᶠ z in 𝓝[>] u, slope F u z < r := by
    intro u hu r hr
    have hscaled : ∀ c, A * Real.sqrt (I u) < c →
        ∀ᶠ z in 𝓝[>] u, slope (fun y ↦ A * D y) u z < c := by
      intro c hc
      have hc' : Real.sqrt (I u) < c / A := (lt_div_iff₀ hA).mpr (by nlinarith)
      filter_upwards [hspeed u hu (c / A) hc'] with z hz
      have hscale : slope (fun y ↦ A * D y) u z = A * slope D u z := by
        simp only [slope_def_field]
        ring
      rw [hscale]
      have hh := (lt_div_iff₀ hA).mp hz
      nlinarith
    exact upper_slope_add (fun y ↦ A * D y) G u (A * Real.sqrt (I u)) _ hscaled
      ((sqrt_energy_hasDerivWithinAt E I hEcont hderiv hE hI u hu).1.const_mul 2) r hr
  have hJ : ∀ u, 0 ≤ u → J u ≤ 0 := by
    intro u hu
    exact sqrt_energy_speed_bound hrho (hE u hu) (hI u hu) (hlsi u hu)
      (sqrt_energy_hasDerivWithinAt E I hEcont hderiv hE hI u hu).2
  have hout := le_gronwallBound_of_liminf_deriv_right_le
    (f := F) (f' := J) (δ := F s) (K := 0) (ε := 0)
    (hFcont.mono (fun u hu ↦ hs.trans hu.1))
    (fun u hu r hr ↦ by
      simpa only [slope_def_field, div_eq_inv_mul] using
        (hFspeed u (hs.trans hu.1) r hr).frequently)
    (le_refl _) (fun u hu ↦ by simpa using hJ u (hs.trans hu.1))
    t (show t ∈ Icc s t from ⟨hst, le_rfl⟩)
  simp only [gronwallBound_K0, zero_mul, add_zero] at hout
  dsimp [F, G, A] at hout
  linarith

theorem energy_decay
    (E I : ℝ → ℝ) (rho : ℝ) (_hrho : 0 < rho)
    (hcont : ContinuousOn E (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt E (-I t) (Ici t) t)
    (hlsi : ∀ t, 0 ≤ t → 2 * rho * E t ≤ I t)
    (t : ℝ) (ht : 0 ≤ t) :
    E t ≤ E 0 * Real.exp (-2 * rho * t) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := E) (f' := fun u ↦ -I u) (δ := E 0) (K := -2 * rho) (ε := 0)
    (hcont.mono (fun u hu ↦ hu.1))
    (fun u hu r hr ↦ (hderiv u hu.1).liminf_right_slope_le hr)
    (le_refl _) (fun u hu ↦ by have hh := hlsi u hu.1; linarith)
    t (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
  simpa only [gronwallBound_ε0, sub_zero] using h

theorem energy_nat_tendsto_zero
    (E I : ℝ → ℝ) (rho : ℝ) (hrho : 0 < rho)
    (hcont : ContinuousOn E (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt E (-I t) (Ici t) t)
    (hE : ∀ t, 0 ≤ t → 0 ≤ E t)
    (hlsi : ∀ t, 0 ≤ t → 2 * rho * E t ≤ I t) :
    Tendsto (fun n : ℕ ↦ E n) atTop (𝓝 0) := by
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp (-2 * rho * (n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (by linarith : -2 * rho < 0))
  have hupper := hexp.const_mul (E 0)
  simp only [mul_zero] at hupper
  exact squeeze_zero (fun n ↦ hE n (Nat.cast_nonneg _))
    (fun n ↦ energy_decay E I rho hrho hcont hderiv hlsi n (Nat.cast_nonneg _)) hupper

/-- Extended LSI implies the corrected Talagrand conclusion by the full
flow-length argument on a complete metric energy domain. No minimizer or
geodesic convexity is an input: a minimizing limit is constructed.

In the latent-density application, dissipation is supplied by
`normalized_product_deBruijn` and upper slopes by the characteristic/coupling
theorem. Lower semicontinuity is supplied by the dominated density chart. -/
theorem metric_flow_talagrand
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (F : X → ℝ) (Fstar : ℝ) (x : ℝ → X) (I : ℝ → ℝ) (rho : ℝ)
    (hrho : 0 < rho) (hF : LowerSemicontinuous F) (hstar : ∀ y, Fstar ≤ F y)
    (hx : ContinuousOn x (Ici 0))
    (henergy : ContinuousOn (fun t ↦ F (x t) - Fstar) (Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt (fun u ↦ F (x u) - Fstar)
      (-I t) (Ici t) t)
    (hI : ∀ t, 0 ≤ t → 0 ≤ I t)
    (hlsi : ∀ t, 0 ≤ t → 2 * rho * (F (x t) - Fstar) ≤ I t)
    (hspeed : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ r, Real.sqrt (I t) < r →
      ∀ᶠ u in 𝓝[>] t, slope (fun v ↦ dist (x s) (x v)) t u < r) :
    ∃ xstar, Tendsto (fun n : ℕ ↦ x n) atTop (𝓝 xstar) ∧
      F xstar = Fstar ∧ (∀ y, F xstar ≤ F y) ∧
      ∀ t, 0 ≤ t → rho * dist (x t) xstar ^ 2 ≤ 2 * (F (x t) - Fstar) := by
  let E : ℝ → ℝ := fun t ↦ F (x t) - Fstar
  have hE (t : ℝ) (_ht : 0 ≤ t) : 0 ≤ E t := sub_nonneg.mpr (hstar (x t))
  have hdrop (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
      Real.sqrt (2 * rho) * dist (x s) (x t) ≤
        2 * (Real.sqrt (E s) - Real.sqrt (E t)) := by
    have h := distance_energy_drop (fun u ↦ dist (x s) (x u)) E I rho hrho
      ((continuous_const.dist continuous_id).comp_continuousOn hx)
      henergy hderiv hE hI hlsi
      (fun u hu ↦ hspeed s u hs hu) s t hs hst
    simpa only [dist_self, sub_zero] using h
  have hEn : Tendsto (fun n : ℕ ↦ E n) atTop (𝓝 0) :=
    energy_nat_tendsto_zero E I rho hrho henergy hderiv hE hlsi
  have hroot : Tendsto (fun n : ℕ ↦ 2 * Real.sqrt (E n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero] using
      (Real.continuous_sqrt.tendsto 0 |>.comp hEn).const_mul 2
  have hA : 0 < Real.sqrt (2 * rho) := Real.sqrt_pos.mpr (by linarith)
  have hCauchy : CauchySeq (fun n : ℕ ↦ x n) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (hroot.eventually (Iio_mem_nhds (mul_pos hA hε)))
    refine ⟨N, ?_⟩
    intro m hm n hn
    rcases le_total m n with hmn | hnm
    · have hd := hdrop m n (Nat.cast_nonneg _) (by exact_mod_cast hmn)
      have hsmall := hN m hm
      have hnonneg := Real.sqrt_nonneg (E n)
      nlinarith
    · have hd := hdrop n m (Nat.cast_nonneg _) (by exact_mod_cast hnm)
      have hsmall := hN n hn
      have hnonneg := Real.sqrt_nonneg (E m)
      rw [dist_comm (x (n : ℝ)) (x (m : ℝ))] at hd
      nlinarith
  have hvalues : Tendsto (fun n : ℕ ↦ F (x n)) atTop (𝓝 Fstar) := by
    convert hEn.add_const Fstar using 1
    · funext n
      dsimp [E]
      ring
    · simp
  obtain ⟨xstar, hlimit, hminvalue, hmin⟩ :=
    SourceResults.cauchy_minimizing_sequence F Fstar hF hstar
      (fun n : ℕ ↦ x n) hCauchy hvalues
  refine ⟨xstar, hlimit, hminvalue, hmin, ?_⟩
  intro t ht
  have hdlim : Tendsto (fun n : ℕ ↦ Real.sqrt (2 * rho) * dist (x t) (x n))
      atTop (𝓝 (Real.sqrt (2 * rho) * dist (x t) xstar)) :=
    (((continuous_const.dist continuous_id).continuousAt.tendsto).comp hlimit).const_mul _
  have heroot : Tendsto (fun n : ℕ ↦ 2 * (Real.sqrt (E t) - Real.sqrt (E n)))
      atTop (𝓝 (2 * Real.sqrt (E t))) := by
    simpa only [Function.comp_apply, Real.sqrt_zero, sub_zero] using
      (tendsto_const_nhds.sub (Real.continuous_sqrt.tendsto 0 |>.comp hEn)).const_mul 2
  have hdbound : Real.sqrt (2 * rho) * dist (x t) xstar ≤ 2 * Real.sqrt (E t) := by
    apply le_of_tendsto_of_tendsto hdlim heroot
    filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop t)] with n hn
    exact hdrop t n ht hn
  have hsq : (Real.sqrt (2 * rho) * dist (x t) xstar) ^ 2 ≤
      (2 * Real.sqrt (E t)) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hdbound 2
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ 2 * rho), mul_pow,
    Real.sq_sqrt (hE t ht)] at hsq
  dsimp [E] at hsq
  nlinarith

end LatentDiffusion.RegularTalagrand
