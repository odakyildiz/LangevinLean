import PBGSO.GlobalIntegral

/-! # Global ODE trajectories from a primitive globally Lipschitz field

Forward and reverse Picard integral trajectories are glued at time zero.
Their actual derivatives agree there. The resulting all-real-time flow
selector assumes no joint continuity or differentiability in its initial
state; those properties can subsequently be proved from the vector field.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace PBGSO
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The ODE is derived from the actual zero-input integral equation by FTC. -/
theorem global_integral_hasDerivWithinAt (f : E → E) (hf : Continuous f)
    (initial : E) (Y : ℝ → E) (hY : Continuous Y)
    (heq : ∀ t, 0 ≤ t → Y t - initial = ∫ r in 0..t, f (Y r))
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt Y (f (Y t)) (Ici 0) t := by
  have hc := hf.comp hY
  have hd := intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
    (hc.intervalIntegrable 0 t) (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt
  apply (hd.const_add initial).hasDerivWithinAt.congr
  · intro r hr
    exact (sub_eq_iff_eq_add.mp (heq r hr)).trans (add_comm _ _)
  · exact (sub_eq_iff_eq_add.mp (heq t ht)).trans (add_comm _ _)

/-- Primitive global Lipschitz regularity constructs an actual all-time
trajectory from every initial state, including the derivative at zero. -/
theorem exists_global_ode_flow (f : E → E) (L : ℝ≥0) (hf : LipschitzWith L f) :
    ∃ Φ : ℝ × E → E, (∀ x, Φ (0, x) = x) ∧
      ∀ t x, HasDerivAt (fun r => Φ (r, x)) (f (Φ (t, x))) t := by
  classical
  have ex (g : E → E) (hg : LipschitzWith L g) (x : E) :
      ∃ Y : ℝ → E, Continuous Y ∧ Y 0 = x ∧
        ∀ t, 0 ≤ t → Y t - x = ∫ r in 0..t, g (Y r) := by
    obtain ⟨Y, hc, hz, he⟩ := exists_global_integral_solution g L hg x
      (fun _ => 0) continuous_const rfl
    exact ⟨Y, hc, hz, fun t ht => by simpa using he t ht⟩
  choose Yp hpc hp0 hpe using ex f hf
  choose Ym hmc hm0 hme using ex (fun z => -f z) hf.neg
  let Φ : ℝ × E → E := fun p => if 0 ≤ p.1 then Yp p.2 p.1 else Ym p.2 (-p.1)
  have hΦ0 (x : E) : Φ (0, x) = x := by simp [Φ, hp0]
  have hpd (x : E) (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt (Yp x) (f (Yp x t)) (Ici 0) t :=
    global_integral_hasDerivWithinAt f hf.continuous x (Yp x) (hpc x) (hpe x) t ht
  have hmd (x : E) (t : ℝ) (ht : 0 ≤ t) :
      HasDerivWithinAt (Ym x) (-f (Ym x t)) (Ici 0) t :=
    global_integral_hasDerivWithinAt (fun z => -f z) hf.continuous.neg x
      (Ym x) (hmc x) (hme x) t ht
  refine ⟨Φ, hΦ0, ?_⟩
  intro t x
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hd := ((hmd x (-t) (by linarith)).hasDerivAt (Ici_mem_nhds (by linarith)))
      |>.scomp t (hasDerivAt_neg t)
    have he : (fun r => Φ (r, x)) =ᶠ[𝓝 t] (fun r => Ym x (-r)) := by
      filter_upwards [eventually_lt_nhds ht] with r hr
      simp [Φ, not_le.mpr hr]
    simpa only [Function.comp_apply, neg_smul, one_smul, neg_neg,
      Φ, ite_eq_right (not_le.mpr ht)] using hd.congr_of_eventuallyEq he
  · have hp : HasDerivWithinAt (fun r => Φ (r, x)) (f x) (Ici 0) 0 := by
      have hd := hpd x 0 le_rfl
      rw [hp0 x] at hd
      exact hd.congr (fun r hr => by simp [Φ, show 0 ≤ r from hr]) (by simp [Φ])
    have hm : HasDerivWithinAt (fun r => Φ (r, x)) (f x) (Iic 0) 0 := by
      have hd0 := hmd x 0 le_rfl
      have hd : HasDerivWithinAt (fun r => Ym x (-r)) (f x) (Iic 0) 0 := by
        have hc := (hmd x (-0) (by norm_num)).scomp 0
          ((hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt (s := Iic 0))
          (show MapsTo (fun r : ℝ => -r) (Iic 0) (Ici 0) from
            fun r hr => by
              change 0 ≤ -r
              exact neg_nonneg.mpr (show r ≤ 0 from hr))
        simpa [Function.comp_def, hm0] using hc
      apply hd.congr
      · intro r hr
        rcases lt_or_eq_of_le (show r ≤ 0 from hr) with hr | rfl
        · simp [Φ, not_le.mpr hr]
        · simp [hΦ0, hm0]
      · simp [hΦ0, hm0]
    have hu := hp.union hm
    rw [Ici_union_Iic] at hu
    simpa only [hΦ0] using hu.hasDerivAt (by simp)
  · have hd := (hpd x t ht.le).hasDerivAt (Ici_mem_nhds ht)
    have he : (fun r => Φ (r, x)) =ᶠ[𝓝 t] Yp x := by
      filter_upwards [eventually_gt_nhds ht] with r hr
      simp [Φ, hr.le]
    simpa only [Φ, ite_eq_left ht.le] using hd.congr_of_eventuallyEq he

end PBGSO
