import UnadjustedLangevin.EulerLimit

/-! # Euler convergence on vanishing meshes with varying endpoints

The number of steps may depend on the mesh. The elapsed times need only stay
in a fixed compact interval and converge to the desired time. This is the
common-mesh approximation needed to pass a discrete Markov composition law
to the actual continuous-time Langevin operators.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology

namespace WassersteinMixing

variable {H I : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {l : Filter I}

/-- The deterministic matching-noise Euler approximation converges at varying
elapsed times on any mesh tending to zero. -/
theorem additiveEulerChain_variable_tendsto
    (g : H → H) (L : ℝ≥0) (hLip : LipschitzWith L g)
    (x : H) (B Y : ℝ → H) (hB0 : B 0 = 0) (hY : Continuous Y)
    (T : ℝ) (hT : 0 ≤ T)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (step : I → ℝ) (count : I → ℕ) (hstep : ∀ i, 0 ≤ step i)
    (hmesh : Tendsto step l (𝓝 0)) (hbound : ∀ i, (count i : ℝ) * step i ≤ T)
    (t : ℝ) (htime : Tendsto (fun i ↦ (count i : ℝ) * step i) l (𝓝 t)) :
    Tendsto (fun i ↦ ULA.additiveEulerChain g (step i) x B (count i)) l (𝓝 (Y t)) := by
  have herror : Tendsto (fun i ↦
      ‖ULA.additiveEulerChain g (step i) x B (count i) - Y ((count i : ℝ) * step i)‖)
      l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let C := T * Real.exp ((L : ℝ) * T)
    have hC : 0 ≤ C := mul_nonneg hT (Real.exp_pos _).le
    let η := ε / (C + 1)
    have hη : 0 < η := div_pos hε (by positivity)
    have hscale : η * (C + 1) = ε := div_mul_cancel₀ _ (by positivity)
    have hsmall : T * η * Real.exp ((L : ℝ) * T) < ε := by
      have he : T * η * Real.exp ((L : ℝ) * T) = C * η := by dsimp [C]; ring
      rw [he]
      nlinarith
    have huc : UniformContinuousOn (fun s ↦ g (Y s)) (Icc 0 T) :=
      isCompact_Icc.uniformContinuousOn_of_continuous (hLip.continuous.comp hY).continuousOn
    obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff_le.mp huc η hη
    filter_upwards [hmesh.eventually (gt_mem_nhds hδ)] with i hi
    let ti := (count i : ℝ) * step i
    have hti : 0 ≤ ti := mul_nonneg (Nat.cast_nonneg _) (hstep i)
    have htiT : ti ≤ T := hbound i
    have hb := ULA.additiveEulerChain_error_le_of_drift_modulus g L hLip x B Y hB0 hY
      ti (step i) η hti (hstep i) hη.le (count i) rfl
      (fun s hs ↦ hYe s ⟨hs.1, hs.2.trans htiT⟩)
      (fun s hs u hu hsu ↦ by
        simpa only [dist_eq_norm] using
          hosc s ⟨hs.1, hs.2.trans htiT⟩ u ⟨hu.1, hu.2.trans htiT⟩
            (hsu.trans hi.le))
    have hm : ti * η * Real.exp ((L : ℝ) * ti) ≤
        T * η * Real.exp ((L : ℝ) * T) := by
      gcongr
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact hb.trans_lt (hm.trans_lt hsmall)
  have htarget : Tendsto (fun i ↦ Y ((count i : ℝ) * step i)) l (𝓝 (Y t)) :=
    (hY.tendsto t).comp htime
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have htarget0 := tendsto_iff_norm_sub_tendsto_zero.mp htarget
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    (by simpa only [add_zero] using herror.add htarget0)
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

end WassersteinMixing
