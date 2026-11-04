import WassersteinMixing.ActualAdapted
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic

/-! # Independence of the actual Brownian future and past

These results use the explicitly constructed independent Gaussian coordinates.
Independence concerns whole paths, rather than just one past value or one
future increment.
-/

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace WassersteinMixing

private theorem iIndep_bool_of_indep {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (m : Bool → MeasurableSpace Ω)
    (hi : Indep (m false) (m true) Q) : iIndep m Q := by
  rw [iIndep_iff]
  intro s f hf
  fin_cases s
  · simp
  · change Q (⋂ i ∈ ({true} : Finset Bool), f i) = _
    simp
  · change Q (⋂ i ∈ ({false} : Finset Bool), f i) = _
    simp
  · change Q (⋂ i ∈ ({true, false} : Finset Bool), f i) = _
    have he : (⋂ i : Bool, f i) = f false ∩ f true := by
      ext x
      simp [Bool.forall_bool]
    simpa [he, mul_comm] using
      hi (f false) (f true) (hf false (by simp)) (hf true (by simp))

/-- Independent rows of independent pairs can be regrouped into an independent
left family and right family. No countability restriction on the row index is
needed. -/
theorem indepFun_families_of_independent_pairs {Ω I A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (X Y : I → Ω → A)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (hrows : iIndepFun (fun i ω ↦ (X i ω, Y i ω)) Q)
    (hpair : ∀ i, IndepFun (X i) (Y i) Q) :
    IndepFun (fun ω i ↦ X i ω) (fun ω i ↦ Y i ω) Q := by
  let Z : I → Bool → Ω → A := fun i b ω ↦ cond b (X i ω) (Y i ω)
  have hZ : ∀ i b, Measurable (Z i b) := by
    intro i b
    cases b <;> simp only [Z, Bool.cond_false, Bool.cond_true]
    · exact hY i
    · exact hX i
  have hrow : iIndepFun (fun i ω b ↦ Z i b ω) Q := by
    exact hrows.comp (fun _ p b ↦ cond b p.1 p.2) (by
      intro i
      exact measurable_pi_iff.mpr (by
        intro b
        cases b
        · exact measurable_snd
        · exact measurable_fst))
  have hp : ∀ i, iIndepFun (Z i) Q := by
    intro i
    apply iIndep_bool_of_indep
    exact (hpair i).symm
  have hi := iIndepFun_uncurry' hZ hrow hp
  let m : I × Bool → MeasurableSpace Ω := fun p ↦ (inferInstance : MeasurableSpace A).comap (Z p.1 p.2)
  have hm : ∀ p, m p ≤ (inferInstance : MeasurableSpace Ω) := fun p ↦ (hZ p.1 p.2).comap_le
  have hind : iIndep m Q := hi
  have hd : Disjoint {p : I × Bool | p.2 = true} {p : I × Bool | p.2 = false} := by
    simp [Set.disjoint_left]
  have hs := indep_iSup_of_disjoint hm hind hd
  change Indep ((inferInstance : MeasurableSpace (I → A)).comap (fun ω i ↦ X i ω))
    ((inferInstance : MeasurableSpace (I → A)).comap (fun ω i ↦ Y i ω)) Q
  apply indep_of_indep_of_le_right (indep_of_indep_of_le_left hs ?_) ?_
  · simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    apply iSup_le
    intro i
    exact (le_iSup_of_le (i, true) (le_iSup_of_le (by simp) le_rfl))
  · simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    apply iSup_le
    intro i
    exact (le_iSup_of_le (i, false) (le_iSup_of_le (by simp) le_rfl))

/-- The whole future of the constructed vector Brownian source is independent
of its whole past, with past time clipped at the cut time. -/
theorem canonicalBrownian_future_past_independent (I : Type*) (a : ℝ≥0) :
    IndepFun
      (fun (ω : ULA.CanonicalBrownian.VectorSample I) i t ↦
        ULA.CanonicalBrownian.coordinate i (a + t) ω - ULA.CanonicalBrownian.coordinate i a ω)
      (fun (ω : ULA.CanonicalBrownian.VectorSample I) i t ↦
        ULA.CanonicalBrownian.coordinate i (min t a) ω)
      (ULA.CanonicalBrownian.vectorProbability I) := by
  apply indepFun_families_of_independent_pairs
  · intro i
    exact measurable_pi_iff.mpr (fun t ↦ by
      exact (ULA.CanonicalBrownian.process_measurable _).comp (measurable_pi_apply i) |>.sub
        ((ULA.CanonicalBrownian.process_measurable _).comp (measurable_pi_apply i)))
  · intro i
    exact measurable_pi_iff.mpr (fun t ↦
      (ULA.CanonicalBrownian.process_measurable _).comp (measurable_pi_apply i))
  · exact (ULA.CanonicalBrownian.coordinate_paths_independent I).comp
      (fun _ p ↦ ((fun t ↦ p (a + t) - p a), fun t ↦ p (min t a)))
      (fun _ ↦ by fun_prop)
  · intro i
    let ψ : (Iic a → ℝ) → (ℝ≥0 → ℝ) := fun p t ↦ p ⟨min t a, by exact min_le_right t a⟩
    have hψ : Measurable ψ := measurable_pi_iff.mpr (fun t ↦ measurable_pi_apply _)
    have hi : IndepFun
        (fun (ω : ULA.CanonicalBrownian.VectorSample I) t ↦
          ULA.CanonicalBrownian.coordinate i (a + t) ω - ULA.CanonicalBrownian.coordinate i a ω)
        (fun (ω : ULA.CanonicalBrownian.VectorSample I) (t : Iic a) ↦
          ULA.CanonicalBrownian.coordinate i t ω)
        (ULA.CanonicalBrownian.vectorProbability I) :=
      (ULA.CanonicalBrownian.coordinate_isPreBrownian i).indepFun_shift a
    exact hi.comp (φ := id) (ψ := ψ) measurable_id hψ

/-- An independent initial sample can be adjoined to the past without revealing
any information about the independent future. -/
theorem indepFun_future_initial_past {Ω₀ Ω A B : Type*}
    [MeasurableSpace Ω₀] [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure Ω₀) (ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y ν) :
    IndepFun (fun ω : Ω₀ × Ω ↦ X ω.2) (fun ω : Ω₀ × Ω ↦ (ω.1, Y ω.2)) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hmX : Measurable (fun ω : Ω₀ × Ω ↦ X ω.2) := hX.comp measurable_snd
  have hmY : Measurable (fun ω : Ω₀ × Ω ↦ (ω.1, Y ω.2)) :=
    measurable_fst.prodMk (hY.comp measurable_snd)
  have hm : MeasurableSet ((fun ω : Ω₀ × Ω ↦ X ω.2) ⁻¹' s ∩
      (fun ω : Ω₀ × Ω ↦ (ω.1, Y ω.2)) ⁻¹' t) := (hmX hs).inter (hmY ht)
  rw [Measure.prod_apply hm, Measure.prod_apply (hmX hs), Measure.prod_apply (hmY ht)]
  change (∫⁻ a, ν (X ⁻¹' s ∩ Y ⁻¹' (Prod.mk a ⁻¹' t)) ∂μ) =
    (∫⁻ _ : Ω₀, ν (X ⁻¹' s) ∂μ) * (∫⁻ a, ν (Y ⁻¹' (Prod.mk a ⁻¹' t)) ∂μ)
  simp only [lintegral_const, measure_univ, mul_one]
  rw [← lintegral_const_mul' _ _ (measure_ne_top _ _)]
  apply lintegral_congr
  intro a
  exact hi.measure_inter_preimage_eq_mul s (Prod.mk a ⁻¹' t) hs (measurable_prodMk_left ht)

/-- Actual whole-path independence on the initial/Brownian product source. -/
theorem actualBrownian_raw_future_initial_past_independent
    (P : Parameters) (V : E P.dimension → ℝ) (hV : PotentialAssumptions P V) (a : ℝ≥0) :
    IndepFun
      (fun (ω : ActualSpace P) i t ↦
        CanonicalSemigroup.brownian P i (a + t) ω - CanonicalSemigroup.brownian P i a ω)
      (fun (ω : ActualSpace P) ↦ (ω.1, fun i t ↦ CanonicalSemigroup.brownian P i (min t a) ω))
      (actualProbability P V) := by
  let := actualTarget_isProbability P V hV
  let := (diagonalGibbsCoupling P V).isProbabilityMeasure
  change IndepFun _ _ ((diagonalGibbsCoupling P V).joint.prod
    (ULA.CanonicalBrownian.vectorProbability (Fin P.dimension)))
  exact indepFun_future_initial_past _ _ _ _ (by
    exact measurable_pi_iff.mpr (fun i ↦ measurable_pi_iff.mpr (fun t ↦
      ((ULA.CanonicalBrownian.process_measurable _).comp (measurable_pi_apply i)).sub
      ((ULA.CanonicalBrownian.process_measurable _).comp (measurable_pi_apply i)))))
    (by exact measurable_pi_iff.mpr (fun i ↦ measurable_pi_iff.mpr (fun t ↦
      (ULA.CanonicalBrownian.process_measurable _).comp (measurable_pi_apply i))))
    (canonicalBrownian_future_past_independent _ a)

end WassersteinMixing
