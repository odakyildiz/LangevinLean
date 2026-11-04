import WassersteinMixing.SemigroupContinuity
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # The Hilbert range of state-measurable observables

Doob--Dynkin factorization identifies every square-integrable function of a
state with an actual target-law observable. Conditional expectations that are
functions of that state are consequently the concrete adjoint compression.
-/
noncomputable section
set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory

namespace WassersteinMixing

section Range
variable {Ω A F : Type*} [mΩ : MeasurableSpace Ω] [mA : MeasurableSpace A]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (Q : Measure Ω) (μ : Measure A) (X : Ω → A) (hX : MeasurePreserving X Q μ)

/-- Every actual square-integrable function of a state is an evaluated
square-integrable observable of its exact law. -/
theorem observable_range_of_state_measurable (Z : Lp F 2 Q)
    (hZ : AEStronglyMeasurable[mA.comap X] Z Q) :
    ∃ f : Lp F 2 μ, Lp.compMeasurePreservingₗᵢ ℝ X hX f = Z := by
  obtain ⟨g, hg, hfac⟩ := hZ.stronglyMeasurable_mk.exists_eq_measurable_comp
  have heq : (Z : Ω → F) =ᵐ[Q] g ∘ X := by
    rw [← hfac]
    exact hZ.ae_eq_mk
  have hc : MemLp (g ∘ X) 2 Q := (memLp_congr_ae heq).mp (Lp.memLp Z)
  have hm : MemLp g 2 μ := by
    rw [← hX.map_eq]
    exact (memLp_map_measure_iff hg.aestronglyMeasurable hX.measurable.aemeasurable).mpr hc
  refine ⟨hm.toLp g, ?_⟩
  apply Lp.ext
  have he := Lp.coeFn_compMeasurePreserving (hm.toLp g) hX
  have hgcoe := hX.quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp
  filter_upwards [he, hgcoe, heq] with ω hp hgp hzp
  exact hp.trans (hgp.trans hzp.symm)

end Range

section Projection
variable {Ω R F : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  (Q : Measure Ω) (J : R →ₗᵢ[ℝ] Lp F 2 Q)

/-- Isometric evaluation followed by its adjoint is the identity on its range. -/
theorem evaluation_projection_eq_of_mem_range (Z : Lp F 2 Q) (hZ : Z ∈ Set.range J) :
    J (J.toContinuousLinearMap.adjoint Z) = Z := by
  obtain ⟨f, rfl⟩ := hZ
  have h := congrArg (fun T : R →L[ℝ] R ↦ T f) J.adjoint_comp_self
  change J.toContinuousLinearMap.adjoint (J f) = f at h
  rw [h]

/-- Conditioning onto a larger past leaves the state compression unchanged
whenever its conditional mean is a function of the current state. -/
theorem conditional_eq_evaluation_adjoint {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (Y : Lp F 2 Q)
    (hJ : ∀ f, AEStronglyMeasurable[m] (J f) Q)
    (hZ : (condExpL2 F ℝ hm Y : Lp F 2 Q) ∈ Set.range J) :
    (condExpL2 F ℝ hm Y : Lp F 2 Q) = J (J.toContinuousLinearMap.adjoint Y) := by
  have ha : J.toContinuousLinearMap.adjoint (condExpL2 F ℝ hm Y : Lp F 2 Q) =
      J.toContinuousLinearMap.adjoint Y := by
    apply ext_inner_right ℝ
    intro f
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    exact inner_condExpL2_eq_inner_fun (𝕜 := ℝ) hm Y (J f) (hJ f)
  calc
    _ = J (J.toContinuousLinearMap.adjoint (condExpL2 F ℝ hm Y : Lp F 2 Q)) :=
      (evaluation_projection_eq_of_mem_range (mΩ := mΩ) Q J _ hZ).symm
    _ = _ := congrArg J ha

end Projection
end WassersteinMixing
