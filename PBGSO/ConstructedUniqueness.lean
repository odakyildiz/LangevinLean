import PBGSO.ConstructedStationarity

/-! # Actual same-driver uniqueness from source joint dissipation
This discharges the restricted stationarity uniqueness condition whenever
source A3 is available, using the computed Brownian difference integral.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.ConstructedStationarity
open FilteredBrownian ConstructedPredictableModel
variable {Ω S Θ Z X I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)
  (M : Model S Θ Z X I) (T : ℝ≥0)

/-- One-sided joint dissipativity proves actual same-initial pathwise
uniqueness in the constructed time-L¹-drift/time-L²-diffusion data class.
Positive rate is unnecessary for uniqueness itself. -/
theorem dataUniqueness_of_twisted (G : TwistedGeometry S Z)
    (hb : ∀ θ, Measurable (M.drift θ))
    (hσ : ∀ θ i, Measurable (fun z => M.diffusion θ z i))
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M G ρ) : DataUniqueness Q D M T := by
  intro U V hs hz t ht
  have hIso : IntegralModelContraction.SynchronousIsometry G
      ((U.trajectory hb).restrict ht) ((V.trajectory hb).restrict ht) := by
    intro r hr
    exact (ConstructedPredictableModel.synchronous_isometry G U V hb) r ⟨hr.1, hr.2.trans ht.2⟩
  have hd := IntegralModelContraction.pair_rms_decay G
    ((U.trajectory hb).restrict ht) ((V.trajectory hb).restrict ht) ht.1 hb hσ ρ hmono hIso
  change Real.sqrt (‖U.optimizer t - V.optimizer t‖ ^ 2 + ‖U.sampler t - V.sampler t‖ ^ 2) ≤
    Real.sqrt G.conditionNumber * Real.exp (-ρ * t) *
      Real.sqrt (‖U.optimizer 0 - V.optimizer 0‖ ^ 2 + ‖U.sampler 0 - V.sampler 0‖ ^ 2) at hd
  simp only [hs, hz, sub_self, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
    add_zero, Real.sqrt_zero, mul_zero] at hd
  have he := congrArg (fun x : ℝ => x ^ 2) (le_antisymm hd (Real.sqrt_nonneg _))
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
    zero_pow (by decide : (2 : ℕ) ≠ 0)] at he
  have ho : ‖U.optimizer t - V.optimizer t‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖U.sampler t - V.sampler t‖]
  have hz' : ‖U.sampler t - V.sampler t‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖U.optimizer t - V.optimizer t‖]
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp ho)),
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz'))⟩

end PBGSO.ConstructedStationarity
