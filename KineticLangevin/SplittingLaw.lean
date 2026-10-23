import KineticLangevin.KineticSplittingLp
import KineticLangevin.LpPhaseLaw
import UnadjustedLangevin.MarkovLaw

/-! # Actual splitting laws from the complete initial/noise joint law -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace KineticLangevin
section General
variable {Ω H Z : Type*} [MeasurableSpace Ω] [MeasurableSpace H] [MeasurableSpace Z]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- A concrete random recursion with the actual product initial/entire-iid-
stream law has precisely the implemented Markov iterate law. -/
theorem noiseDrivenChain_law_of_jointLaw
    (step : H → Z → H) (hstep : Measurable (Function.uncurry step))
    (π : Measure H) [IsProbabilityMeasure π] (Q : Measure Z) [IsProbabilityMeasure Q]
    (X : Ω → H) (N : ℕ → Ω → Z)
    (hjoint : HasLaw (fun ω ↦ (X ω,fun k ↦ N k ω))
      (π.prod (Measure.infinitePi (fun _ : ℕ ↦ Q))) P) (n : ℕ) :
    P.map (fun ω ↦ ULA.noiseDrivenChain step (X ω) (fun k ↦ N k ω) n) =
      ULA.markovLaws step Q π n := by
  have hc : HasLaw (fun p : H×(ℕ→Z) ↦ ULA.noiseDrivenChain step p.1 p.2 n)
      (ULA.chainLaw step π (Measure.infinitePi (fun _ : ℕ ↦ Q)) n)
      (π.prod (Measure.infinitePi (fun _ : ℕ ↦ Q))) :=
    ⟨(ULA.noiseDrivenChain_measurable step hstep n).aemeasurable,rfl⟩
  exact (hc.comp hjoint).map_eq.trans (ULA.chainLaw_eq_markovLaws step hstep π Q n)

/-- An actual source stream with its proved law remains independent of the
initial coordinate on the explicit initial-law/source product. -/
theorem jointLaw_product_source {S : Type*} [MeasurableSpace S]
    (π : Measure H) [IsProbabilityMeasure π] (Q : Measure S) [IsProbabilityMeasure Q]
    (η : Measure Z) [IsProbabilityMeasure η] (W : S → ℕ → Z) (hW : Measurable W)
    (hlaw : HasLaw W (Measure.infinitePi (fun _ : ℕ ↦ η)) Q) :
    HasLaw (fun p : H×S ↦ (p.1,W p.2))
      (π.prod (Measure.infinitePi (fun _ : ℕ ↦ η))) (π.prod Q) := by
  refine ⟨(measurable_fst.prodMk (hW.comp measurable_snd)).aemeasurable,?_⟩
  have hr := Measure.map_prod_map π Q measurable_id hW
  rw [Measure.map_id,hlaw.map_eq] at hr
  simpa only [Prod.map_def,id_eq] using hr.symm

end General
section Splitting
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The explicit Verlet--OU recursion agrees with the generic random
recursion for precisely the same supplied innovation sequence. -/
theorem kineticSplitNoiseChain_eq_noiseDrivenChain (g : E → E) (γ h : ℝ)
    (initial : E×E) (N : ℕ → E) (n : ℕ) :
    kineticSplitNoiseChain g γ h initial N n =
      ULA.noiseDrivenChain (kineticSplitStep g γ h) initial N n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [kineticSplitNoiseChain,ULA.noiseDrivenChain_succ,ih]

/-- The actual pointwise Verlet--OU step is jointly measurable. -/
theorem kineticSplitStep_measurable (g : E → E) (hg : Continuous g) (γ h : ℝ) :
    Measurable (Function.uncurry (kineticSplitStep g γ h)) := by
  apply Continuous.measurable
  unfold Function.uncurry kineticSplitStep verletStep ornsteinStep kickStep driftStep
  fun_prop

/-- The actual L² splitting chain has the Markov law specified by its full
initial/noise joint distribution. Its representatives introduce no extra law
hypothesis and cannot change the resulting transition. -/
theorem lp_kineticSplitNoiseChain_law_of_jointLaw
    (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g) (γ h : ℝ)
    (initial : Lp E 2 P × Lp E 2 P) (N : ℕ → Lp E 2 P)
    (π : Measure (E×E)) [IsProbabilityMeasure π]
    (Q : Measure E) [IsProbabilityMeasure Q]
    (hjoint : HasLaw (fun ω ↦ (lpPhaseCoe P initial ω,fun k ↦ N k ω))
      (π.prod (Measure.infinitePi (fun _ : ℕ ↦ Q))) P) (n : ℕ) :
    P.map (lpPhaseCoe P (kineticSplitNoiseChain (ULA.lpDrift P g hg) γ h initial N n)) =
      ULA.markovLaws (kineticSplitStep g γ h) Q π n := by
  rw [Measure.map_congr (lp_kineticSplitNoiseChain_coe P g M hg γ h initial N n)]
  simp_rw [kineticSplitNoiseChain_eq_noiseDrivenChain]
  exact noiseDrivenChain_law_of_jointLaw P (kineticSplitStep g γ h)
    (kineticSplitStep_measurable g hg.continuous γ h) π Q (lpPhaseCoe P initial)
    (fun k ω ↦ N k ω) hjoint n

end Splitting
end KineticLangevin
