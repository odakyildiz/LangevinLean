import KineticLangevin.OUMarginal
import KineticLangevin.GibbsTarget
import KineticLangevin.MarkovTests
import KineticLangevin.HamiltonianTests

/-! # Actual kinetic splitting has a proved quadratic stationary weak defect -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual additive OU innovation law at the chosen friction and step. -/
def ouThermalLaw (γ h : ℝ) : Measure E :=
  (stdGaussian E).map (fun x ↦ Real.sqrt (1-(psi γ 0 h)^2) • x)

instance ouThermalLaw_probability (γ h : ℝ) : IsProbabilityMeasure (ouThermalLaw (E := E) γ h) := by
  unfold ouThermalLaw
  infer_instance

/-- The finite target's exact corrected Verlet identity follows by scaling
the already proved actual Hamiltonian Gibbs measure identity. -/
theorem correctedVerlet_preserves_target (f : E → ℝ) (hf : Measurable f)
    (hg : Measurable (gradient f)) (h : ℝ) :
    ((kineticGibbsTarget f).withDensity (fun z ↦ ENNReal.ofReal (verletAcceptance f h z))).map
        (verletStep (gradient f) h) +
      ((kineticGibbsTarget f).withDensity (fun z ↦ ENNReal.ofReal (1-verletAcceptance f h z))).map
        reverseVelocity = kineticGibbsTarget f := by
  rw [kineticGibbsTarget_eq_scaled f hf,withDensity_smul_measure,withDensity_smul_measure,
    Measure.map_smul _ (verletStep_measurePreserving volume (gradient f) hg h).measurable.aemeasurable,
    Measure.map_smul _ (reverseVelocity_measurePreserving (volume : Measure E)).measurable.aemeasurable,
    ← smul_add,correctedVerlet_preserves_gibbs volume f hf hg h]

/-- The precise quadratic envelope in the rejection bound is integrable
under the actual normalized canonical target. -/
theorem kineticGibbsTarget_phase_moment (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (M : ℝ≥0) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) :
    Integrable (fun z : E×E ↦ ‖z.1‖^2+‖gradient f z.2‖^2) (kineticGibbsTarget f) := by
  rw [kineticGibbsTarget_eq_scaled f hf.continuous.measurable]
  apply (hamiltonianGibbs_phase_moment f m hm M hf hsc hLip).smul_measure
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ULA.gibbsPartition_pos f hf)))

/-- The additive OU innovation law preserves the actual normalized target. -/
theorem ouThermalStep_preserves_target (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (γ h : ℝ) (hγ : 0≤γ) (hh : 0≤h) :
    ULA.markovStep (fun z N ↦ ornsteinStep (Real.exp (-γ*h)) 1 N z)
      (ouThermalLaw (E := E) γ h) (kineticGibbsTarget f) = kineticGibbsTarget f := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let δ := Real.exp (-γ*h)
  let σ := Real.sqrt (1-(psi γ 0 h)^2)
  have hp : 0≤1-(psi γ 0 h)^2 := by
    have h0 := psi_nonneg γ 0 hh
    have h1 := psi_zero_le_one hγ hh
    nlinarith
  have hab : δ^2+σ^2=1 := by
    change (psi γ 0 h)^2+(Real.sqrt (1-(psi γ 0 h)^2))^2=1
    rw [Real.sq_sqrt hp]
    ring
  have ht := thermostat_preserves_target f m hm hf hsc δ σ hab
  have hmapping := Measure.map_prod_map (kineticGibbsTarget f) (stdGaussian E)
    measurable_id (show Measurable (fun x : E ↦ σ • x) by fun_prop)
  rw [Measure.map_id] at hmapping
  unfold ULA.markovStep ouThermalLaw
  rw [hmapping,Measure.map_map (by unfold Function.uncurry ornsteinStep; fun_prop) (by fun_prop)]
  simpa only [Function.comp_def,Function.uncurry_apply_pair,Prod.map,ornsteinStep,
    one_smul,δ,σ,id_eq] using ht

/-- Averaging a test over the exact thermostat retains its bound; corrected
Verlet invariance therefore bounds the actual splitting stationary defect. -/
theorem kineticSplitStep_stationary_weak_error (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (M : ℝ≥0) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ) (hγ : 0≤γ) (hh : 0≤h) (hh1 : h≤1)
    (F : E×E → ℂ) (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hFb : ∀ z, ‖F z‖≤C) :
    ‖(∫ z,F z ∂ULA.markovStep (kineticSplitStep (gradient f) γ h)
      (ouThermalLaw (E := E) γ h) (kineticGibbsTarget f))-(∫ z,F z ∂kineticGibbsTarget f)‖ ≤
      2*C*h^2*((M : ℝ)*(2*(M : ℝ)+11)/8)*
        (∫ z,‖z.1‖^2+‖gradient f z.2‖^2 ∂kineticGibbsTarget f) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let π := kineticGibbsTarget f
  let Q := ouThermalLaw (E := E) γ h
  let O : (E×E) → E → (E×E) := fun z N ↦ ornsteinStep (Real.exp (-γ*h)) 1 N z
  have hO : Measurable (Function.uncurry O) := by dsimp [O,Function.uncurry,ornsteinStep]; fun_prop
  have hV := (verletStep_measurePreserving volume (gradient f) hLip.continuous.measurable h).measurable
  let G := markovTest O Q F
  have hG : Measurable G := markovTest_measurable O hO Q F hF
  have hGb : ∀ z, ‖G z‖≤C := markovTest_norm_le O Q F C hC hFb
  have hstat := ouThermalStep_preserves_target f m hm hf hsc γ h hγ hh
  have hmean : (∫ z,G z ∂π)=(∫ z,F z ∂π) := by
    have he := markovStep_integral_test O hO Q π F hF C hFb
    rw [hstat] at he
    exact he.symm
  have hw := correctedMeasure_weak_error π (verletStep (gradient f) h) reverseVelocity hV
    (reverseVelocity_measurePreserving (volume : Measure E)).measurable
    (verletAcceptance f h) (verletAcceptance_measurable f hf.continuous.measurable hLip.continuous.measurable h)
    (verletAcceptance_nonneg f h) (verletAcceptance_le_one f h)
    (correctedVerlet_preserves_target f hf.continuous.measurable hLip.continuous.measurable h)
    G hG C hC hGb
  have hre := verlet_rejection_integral_le π f M hf hLip
    (kineticGibbsTarget_phase_moment f m hm M hf hsc hLip) h hh hh1
  have hgrad : Measurable (gradient f) := hLip.continuous.measurable
  have hs : Measurable (Function.uncurry (kineticSplitStep (gradient f) γ h)) := by
    unfold Function.uncurry kineticSplitStep verletStep kickStep driftStep ornsteinStep
    fun_prop
  rw [markovStep_integral_test (kineticSplitStep (gradient f) γ h) hs Q π F hF C hFb]
  change ‖(∫ z,G (verletStep (gradient f) h z) ∂π)-(∫ z,F z ∂π)‖≤_
  rw [← hmean]
  exact (hw.trans (mul_le_mul_of_nonneg_left hre (by positivity : 0≤2*C))).trans_eq (by ring)

/-- The actual independent-noise splitting Markov law accumulates only a
linear number of the proved quadratic weak defects. -/
theorem kineticSplitLaws_stationary_weak_error (f : E → ℝ) (m : ℝ) (hm : 0<m)
    (M : ℝ≥0) (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (γ h : ℝ) (hγ : 0≤γ) (hh : 0≤h) (hh1 : h≤1)
    (F : E×E → ℂ) (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hFb : ∀ z, ‖F z‖≤C)
    (n : ℕ) :
    ‖(∫ z,F z ∂ULA.markovLaws (kineticSplitStep (gradient f) γ h)
      (ouThermalLaw (E := E) γ h) (kineticGibbsTarget f) n)-(∫ z,F z ∂kineticGibbsTarget f)‖ ≤
      (n : ℝ)*(2*C*h^2*((M : ℝ)*(2*(M : ℝ)+11)/8)*
        (∫ z,‖z.1‖^2+‖gradient f z.2‖^2 ∂kineticGibbsTarget f)) := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  have hgrad : Measurable (gradient f) := hLip.continuous.measurable
  have hs : Measurable (Function.uncurry (kineticSplitStep (gradient f) γ h)) := by
    unfold Function.uncurry kineticSplitStep verletStep kickStep driftStep ornsteinStep
    fun_prop
  have hB : 0≤∫ z,‖z.1‖^2+‖gradient f z.2‖^2 ∂kineticGibbsTarget f :=
    integral_nonneg (fun _ ↦ by positivity)
  exact markovLaws_weak_error (kineticSplitStep (gradient f) γ h) hs (ouThermalLaw γ h)
    (kineticGibbsTarget f) C _ hC (by positivity)
    (fun G hG hGb ↦ kineticSplitStep_stationary_weak_error f m hm M hf hsc hLip
      γ h hγ hh hh1 G hG C hC hGb) F hF hFb n

end KineticLangevin
