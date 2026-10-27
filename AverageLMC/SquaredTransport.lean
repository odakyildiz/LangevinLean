import UnadjustedLangevin.InitialExtension
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Tactic

set_option linter.style.header false

/-! # Lifting output couplings and taking the quadratic transport infimum

The SGLD proof couples the full-gradient output with the target, then adds a
centered finite-index perturbation. Disintegration constructs that coupling
on the original input space; no optimal coupling is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace AverageLMC

variable {S E : Type*} [MeasurableSpace S] [MeasurableSpace E]
  [NormedAddCommGroup E]

/-- Squared estimates uniform over finite-cost couplings pass to the actual
transport infimum. The output distance is finite before using its real value. -/
theorem real_bound_of_finite_couplings
    (μ π : Measure E) (r a b : ℝ)
    (hfinite : ULA.wasserstein2 μ π ≠ ⊤)
    (hfamily : ∀ c : ULA.Coupling μ π, ULA.couplingCost c.joint ≠ ⊤ →
      r ≤ a * (ULA.couplingCost c.joint).toReal ^ 2 + b) :
    r ≤ a * ULA.wasserstein2Real μ π ^ 2 + b := by
  have hw : 0 ≤ ULA.wasserstein2Real μ π := ENNReal.toReal_nonneg
  by_cases ha : 0 ≤ a
  · have heps (ε : ℝ) (hε : 0 < ε) :
        r ≤
          a * (ULA.wasserstein2Real μ π + ε) ^ 2 + b := by
      have hi : ULA.wasserstein2 μ π <
          ENNReal.ofReal (ULA.wasserstein2Real μ π + ε) := by
        rw [← ENNReal.ofReal_toReal hfinite]
        apply (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < ULA.wasserstein2Real μ π + ε)).mpr
        change (ULA.wasserstein2 μ π).toReal < (ULA.wasserstein2 μ π).toReal + ε
        linarith
      obtain ⟨c, hc⟩ := iInf_lt_iff.mp hi
      have hcf : ULA.couplingCost c.joint ≠ ⊤ := ne_top_of_lt hc
      have hreal : (ULA.couplingCost c.joint).toReal ≤
          ULA.wasserstein2Real μ π + ε := by
        have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc.le
        simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ ULA.wasserstein2Real μ π + ε)] using ht
      have hsq := (sq_le_sq₀ ENNReal.toReal_nonneg (by linarith)).mpr hreal
      exact (hfamily c hcf).trans (add_le_add (mul_le_mul_of_nonneg_left hsq ha) le_rfl)
    have hlim : Tendsto (fun ε : ℝ ↦ a * (ULA.wasserstein2Real μ π + ε) ^ 2 + b)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (a * ULA.wasserstein2Real μ π ^ 2 + b)) := by
      have hcont : Continuous (fun ε : ℝ ↦ a * (ULA.wasserstein2Real μ π + ε) ^ 2 + b) := by
        fun_prop
      simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Ioi 0))
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (by filter_upwards [self_mem_nhdsWithin] with ε hε using heps ε hε)
  · obtain ⟨c, hc⟩ := ULA.exists_finiteCost_coupling μ π hfinite
    have hcf : ULA.couplingCost c.joint ≠ ⊤ := ne_of_lt hc
    have hle := ENNReal.toReal_mono hcf (ULA.wasserstein2_le_couplingCost c)
    change ULA.wasserstein2Real μ π ≤ (ULA.couplingCost c.joint).toReal at hle
    have hsq := (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hle
    exact (hfamily c hcf).trans (add_le_add
      (mul_le_mul_of_nonpos_left hsq (le_of_not_ge ha)) le_rfl)

/-- Quadratic transport specialization, retaining output finiteness as an
explicit side condition before its real-valued distance is used. -/
theorem wasserstein2_sq_bound_of_finite_couplings
    (μ π μ' π' : Measure E) (a b : ℝ)
    (hfinite : ULA.wasserstein2 μ π ≠ ⊤)
    (_houtput : ULA.wasserstein2 μ' π' ≠ ⊤)
    (hfamily : ∀ c : ULA.Coupling μ π, ULA.couplingCost c.joint ≠ ⊤ →
      ULA.wasserstein2Real μ' π' ^ 2 ≤ a * (ULA.couplingCost c.joint).toReal ^ 2 + b) :
    ULA.wasserstein2Real μ' π' ^ 2 ≤ a * ULA.wasserstein2Real μ π ^ 2 + b :=
  real_bound_of_finite_couplings μ π (ULA.wasserstein2Real μ' π' ^ 2) a b hfinite hfamily

section Lift
variable [StandardBorelSpace E]

/-- A target coupling pulled back to the original state by a conditional
kernel. Its first coordinate retains the original input law. -/
def liftedOutputCoupling (P : Measure S) [IsProbabilityMeasure P]
    (F : S → E) (hF : Measurable F) {π : Measure E}
    (c : ULA.Coupling (P.map F) π) : Measure (S × E) :=
  have := c.isProbabilityMeasure
  P ⊗ₘ (c.joint.condKernel.comap F hF)

instance liftedOutputCoupling_probability (P : Measure S) [IsProbabilityMeasure P]
    (F : S → E) (hF : Measurable F) {π : Measure E}
    (c : ULA.Coupling (P.map F) π) :
    IsProbabilityMeasure (liftedOutputCoupling P F hF c) := by
  unfold liftedOutputCoupling
  infer_instance

theorem liftedOutputCoupling_fst (P : Measure S) [IsProbabilityMeasure P]
    (F : S → E) (hF : Measurable F) {π : Measure E}
    (c : ULA.Coupling (P.map F) π) :
    (liftedOutputCoupling P F hF c).map Prod.fst = P := by
  unfold liftedOutputCoupling
  exact Measure.fst_compProd _ _

/-- The full-gradient output and the lifted target reproduce exactly the
chosen coupling, including its cost. -/
theorem liftedOutputCoupling_output (P : Measure S) [IsProbabilityMeasure P]
    (F : S → E) (hF : Measurable F) {π : Measure E}
    (c : ULA.Coupling (P.map F) π) :
    (liftedOutputCoupling P F hF c).map (fun q ↦ (F q.1, q.2)) = c.joint := by
  haveI := c.isProbabilityMeasure
  have hfst : c.joint.fst = P.map F := c.fst
  have hdis := c.joint.disintegrate c.joint.condKernel
  rw [hfst] at hdis
  rw [← hdis]
  change (P ⊗ₘ (c.joint.condKernel.comap F hF)).map
    (fun q : S × E ↦ (F q.1, q.2)) = _
  ext A hA
  rw [Measure.map_apply (by fun_prop) hA,
    Measure.compProd_apply hA, Measure.compProd_apply (hA.preimage (by fun_prop)),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hA) hF]
  rfl

theorem liftedOutputCoupling_snd (P : Measure S) [IsProbabilityMeasure P]
    (F : S → E) (hF : Measurable F) {π : Measure E}
    (c : ULA.Coupling (P.map F) π) :
    (liftedOutputCoupling P F hF c).map Prod.snd = π := by
  have h := congrArg (fun Q : Measure (E × E) ↦ Q.map Prod.snd)
    (liftedOutputCoupling_output P F hF c)
  rw [Measure.map_map measurable_snd (by fun_prop), c.snd] at h
  exact h

end Lift
end AverageLMC
