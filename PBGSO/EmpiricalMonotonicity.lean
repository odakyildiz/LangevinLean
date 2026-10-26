import PBGSO.PaperTheorems
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! # Lifting the general law-level condition to actual empirical clouds

The pairing measure here is the actual empirical law of the paired particle
coordinates. Its two marginals are proved equal to the empirical cloud laws.
Joint monotonicity therefore applies to the actual finite-particle force and
the averaged synchronous diffusion correction, without an independence premise
for the interacting particles.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace PBGSO

section Empirical
variable {E F B : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
  [MeasurableSpace F] [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- All functions into a normed space are integrable against a nonempty
finite empirical law. No regularity or global growth condition is needed. -/
theorem empiricalLaw_integrable (N : ℕ) (hN : 0 < N) (z : Fin N → E) (f : E → B) :
    Integrable f (Model.empiricalLaw N z) := by
  unfold Model.empiricalLaw
  apply Integrable.smul_measure
  · exact integrable_finsetSum_measure.mpr (fun i _ => integrable_dirac (by simp))
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hN.ne')

/-- Empirical integration is exactly the arithmetic mean. -/
theorem integral_empiricalLaw [CompleteSpace B] (N : ℕ) (z : Fin N → E) (f : E → B) :
    (∫ x, f x ∂Model.empiricalLaw N z) = (N : ℝ)⁻¹ • ∑ i, f (z i) := by
  unfold Model.empiricalLaw
  rw [integral_smul_measure, integral_finsetSum_measure
    (fun i _ => integrable_dirac (by simp))]
  simp

/-- Pushforward commutes with the actual finite empirical law. -/
theorem empiricalLaw_map (N : ℕ) (z : Fin N → E) (f : E → F) (hf : Measurable f) :
    (Model.empiricalLaw N z).map f = Model.empiricalLaw N (f ∘ z) := by
  unfold Model.empiricalLaw
  rw [Measure.map_smul _ hf.aemeasurable, Measure.map_finset_sum' hf.aemeasurable]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact Measure.map_dirac' hf (z i)

end Empirical

variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z] [Fintype I]

/-- Pairing particle i with reference particle i is an actual measure
coupling. This property does not require the arrays to be independent. -/
theorem empiricalPair_isCoupling (N : ℕ) (z w : Fin N → Z) :
    IsCoupling (Model.empiricalLaw N (fun i => (z i, w i)))
      (Model.empiricalLaw N z) (Model.empiricalLaw N w) := by
  constructor
  · exact empiricalLaw_map N _ Prod.fst measurable_fst
  · exact empiricalLaw_map N _ Prod.snd measurable_snd

/-- The actual averaged twisted separation of two finite clouds. -/
def particleCouplingEnergy (D : TwistedGeometry S Z) (N : ℕ)
    (s s' : S) (z w : Fin N → Z) : ℝ :=
  D.optimizerSq (s - s') + (N : ℝ)⁻¹ * ∑ i, D.samplerSq (z i - w i)

/-- The empirical joint work, including the full weighted diffusion
correction for each synchronously driven sampler. -/
def particleCouplingWork (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (N : ℕ) (t : ℝ) (s s' : S) (z w : Fin N → Z) : ℝ :=
  ⟪s - s', D.optimizerWeight
    (M.particleField N t s z - M.particleField N t s' w)⟫ +
    (N : ℝ)⁻¹ * ∑ i, samplerCouplingWork M D s s' (z i, w i)

/-- The law-level joint condition lifts to the actual finite empirical
cloud with exactly the same rate and normalisation. -/
theorem particleCouplingWork_le (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (ρ : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 0 ≤ t)
    (s s' : S) (z w : Fin N → Z) :
    particleCouplingWork M D N t s s' z w ≤
      -ρ * particleCouplingEnergy D N s s' z w := by
  have h := hmono t ht s s' (Model.empiricalLaw N z) (Model.empiricalLaw N w)
    (Model.empiricalLaw N (fun i => (z i, w i)))
    (empiricalPair_isCoupling N z w)
    (Model.empiricalLaw_probability N hN z) (Model.empiricalLaw_probability N hN w)
    (empiricalLaw_integrable N hN z _) (empiricalLaw_integrable N hN w _)
    (empiricalLaw_integrable N hN z _) (empiricalLaw_integrable N hN w _)
    (empiricalLaw_integrable N hN (fun i => (z i, w i)) _)
    (empiricalLaw_integrable N hN (fun i => (z i, w i)) _)
  simp only [integral_empiricalLaw, smul_eq_mul,
    Model.optimizerField, Model.meanGradient_empirical] at h
  exact h

/-- The only additional term when the reference optimiser uses the
population gradient is its actual empirical observation fluctuation. -/
theorem particle_population_work_decomposition (M : Model S Θ Z X I)
    (D : TwistedGeometry S Z) (N : ℕ) (t : ℝ) (s s' : S)
    (z w : Fin N → Z) (ν : Measure Z) :
    ⟪s - s', D.optimizerWeight
      (M.particleField N t s z - M.optimizerField t s' ν)⟫ +
      (N : ℝ)⁻¹ * ∑ i, samplerCouplingWork M D s s' (z i, w i) =
    particleCouplingWork M D N t s s' z w +
      ⟪s - s', D.optimizerWeight
        (M.particleField N t s' w - M.optimizerField t s' ν)⟫ := by
  unfold particleCouplingWork
  simp only [map_sub, inner_sub_right]
  ring

end PBGSO
