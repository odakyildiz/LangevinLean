import PBGSO.NumericsTarget
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Parameter-law identities from actual shared L² coordinates

The paired law is an actual pushforward of two random states on the same
probability space. Its parameter marginal is derived from pointwise L² lift
identities and composition of pushforwards. No law-compatibility conclusion
is a premise. Concrete momentum and HOL packings retain the shared optimiser
and all encoded particle coordinates.
-/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace PBGSO.ParameterLawTransfer

section Generic
variable {Ω E F A : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  (Q : Measure Ω) [IsFiniteMeasure Q]

/-- The actual joint law, retaining arbitrary dependence between the two
complete states. -/
def pairedLaw (U : Lp E 2 Q) (V : Lp F 2 Q) : Measure (E × F) :=
  Q.map (fun ω ↦ (U ω, V ω))

/-- The parameter marginal of the actual paired state equals the actual
pointwise L² parameter lift. This derives the desired compatibility identity.
-/
theorem liftMap_paired_law (f : E → A) {L : ℝ≥0} (hf : LipschitzWith L f)
    (U : Lp E 2 Q) (V : Lp F 2 Q) :
    Q.map (liftMap Q f hf U) = (pairedLaw Q U V).map (fun p ↦ f p.1) := by
  rw [Measure.map_congr (liftMap_coe Q f hf U)]
  exact (AEMeasurable.map_map_of_aemeasurable
    (hf.continuous.comp continuous_fst).measurable.aemeasurable
    ((Lp.aestronglyMeasurable U).aemeasurable.prodMk
      (Lp.aestronglyMeasurable V).aemeasurable)).symm

/-- A continuous-linear coordinate projection is an actual L² parameter
variable. The law equality is derived, not supplied. -/
theorem compLp_paired_law (f : E →L[ℝ] A)
    (U : Lp E 2 Q) (V : Lp F 2 Q) :
    Q.map (f.compLp U) = (pairedLaw Q U V).map (fun p ↦ f p.1) := by
  rw [Measure.map_congr (f.coeFn_compLp U)]
  exact (AEMeasurable.map_map_of_aemeasurable
    (f.continuous.comp continuous_fst).measurable.aemeasurable
    ((Lp.aestronglyMeasurable U).aemeasurable.prodMk
      (Lp.aestronglyMeasurable V).aemeasurable)).symm

end Generic

section Norm
variable {Ω E F A : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The L² parameter error and the particle-law RMS are the same genuine
quantity for the actual packing; the marginal identity is proved internally.
-/
theorem liftMap_target_norm_eq_paired_rms
    (f : E → A) {L : ℝ≥0} (hf : LipschitzWith L f)
    (U : Lp E 2 Q) (V : Lp F 2 Q) (a : A) :
    ‖liftMap Q f hf U - Lp.const 2 Q a‖ =
      Real.sqrt (∫ p, ‖f p.1 - a‖ ^ 2 ∂pairedLaw Q U V) := by
  exact lp_target_norm_eq_law_rms Q (liftMap Q f hf U) a
    (pairedLaw Q U V) (fun p ↦ f p.1)
    (hf.continuous.comp continuous_fst).measurable.aemeasurable
    (liftMap_paired_law Q f hf U V)

end Norm

section Particle
variable {Ω S A Z X I : Type*} {N : ℕ} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]
  (Q : Measure Ω) [IsFiniteMeasure Q]

/-- For the complete interacting/copy particle law, the actual parameter
lift has exactly the parameter marginal used by the source particle bound.
Neither an error estimate nor a marginal-law equality is assumed. -/
theorem particle_parameter_law (M : Model S A Z X I) {L : ℝ≥0}
    (hparam : LipschitzWith L M.parameter)
    (U V : Lp (S × (Fin N → Z)) 2 Q) :
    Q.map (liftMap Q (fun p : S × (Fin N → Z) ↦ M.parameter p.1)
      (hparam.comp (ContinuousLinearMap.fst ℝ S (Fin N → Z)).lipschitzWith) U) =
      (pairedLaw Q U V).map (fun p ↦ M.parameter p.1.1) :=
  liftMap_paired_law Q _ _ U V

/-- Projecting the actual shared optimiser first and then lifting the
model's parameter gives the identical particle-law marginal. This is the
coordinate representation used by actual particle integral realizations. -/
theorem optimizer_parameter_law (M : Model S A Z X I) {L : ℝ≥0}
    (hparam : LipschitzWith L M.parameter)
    (U V : Lp (S × (Fin N → Z)) 2 Q) :
    Q.map (liftMap Q M.parameter hparam
      ((ContinuousLinearMap.fst ℝ S (Fin N → Z)).compLp U)) =
      (pairedLaw Q U V).map (fun p ↦ M.parameter p.1.1) := by
  rw [Measure.map_congr (liftMap_coe Q M.parameter hparam
    ((ContinuousLinearMap.fst ℝ S (Fin N → Z)).compLp U))]
  have he : (fun ω ↦ M.parameter
      (((ContinuousLinearMap.fst ℝ S (Fin N → Z)).compLp U) ω)) =ᵐ[Q]
      fun ω ↦ M.parameter (U ω).1 := by
    filter_upwards [(ContinuousLinearMap.fst ℝ S (Fin N → Z)).coeFn_compLp U]
      with ω hω
    rw [hω]
    rfl
  rw [Measure.map_congr he]
  exact (AEMeasurable.map_map_of_aemeasurable
    (hparam.continuous.comp (continuous_fst.comp continuous_fst)).measurable.aemeasurable
    ((Lp.aestronglyMeasurable U).aemeasurable.prodMk
      (Lp.aestronglyMeasurable V).aemeasurable)).symm

end Particle

section ConcretePacking
open PBGSO.Methods
variable {Ω A X C : Type*} {N : ℕ} [MeasurableSpace Ω]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (Q : Measure Ω) (D : ParticleForceData A X C N)

/-- Repack the actual momentum/position phase into the paper's shared
optimiser (theta,m) and sampler array (x,v). -/
def momentumParticleState
    (z : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) (ω : Ω) :
    (A × A) × (Fin N → X × X) :=
  ((z.2.1 ω, z.1.1 ω), fun i ↦ (D.cloud (z.2.2 ω) i, D.cloud (z.1.2 ω) i))

theorem momentumParticleState_aemeasurable
    (z : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) :
    AEMeasurable (momentumParticleState Q D z) Q := by
  have ha := (Lp.aestronglyMeasurable z.2.1).aemeasurable
  have hm := (Lp.aestronglyMeasurable z.1.1).aemeasurable
  have hx := D.cloud.continuous.measurable.comp_aemeasurable
    (Lp.aestronglyMeasurable z.2.2).aemeasurable
  have hv := D.cloud.continuous.measurable.comp_aemeasurable
    (Lp.aestronglyMeasurable z.1.2).aemeasurable
  exact (ha.prodMk hm).prodMk (AEMeasurable.of_eval fun i ↦
    ((measurable_pi_apply i).comp_aemeasurable hx).prodMk
      ((measurable_pi_apply i).comp_aemeasurable hv))

/-- In the actual raw momentum packing, the interacting parameter marginal
is exactly the phase's optimiser-position coordinate. -/
theorem momentum_parameter_law
    (z r : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) :
    Q.map z.2.1 =
      (Q.map (fun ω ↦ (momentumParticleState Q D z ω,
        momentumParticleState Q D r ω))).map (fun p ↦ p.1.1.1) := by
  symm
  exact AEMeasurable.map_map_of_aemeasurable
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).aemeasurable
    ((momentumParticleState_aemeasurable Q D z).prodMk
      (momentumParticleState_aemeasurable Q D r))

/-- Repack the actual HOL variables into optimiser theta and sampler array
(x,u,v), using the same cloud encoding in every sampler coordinate. -/
def higherOrderParticleState (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) (ω : Ω) :
    A × (Fin N → X × X × X) :=
  (z.1 ω, fun i ↦ (D.cloud (z.2.1 ω) i, D.cloud (z.2.2.1 ω) i,
    D.cloud (z.2.2.2 ω) i))

theorem higherOrderParticleState_aemeasurable
    (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    AEMeasurable (higherOrderParticleState Q D z) Q := by
  have ha := (Lp.aestronglyMeasurable z.1).aemeasurable
  have hx := D.cloud.continuous.measurable.comp_aemeasurable
    (Lp.aestronglyMeasurable z.2.1).aemeasurable
  have hu := D.cloud.continuous.measurable.comp_aemeasurable
    (Lp.aestronglyMeasurable z.2.2.1).aemeasurable
  have hv := D.cloud.continuous.measurable.comp_aemeasurable
    (Lp.aestronglyMeasurable z.2.2.2).aemeasurable
  exact ha.prodMk (AEMeasurable.of_eval fun i ↦
    ((measurable_pi_apply i).comp_aemeasurable hx).prodMk
      (((measurable_pi_apply i).comp_aemeasurable hu).prodMk
        ((measurable_pi_apply i).comp_aemeasurable hv)))

/-- In the actual raw HOL packing, the parameter marginal is exactly the
first L² coordinate, without any law-compatibility premise. -/
theorem higherOrder_parameter_law
    (z r : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    Q.map z.1 =
      (Q.map (fun ω ↦ (higherOrderParticleState Q D z ω,
        higherOrderParticleState Q D r ω))).map (fun p ↦ p.1.1) := by
  symm
  exact AEMeasurable.map_map_of_aemeasurable (measurable_fst.comp measurable_fst).aemeasurable
    ((higherOrderParticleState_aemeasurable Q D z).prodMk
      (higherOrderParticleState_aemeasurable Q D r))

/-- The same actual momentum state in the Hilbert product coordinates
used by the general model, rather than the default max-norm product. -/
def momentumHilbertState
    (z : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) (ω : Ω) :
    WithLp 2 (A × A) × (Fin N → WithLp 2 (X × X)) :=
  (WithLp.toLp 2 (momentumParticleState Q D z ω).1,
    fun i ↦ WithLp.toLp 2 ((momentumParticleState Q D z ω).2 i))

theorem momentumHilbertState_aemeasurable
    (z : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) :
    AEMeasurable (momentumHilbertState Q D z) Q := by
  have h := momentumParticleState_aemeasurable Q D z
  exact ((WithLp.measurable_toLp 2 (A × A)).comp_aemeasurable h.fst).prodMk
    (AEMeasurable.of_eval fun i ↦ (WithLp.measurable_toLp 2 (X × X)).comp_aemeasurable
      ((measurable_pi_apply i).comp_aemeasurable h.snd))

/-- The full Hilbert momentum packing is genuinely square integrable. -/
theorem momentumHilbertState_memLp
    (z : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) :
    MemLp (momentumHilbertState Q D z) 2 Q := by
  apply memLp_prod_iff.mpr
  constructor
  · apply memLp_prodLp_iff.mpr
    exact ⟨Lp.memLp z.2.1, Lp.memLp z.1.1⟩
  · apply memLp_pi_iff.mpr
    intro i
    apply memLp_prodLp_iff.mpr
    exact ⟨((ContinuousLinearMap.proj i).comp D.cloud.toContinuousLinearMap).comp_memLp z.2.2,
      ((ContinuousLinearMap.proj i).comp D.cloud.toContinuousLinearMap).comp_memLp z.1.2⟩

/-- Actual L² interacting state in the Hilbert model coordinates. -/
def momentumHilbertLp
    (z : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) :
    Lp (WithLp 2 (A × A) × (Fin N → WithLp 2 (X × X))) 2 Q :=
  (momentumHilbertState_memLp Q D z).toLp (momentumHilbertState Q D z)

theorem momentumHilbertLp_coe
    (z : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) :
    momentumHilbertLp Q D z =ᵐ[Q] momentumHilbertState Q D z :=
  (momentumHilbertState_memLp Q D z).coeFn_toLp

/-- The exact raw optimiser-position law is retained by the actual Hilbert
model-state packing, including all shared optimiser momentum and particles. -/
theorem momentum_hilbert_parameter_law
    (z r : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) :
    Q.map z.2.1 =
      (Q.map (fun ω ↦ (momentumHilbertState Q D z ω,
        momentumHilbertState Q D r ω))).map (fun p ↦ p.1.1.fst) := by
  symm
  exact AEMeasurable.map_map_of_aemeasurable
    (((WithLp.measurable_ofLp 2 (A × A)).comp (measurable_fst.comp measurable_fst)).fst).aemeasurable
    ((momentumHilbertState_aemeasurable Q D z).prodMk
      (momentumHilbertState_aemeasurable Q D r))

/-- This is the exact compatibility identity for an actual paired L²
particle/reference momentum state; its proof contains no law premise. -/
theorem momentum_hilbert_lp_parameter_law
    (z r : ((Lp A 2 Q) × Lp C 2 Q) × ((Lp A 2 Q) × Lp C 2 Q)) :
    Q.map z.2.1 = (pairedLaw Q (momentumHilbertLp Q D z)
      (momentumHilbertLp Q D r)).map (fun p ↦ p.1.1.fst) := by
  rw [pairedLaw, Measure.map_congr
    ((momentumHilbertLp_coe Q D z).prodMk (momentumHilbertLp_coe Q D r))]
  exact momentum_hilbert_parameter_law Q D z r

/-- The HOL model's two nested Euclidean products keep the full (x,u,v)
sampler, while the optimiser has no auxiliary momentum. -/
def higherOrderHilbertState (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) (ω : Ω) :
    A × (Fin N → WithLp 2 (X × WithLp 2 (X × X))) :=
  (z.1 ω, fun i ↦ WithLp.toLp 2 (D.cloud (z.2.1 ω) i,
    WithLp.toLp 2 (D.cloud (z.2.2.1 ω) i, D.cloud (z.2.2.2 ω) i)))

theorem higherOrderHilbertState_aemeasurable
    (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    AEMeasurable (higherOrderHilbertState Q D z) Q := by
  have h := higherOrderParticleState_aemeasurable Q D z
  refine h.fst.prodMk (AEMeasurable.of_eval fun i ↦ ?_)
  have hi := (measurable_pi_apply i).comp_aemeasurable h.snd
  exact (WithLp.measurable_toLp 2 (X × WithLp 2 (X × X))).comp_aemeasurable
    (hi.fst.prodMk ((WithLp.measurable_toLp 2 (X × X)).comp_aemeasurable hi.snd))

/-- The full nested-Hilbert HOL state is genuinely square integrable. -/
theorem higherOrderHilbertState_memLp
    (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    MemLp (higherOrderHilbertState Q D z) 2 Q := by
  apply memLp_prod_iff.mpr
  constructor
  · exact Lp.memLp z.1
  · apply memLp_pi_iff.mpr
    intro i
    apply memLp_prodLp_iff.mpr
    refine ⟨((ContinuousLinearMap.proj i).comp D.cloud.toContinuousLinearMap).comp_memLp z.2.1, ?_⟩
    apply memLp_prodLp_iff.mpr
    exact ⟨((ContinuousLinearMap.proj i).comp D.cloud.toContinuousLinearMap).comp_memLp z.2.2.1,
      ((ContinuousLinearMap.proj i).comp D.cloud.toContinuousLinearMap).comp_memLp z.2.2.2⟩

/-- Actual complete L² HOL state on the shared probability space. -/
def higherOrderHilbertLp (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    Lp (A × (Fin N → WithLp 2 (X × WithLp 2 (X × X)))) 2 Q :=
  (higherOrderHilbertState_memLp Q D z).toLp (higherOrderHilbertState Q D z)

theorem higherOrderHilbertLp_coe
    (z : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    higherOrderHilbertLp Q D z =ᵐ[Q] higherOrderHilbertState Q D z :=
  (higherOrderHilbertState_memLp Q D z).coeFn_toLp

/-- The actual HOL Hilbert packing has exactly its optimiser L² marginal;
there is no final compatibility equality to assume. -/
theorem higherOrder_hilbert_parameter_law
    (z r : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    Q.map z.1 =
      (Q.map (fun ω ↦ (higherOrderHilbertState Q D z ω,
        higherOrderHilbertState Q D r ω))).map (fun p ↦ p.1.1) := by
  symm
  exact AEMeasurable.map_map_of_aemeasurable (measurable_fst.comp measurable_fst).aemeasurable
    ((higherOrderHilbertState_aemeasurable Q D z).prodMk
      (higherOrderHilbertState_aemeasurable Q D r))

/-- The actual paired L² HOL state has the exact parameter law required
by the numerical target assembly, without assuming compatibility. -/
theorem higherOrder_hilbert_lp_parameter_law
    (z r : HOLState (Lp A 2 Q) (Lp C 2 Q)) :
    Q.map z.1 = (pairedLaw Q (higherOrderHilbertLp Q D z)
      (higherOrderHilbertLp Q D r)).map (fun p ↦ p.1.1) := by
  rw [pairedLaw, Measure.map_congr
    ((higherOrderHilbertLp_coe Q D z).prodMk (higherOrderHilbertLp_coe Q D r))]
  exact higherOrder_hilbert_parameter_law Q D z r

end ConcretePacking
end PBGSO.ParameterLawTransfer
