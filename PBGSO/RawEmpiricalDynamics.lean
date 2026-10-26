import PBGSO.RawParticleInteraction
import PBGSO.RawNaturalSampler

/-! # Original empirical dynamics in physical Hilbert coordinates
The empirical optimizer sees the literal finite observation average. A noise
column acts only on its sampler coordinate and never on the optimizer.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawEmpiricalDynamics
open FilteredBrownian ConstructedItoParticle
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [Fintype I] [DecidableEq I]
  (M : Model S Θ Z X I) (N : ℕ)

/-- Literal original empirical drift, before reference-copy coupling. -/
def drift (t : ℝ) (y : OneHilbert N S Z) : OneHilbert N S Z :=
  (oneEquiv N).symm
    (M.particleField N t (oneEquiv N y).1 (oneEquiv N y).2,
      fun i => M.drift (M.parameter (oneEquiv N y).1) ((oneEquiv N y).2 i))

/-- Literal physical original empirical diffusion. -/
def sigma (ij : Fin N × I) (y : OneHilbert N S Z) : OneHilbert N S Z :=
  (oneEquiv N).symm (0, fun k => if k = ij.1 then
    M.diffusion (M.parameter (oneEquiv N y).1) ((oneEquiv N y).2 k) ij.2 else 0)

@[simp] theorem drift_coordinates (t : ℝ) (y : OneHilbert N S Z) :
    oneEquiv N (drift M N t y) =
      (M.particleField N t (oneEquiv N y).1 (oneEquiv N y).2,
        fun i => M.drift (M.parameter (oneEquiv N y).1) ((oneEquiv N y).2 i)) :=
  (oneEquiv N).apply_symm_apply _

@[simp] theorem sigma_coordinates (ij : Fin N × I) (y : OneHilbert N S Z) :
    oneEquiv N (sigma M N ij y) =
      (0,fun k => if k = ij.1 then
        M.diffusion (M.parameter (oneEquiv N y).1) ((oneEquiv N y).2 k) ij.2 else 0) :=
  (oneEquiv N).apply_symm_apply _

/-- The original time-dependent empirical SDE, encoded as a natural sampler
with literal deterministic time parameter. Its auxiliary observation/optimizer
are unused. No reference cloud or paired coefficient occurs in this model. -/
def timeModel : Model ℝ ℝ (OneHilbert N S Z) (OneHilbert N S Z) (Fin N × I) where
  parameter := id
  position := id
  observation _ _ := 0
  optimizer _ _ _ := 0
  drift := drift M N
  diffusion _ y ij := sigma M N ij y

end PBGSO.RawEmpiricalDynamics

namespace PBGSO.RawEmpiricalDynamics
open FilteredBrownian ConstructedItoParticle
variable {S Θ Z X I Ω : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [MeasurableSpace Θ] [BorelSpace Θ] [SecondCountableTopology Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [Fintype I] [DecidableEq I]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  (M : Model S Θ Z X I) (N : ℕ)
  {D : Driver (I := Fin N × I) Q} {T : ℝ≥0}

/-- An actual original empirical strong solution. This input asserts original
physical raw equations, rather than existence from the mean-field A1. There
are no reference-copy, iid, energy or global drift-moment assumptions. -/
structure Solution (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : Driver (I := Fin N × I) Q) (T : ℝ≥0) extends
    RawLocalStationarity.SamplerData Q D (timeModel M N) T id where
  initial_square : MemLp (state 0) 2 Q

/-- Primitive Borel fields imply measurability of the literal full empirical
drift, including its actual finite observation average and shared optimizer. -/
theorem drift_measurable
    (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hb : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hΨ : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2)) :
    Measurable (fun p : ℝ × OneHilbert N S Z => drift M N p.1 p.2) := by
  have hs : Measurable (fun p : ℝ × OneHilbert N S Z => (oneEquiv N p.2).1) :=
    ((oneEquiv N).continuous.measurable.comp measurable_snd).fst
  have hz (i : Fin N) : Measurable (fun p : ℝ × OneHilbert N S Z => (oneEquiv N p.2).2 i) :=
    (measurable_pi_apply i).comp (((oneEquiv N).continuous.measurable.comp measurable_snd).snd)
  have hg : Measurable (fun p : ℝ × OneHilbert N S Z =>
      M.particleGradient N (oneEquiv N p.2).1 (oneEquiv N p.2).2) := by
    exact (Finset.measurable_fun_sum Finset.univ (fun i _ => hF.comp (hs.prodMk (hz i)))).const_smul _
  have ho : Measurable (fun p : ℝ × OneHilbert N S Z =>
      M.particleField N p.1 (oneEquiv N p.2).1 (oneEquiv N p.2).2) :=
    hΨ.comp (measurable_fst.prodMk (hs.prodMk hg))
  have hc : Measurable (fun p : ℝ × OneHilbert N S Z =>
      fun i => M.drift (M.parameter (oneEquiv N p.2).1) ((oneEquiv N p.2).2 i)) := by
    apply measurable_pi_lambda
    intro i
    exact hb.comp (hs.prodMk (hz i))
  exact (oneEquiv N).symm.continuous.measurable.comp (ho.prodMk hc)

/-- The original empirical solution produces controlled raw data from its
own original local equation and primitive fields. No final paired dynamics
or iid law is used. -/
def build (U : Solution M N Q D T)
    (hF : Measurable (fun p : S × Z => M.observation (M.parameter p.1) (M.position p.2)))
    (hb : Measurable (fun p : S × Z => M.drift (M.parameter p.1) p.2))
    (hΨ : Measurable (fun p : ℝ × (S × Θ) => M.optimizer p.1 p.2.1 p.2.2)) :
    RawNaturalSampler.Realization U.toSamplerData :=
  RawNaturalSampler.build U.toSamplerData continuous_id.continuousOn U.initial_square
    (drift_measurable M N hF hb hΨ)

end PBGSO.RawEmpiricalDynamics
