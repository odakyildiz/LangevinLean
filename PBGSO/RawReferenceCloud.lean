import PBGSO.RawIndependentCopies
import PBGSO.ContinuousProcessRepresentative
import PBGSO.RawIntegralCLM
import Mathlib.Analysis.Normed.Lp.PiLp

/-! # Physical Hilbert encoding of the independent raw reference cloud
The full flattened diffusion is assembled from the actual pulled coordinate
columns. Its local gauge is the sum of the primitive one-copy gauges; no
expected coefficient moment or noise-law matching premise is introduced.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawReferenceCloud
open FilteredBrownian
variable {Ω I Z : Type*} [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q) (N : ℕ)

abbrev Cloud (N : ℕ) (Z : Type*) [NormedAddCommGroup Z] := PiLp 2 (fun _ : Fin N => Z)

def single (i : Fin N) : Z →L[ℝ] Cloud N Z :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => Z)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin N => Z) i)

@[simp] theorem single_apply (i k : Fin N) (z : Z) :
    single (Z := Z) N i z k = (Pi.single i z : Fin N → Z) k := rfl

@[simp] theorem single_norm (i : Fin N) (z : Z) : ‖single (Z := Z) N i z‖ = ‖z‖ := by
  change ‖PiLp.single (β := fun _ : Fin N => Z) 2 i z‖ = ‖z‖
  exact PiLp.norm_single 2 (fun _ : Fin N => Z) i z

variable {T : ℝ≥0} (L : RawLocalDiffusion (Z := Z) Q D T)

/-- The original row coefficient on its independent complete seed. -/
def row (i : Fin N) : RawLocalDiffusion (Z := Z)
    (IndependentCopies.seeds (J := Fin N) Q) (RawIndependentCopies.rowDriver Q D N i) T :=
  L.pullback (measurePreserving_eval (fun _ : Fin N => Q) i)
    (RawIndependentCopies.rowDriver Q D N i)
    (fun t => RawIndependentCopies.eval_filtration_le Q D N i t)

/-- Actual flattened physical columns: exactly one cloud coordinate receives
one original sampler noise column. -/
def sigma (ij : Fin N × I) (r : ℝ) (ω : Fin N → Ω) : Cloud N Z :=
  single (Z := Z) N ij.1 ((row Q D N L ij.1).sigma ij.2 r ω)

/-- One actual local energy controls all independently copied columns. -/
def q (r : ℝ) (ω : Fin N → Ω) : ℝ := ∑ i : Fin N, (row Q D N L i).q r ω

/-- Full locally square-integrable cloud diffusion, with constructed gauge. -/
def diffusion : RawLocalDiffusion (Z := Cloud N Z) (IndependentCopies.seeds (J := Fin N) Q)
    (RawIndependentCopies.driver Q D N) T where
  sigma := sigma Q D N L
  sigma_strong ij := (single (Z := Z) N ij.1).continuous.comp_stronglyMeasurable
    ((row Q D N L ij.1).sigma_strong ij.2)
  sigma_adapted t ij := (single (Z := Z) N ij.1).continuous.comp_aestronglyMeasurable
    ((row Q D N L ij.1).sigma_adapted t ij.2)
  q := q Q D N L
  q_strong := by
    change StronglyMeasurable (fun p : ℝ × (Fin N → Ω) => ∑ i : Fin N, (row Q D N L i).q p.1 p.2)
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    exact (row Q D N L i).q_strong
  q_nonneg r ω := Finset.sum_nonneg (fun i _ => (row Q D N L i).q_nonneg r ω)
  q_local ω := integrable_finset_sum _ (fun i _ => (row Q D N L i).q_local ω)
  q_progressive t := by
    have hs : StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod
        ((RawIndependentCopies.driver Q D N).filtration t)]
        (fun p : ℝ × (Fin N → Ω) => ∑ i : Fin N,
          (Ioc 0 (t : ℝ)).indicator (fun r => (row Q D N L i).q r p.2) p.1) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro i _
      exact (row Q D N L i).q_progressive t
    convert hs using 1
    funext p
    by_cases hp : p.1 ∈ Ioc 0 (t : ℝ)
    · simp [q,hp]
    · simp [q,hp]
  sigma_control r ω := by
    simp only [sigma,single_norm,Fintype.sum_prod_type,q]
    exact Finset.sum_le_sum (fun i _ => (row Q D N L i).sigma_control r ω)

@[simp] theorem diffusion_sigma (ij : Fin N × I) (r : ℝ) (ω : Fin N → Ω) :
    (diffusion Q D N L).sigma ij r ω = single (Z := Z) N ij.1 (L.sigma ij.2 r (ω ij.1)) := rfl

@[simp] theorem diffusion_q (r : ℝ) (ω : Fin N → Ω) :
    (diffusion Q D N L).q r ω = ∑ i : Fin N, L.q r (ω i) := rfl

/-- The coordinate projection of the flattened physical column is the
literal zero-padded row column. -/
theorem projected_sigma (i : Fin N) (ij : Fin N × I) (r : ℝ) (ω : Fin N → Ω) :
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => Z) i ((diffusion Q D N L).sigma ij r ω) =
      if ij.1 = i then L.sigma ij.2 r (ω i) else 0 := by
  classical
  by_cases h : ij.1 = i
  · subst i
    simp [diffusion_sigma,single_apply]
  · simp [diffusion_sigma,single_apply,Pi.single_apply,h,Ne.symm h]


section State
variable {S Θ X : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  {M : Model S Θ Z X I}
  (U : RawLocalStationarity.Data Q D M T)

/-- The literal reference cloud in its physical Hilbert coordinates. -/
def state (t : ℝ) (ω : Fin N → Ω) : Cloud N Z :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => Z)).symm
    (RawIndependentCopies.cloud Q D N U t ω)

@[simp] theorem state_apply (t : ℝ) (ω : Fin N → Ω) (i : Fin N) :
    state Q D N U t ω i = U.sampler.state t (ω i) := rfl

theorem state_measurable (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : Measurable (state Q D N U t) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => Z)).symm.continuous.measurable.comp
    (RawIndependentCopies.cloud_measurable Q D N U t ht)

/-- Exact physical columns against the actual constructed independent state. -/
theorem physical_columns :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ t ∈ Icc 0 (T : ℝ), ∀ ij : Fin N × I,
      (diffusion Q D N U.sampler.localDiffusion).sigma ij t ω =
        single (Z := Z) N ij.1
          (M.diffusion (M.parameter (U.optimizer t)) (state Q D N U t ω ij.1) ij.2) := by
  filter_upwards [RawIndependentCopies.physical_columns Q D N U] with ω hω t ht ij
  change single (Z := Z) N ij.1
      ((RawIndependentCopies.copy Q D N U ij.1).sampler.localDiffusion.sigma ij.2 t ω) = _
  rw [hω ij.1 t ht ij.2]
  rfl

/-- Original finite second moments are inherited by the entire finite cloud. -/
theorem state_square (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    MemLp (state Q D N U t) 2 (IndependentCopies.seeds (J := Fin N) Q) := by
  have hU : MemLp (U.sampler.state t) 2 Q := by
    apply (memLp_two_iff_integrable_sq_norm (U.sampler.measurable t ht).stronglyMeasurable.aestronglyMeasurable).mpr
    exact (integrable_map_measure (by fun_prop) (U.sampler.measurable t ht).aemeasurable).mp
      (U.second_moment t ht)
  have hi (i : Fin N) : Integrable (fun ω : Fin N → Ω => ‖U.sampler.state t (ω i)‖ ^ 2)
      (IndependentCopies.seeds (J := Fin N) Q) :=
    ((hU.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => Q) i)).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0))
  apply (memLp_two_iff_integrable_sq_norm (state_measurable Q D N U t ht).stronglyMeasurable.aestronglyMeasurable).mpr
  have hh := integrable_finsetSum Finset.univ (fun i _ => hi i)
  simpa only [PiLp.norm_sq_eq_of_L2,state_apply] using hh

/-- The whole original cloud has almost surely continuous physical paths. -/
theorem state_continuous_paths :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      ContinuousOn (fun t => state Q D N U t ω) (Icc 0 (T : ℝ)) := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin N =>
    (RawIndependentCopies.copy Q D N U i).sampler.continuous_paths)] with ω hω
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => Z)).symm.continuous.comp_continuousOn
  exact continuousOn_pi.mpr hω

/-- Joint strong measurability is derived from the original fixed-time
measurability and one common almost-sure continuous-path event. -/
theorem exists_regular_state :
    ∃ g : Icc 0 (T : ℝ) → (Fin N → Ω) → Cloud N Z,
      StronglyMeasurable (Function.uncurry g) ∧
      (∀ ω, Continuous (fun t => g t ω)) ∧
      ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ t,
        g t ω = state Q D N U t ω := by
  apply ContinuousProcessRepresentative.exists_joint_of_measurable
    (IndependentCopies.seeds (J := Fin N) Q) (fun (t : Icc 0 (T : ℝ)) ω => state Q D N U t ω)
    (fun t => state_measurable Q D N U t t.property)
  exact (state_continuous_paths Q D N U).mono (fun _ hc => hc.restrict)

end State

end PBGSO.RawReferenceCloud
