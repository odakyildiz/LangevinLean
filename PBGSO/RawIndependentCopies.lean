import PBGSO.RawLocalSolutionTransport
import PBGSO.IndependentCopies
import PBGSO.BrownianVectorFiltration
import Mathlib.Probability.Independence.InfinitePi

/-! # Independent original raw reference trajectories
Independent complete source seeds carry a genuine full vector Brownian driver.
Every coordinate copy solves the original local strong equation in that full
past filtration, and its actual whole-trajectory and cloud laws are derived.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawIndependentCopies
open FilteredBrownian
variable {Ω I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q) (N : ℕ)

/-- Every independent seed contributes its entire original filtration. -/
def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Fin N → Ω)) where
  seq t := @MeasurableSpace.pi (Fin N) (fun _ => Ω) (fun _ => D.filtration t)
  mono' s t h := by
    change (⨆ i : Fin N, (D.filtration s).comap (fun ω : Fin N → Ω => ω i)) ≤
      ⨆ i : Fin N, (D.filtration t).comap (fun ω : Fin N → Ω => ω i)
    exact iSup_mono (fun _ => MeasurableSpace.comap_mono (D.filtration.mono h))
  le' t := by
    change (⨆ i : Fin N, (D.filtration t).comap (fun ω : Fin N → Ω => ω i)) ≤
      ⨆ i : Fin N, mΩ.comap (fun ω : Fin N → Ω => ω i)
    exact iSup_mono (fun _ => MeasurableSpace.comap_mono (D.filtration.le t))

/-- A seed coordinate reveals only original current-past information. -/
theorem eval_filtration_le (i : Fin N) (t : ℝ≥0) :
    (D.filtration t).comap (fun ω : Fin N → Ω => ω i) ≤ filtration Q D N t := by
  exact le_iSup (fun j : Fin N => (D.filtration t).comap (fun ω : Fin N → Ω => ω j)) i

def process (ij : Fin N × I) (t : ℝ≥0) (ω : Fin N → Ω) : ℝ := D.process ij.2 t (ω ij.1)

theorem adapted (ij : Fin N × I) : StronglyAdapted (filtration Q D N) (process Q D N ij) := by
  intro t
  exact (D.adapted ij.2 t).comp_measurable (measurable_iff_comap_le.mpr (eval_filtration_le Q D N ij.1 t))

theorem increment_independent (s t : ℝ≥0) (hst : s ≤ t) :
    iIndepFun (fun ij (ω : Fin N → Ω) => process Q D N ij t ω-process Q D N ij s ω)
      (IndependentCopies.seeds (J := Fin N) Q) := by
  change iIndepFun (fun (ij : Fin N × I) (ω : Fin N → Ω) => D.process ij.2 t (ω ij.1)-D.process ij.2 s (ω ij.1)) _
  apply iIndepFun_uncurry' (X := fun (i : Fin N) (j : I) (ω : Fin N → Ω) =>
    D.process j t (ω i)-D.process j s (ω i))
  · intro i j
    exact ((increment_measurable Q D s t j).comp (measurable_pi_apply i))
  · exact iIndepFun_pi (fun _ : Fin N =>
      (measurable_pi_iff.mpr fun j => increment_measurable Q D s t j).aemeasurable)
  · intro i
    exact (pullbackDriver (measurePreserving_eval (fun _ : Fin N => Q) i) D).increment_coordinates s t hst

/-- A type synonym lets the past sigma-algebra be a genuine codomain
without replacing the original source's ambient measurable structure. -/
def PastSpace (D : Driver (I := I) Q) (s : ℝ≥0) := Ω

instance pastSpaceMeasurable (s : ℝ≥0) : MeasurableSpace (PastSpace Q D s) := D.filtration s

/-- Entire future increment vectors are independent of the complete product
past, including every original seed's initial information. -/
theorem future_independent (s t : ℝ≥0) (hst : s ≤ t) :
    Indep (MeasurableSpace.comap
      (fun (ω : Fin N → Ω) ij => process Q D N ij t ω-process Q D N ij s ω) inferInstance)
      (filtration Q D N s) (IndependentCopies.seeds (J := Fin N) Q) := by
  let X : Fin N → (Fin N → Ω) → (I → ℝ) :=
    fun i ω j => D.process j t (ω i)-D.process j s (ω i)
  let Y : Fin N → (Fin N → Ω) → PastSpace Q D s := fun i ω => ω i
  have hX (i : Fin N) : Measurable (X i) := measurable_pi_iff.mpr fun j =>
    (increment_measurable Q D s t j).comp (measurable_pi_apply i)
  have hY (i : Fin N) : Measurable (Y i) := by
    exact (measurable_pi_apply i).mono le_rfl (D.filtration.le s)
  have hpair : iIndepFun (fun i ω => (X i ω,Y i ω))
      (IndependentCopies.seeds (J := Fin N) Q) := by
    exact iIndepFun_pi (X := fun (_ : Fin N) (ω : Ω) =>
      ((fun j : I => D.process j t ω-D.process j s ω),(show PastSpace Q D s from ω)))
      (fun _ => ((measurable_pi_iff.mpr fun j => increment_measurable Q D s t j).prodMk
        (show @Measurable Ω (PastSpace Q D s) mΩ (D.filtration s) id from
          measurable_iff_comap_le.mpr (by simpa using D.filtration.le s))).aemeasurable)
  have hxy (i : Fin N) : IndepFun (X i) (Y i) (IndependentCopies.seeds (J := Fin N) Q) := by
    have hi := (pullbackDriver (measurePreserving_eval (fun _ : Fin N => Q) i) D).future_independent s t hst
    change Indep (MeasurableSpace.comap
      (fun ω j => D.process j t (ω i)-D.process j s (ω i)) inferInstance)
      ((D.filtration s).comap (fun ω : Fin N → Ω => ω i))
      (IndependentCopies.seeds (J := Fin N) Q)
    exact hi
  have hv := independent_pair_vectors (IndependentCopies.seeds (J := Fin N) Q)
    X Y (fun i => (hX i).aemeasurable) (fun i => (hY i).aemeasurable) hpair hxy
  have hv' : Indep (MeasurableSpace.comap (fun ω i => X i ω) inferInstance)
      (filtration Q D N s) (IndependentCopies.seeds (J := Fin N) Q) := by
    have hYid : (fun (ω : Fin N → Ω) i => Y i ω) = id := rfl
    rw [hYid] at hv
    simpa only [IndepFun,Kernel.IndepFun,Indep,MeasurableSpace.comap_id,
      filtration,pastSpaceMeasurable] using hv
  have hflat : Measurable (fun h : Fin N → I → ℝ => fun ij : Fin N × I => h ij.1 ij.2) :=
    measurable_pi_iff.mpr fun ij => (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1)
  apply indep_of_indep_of_le_left hv'
  have hh := MeasurableSpace.comap_mono (g := fun ω i => X i ω) hflat.comap_le
  simpa only [MeasurableSpace.comap_comp,Function.comp_def,X,process] using hh

/-- The complete independent reference Brownian driver. -/
def driver : Driver (I := Fin N × I) (IndependentCopies.seeds (J := Fin N) Q) where
  process := process Q D N
  brownian ij := ⟨fun J => (D.brownian ij.2).hasLaw J |>.comp
    (measurePreserving_eval (fun _ : Fin N => Q) ij.1).hasLaw⟩
  filtration := filtration Q D N
  adapted := adapted Q D N
  increment_coordinates := increment_independent Q D N
  future_independent := future_independent Q D N

/-- One row of the complete vector, retaining the complete product past. -/
def rowDriver (i : Fin N) : Driver (I := I) (IndependentCopies.seeds (J := Fin N) Q) where
  process j := (driver Q D N).process (i,j)
  brownian j := (driver Q D N).brownian (i,j)
  filtration := (driver Q D N).filtration
  adapted j := (driver Q D N).adapted (i,j)
  increment_coordinates s t hst := ((driver Q D N).increment_coordinates s t hst).precomp
    (g := fun j => (i,j)) (fun _ _ h => (Prod.mk.inj h).2)
  future_independent s t hst := by
    apply indep_of_indep_of_le_left ((driver Q D N).future_independent s t hst)
    have hm : Measurable (fun x : Fin N × I → ℝ => fun j => x (i,j)) :=
      measurable_pi_iff.mpr fun j => measurable_pi_apply (i,j)
    have hh := MeasurableSpace.comap_mono
      (g := fun ω ij => (driver Q D N).process ij t ω-(driver Q D N).process ij s ω) hm.comap_le
    simpa only [MeasurableSpace.comap_comp,Function.comp_def] using hh


section Copies
section SeparableSeeds
variable [MeasurableSpace.CountablyGenerated Ω]

/-- Finite products retain countably generated measurable structure. -/
theorem fin_countablyGenerated (n : ℕ) : MeasurableSpace.CountablyGenerated (Fin n → Ω) := by
  induction n with
  | zero =>
      refine ⟨⟨∅, Set.countable_empty, ?_⟩⟩
      simp [MeasurableSpace.pi]
  | succ n hn =>
      letI := hn
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Ω) 0
      have h := MeasurableSpace.CountablyGenerated.comap (e : (Fin (n+1) → Ω) → _)
      rwa [e.measurableEmbedding.comap_eq] at h

local instance pi_separable : IsSeparable (Measure.pi (fun _ : Fin N => Q)) := by
  letI := fin_countablyGenerated (Ω := Ω) N
  infer_instance

local instance seeds_separable : IsSeparable (IndependentCopies.seeds (J := Fin N) Q) := pi_separable Q N

/-- Product-measure separability follows from the actual countably generated
seed space, with no additional moment hypothesis. -/
theorem seeds_isSeparable : IsSeparable (IndependentCopies.seeds (J := Fin N) Q) :=
  seeds_separable Q N

end SeparableSeeds

variable
  {S Θ Z X : Type*}
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {M : Model S Θ Z X I} {T : ℝ≥0}
  (U : RawLocalStationarity.Data Q D M T)

/-- The actual original one-copy equation on seed i, in the complete
product filtration and with computed pulled-back local Brownian noise. -/
def copy (i : Fin N) : RawLocalStationarity.Data
    (IndependentCopies.seeds (J := Fin N) Q) (rowDriver Q D N i) M T :=
  U.pullback (measurePreserving_eval (fun _ : Fin N => Q) i) (rowDriver Q D N i)
    (fun t => eval_filtration_le Q D N i t) (fun _ _ => Eventually.of_forall (fun _ => rfl))

@[simp] theorem copy_optimizer (i : Fin N) : (copy Q D N U i).optimizer = U.optimizer := rfl

@[simp] theorem copy_state (i : Fin N) (t : ℝ) (ω : Fin N → Ω) :
    (copy Q D N U i).sampler.state t ω = U.sampler.state t (ω i) := rfl

/-- Literal independent-reference cloud. -/
def cloud (t : ℝ) (ω : Fin N → Ω) : Fin N → Z := fun i => U.sampler.state t (ω i)

theorem cloud_measurable (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : Measurable (cloud Q D N U t) :=
  IndependentCopies.cloud_measurable _ (U.sampler.measurable t ht)

/-- Exact iid law of the original copies is derived from the complete
seed product. No property of an interacting cloud is assumed here. -/
theorem cloud_law (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    (IndependentCopies.seeds (J := Fin N) Q).map (cloud Q D N U t) =
      Measure.pi (fun _ : Fin N => Q.map (U.sampler.state t)) :=
  IndependentCopies.cloud_law Q _ (U.sampler.measurable t ht)

/-- Independence holds for the whole finite-horizon trajectories. -/
theorem trajectories_independent :
    iIndepFun (fun i (ω : Fin N → Ω) (t : Icc 0 (T : ℝ)) => U.sampler.state t (ω i))
      (IndependentCopies.seeds (J := Fin N) Q) := by
  exact iIndepFun_pi (fun _ : Fin N =>
    (measurable_pi_iff.mpr (fun t : Icc 0 (T : ℝ) => U.sampler.measurable t t.property)).aemeasurable)

/-- Each coordinate's actual law is the original reference marginal. -/
theorem copy_law (i : Fin N) (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    (IndependentCopies.seeds (J := Fin N) Q).map ((copy Q D N U i).sampler.state t) =
      Q.map (U.sampler.state t) :=
  U.sampler.pullback_law (measurePreserving_eval (fun _ : Fin N => Q) i)
    (rowDriver Q D N i) (fun t => eval_filtration_le Q D N i t)
    (fun _ _ => Eventually.of_forall (fun _ => rfl)) t ht

/-- Every copy uses the original physical model columns, on one common
full-measure event for all particles, noise indices and horizon times. -/
theorem physical_columns :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ i : Fin N, ∀ t ∈ Icc 0 (T : ℝ), ∀ j : I,
      (copy Q D N U i).sampler.localDiffusion.sigma j t ω =
        M.diffusion (M.parameter (U.optimizer t)) (cloud Q D N U t ω i) j := by
  exact ae_all_iff.mpr (fun i => (copy Q D N U i).sampler.diffusion_realizes)

/-- The original raw coordinate SDEs hold simultaneously. The stochastic
inputs are constructed row integrals, not free processes with assumed laws. -/
theorem coordinate_equations :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ i : Fin N, ∀ t ∈ Icc 0 (T : ℝ),
      cloud Q D N U t ω i = cloud Q D N U 0 ω i +
        (∫ r in 0..t, M.drift (M.parameter (U.optimizer r)) (cloud Q D N U r ω i)) +
          (copy Q D N U i).sampler.localDiffusion.localNoise t.toNNReal ω := by
  exact ae_all_iff.mpr (fun i => (copy Q D N U i).sampler.equation)

/-- Current-time reference coordinates are adapted to the full product past. -/
theorem cloud_adapted (t : ℝ≥0) :
    AEStronglyMeasurable[(driver Q D N).filtration t] (cloud Q D N U t)
      (IndependentCopies.seeds (J := Fin N) Q) := by
  let f : (Fin N → Ω) → Fin N → Z := fun ω i =>
    ((copy Q D N U i).sampler.adapted t).mk ((copy Q D N U i).sampler.state t) ω
  have hh (i : Fin N) : StronglyMeasurable[(driver Q D N).filtration t] (fun ω => f ω i) :=
    ((copy Q D N U i).sampler.adapted t).stronglyMeasurable_mk
  have hf : StronglyMeasurable[(driver Q D N).filtration t] f := by
    letI : MeasurableSpace (Fin N → Ω) := (driver Q D N).filtration t
    exact (measurable_pi_iff.mpr (fun i => (hh i).measurable)).stronglyMeasurable
  refine ⟨f,hf,?_⟩
  filter_upwards [ae_all_iff.mpr (fun i => ((copy Q D N U i).sampler.adapted t).ae_eq_mk)] with ω hω
  exact funext hω

end Copies

end PBGSO.RawIndependentCopies
