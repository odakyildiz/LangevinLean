import PBGSO.RawReferenceCloud
import PBGSO.RawLocalLinearMap
import PBGSO.RawLocalNoiseEmbedding

/-! # The original independent cloud equation with actual physical noise
Coordinatewise original strong equations are assembled in Hilbert coordinates.
Ordinary Bochner integrability is derived pathwise, without expected drift
moments or an assumed cloud integral equation.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.RawReferenceCloud
open FilteredBrownian
variable {Ω I Z S Θ X : Type*} [MeasurableSpace Ω]
  [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q) (N : ℕ)
  {T : ℝ≥0} {M : Model S Θ Z X I}
  (U : RawLocalStationarity.Data Q D M T)

/-- The original row's Brownian columns are its literal flattened indices. -/
def rowEmbedding (i : Fin N) : I ↪ Fin N × I :=
  ⟨fun j => (i,j),fun _ _ h => (Prod.mk.inj h).2⟩

/-- Projection of the actual full cloud stochastic integral is the actual
original row stochastic integral, on one event for every horizon time. -/
theorem coordinate_noise :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      ∀ i : Fin N, ∀ t : ℝ≥0, t ≤ T →
        (diffusion Q D N U.sampler.localDiffusion).localNoise t ω i =
          (RawIndependentCopies.copy Q D N U i).sampler.localDiffusion.localNoise t ω := by
  classical
  let C := diffusion Q D N U.sampler.localDiffusion
  have hi (i : Fin N) : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      ∀ t : ℝ≥0, t ≤ T → C.localNoise t ω i =
        (row Q D N U.sampler.localDiffusion i).localNoise t ω := by
    let A := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => Z) i
    let K := C.linearMap A
    have he : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
        ∀ ij r, r ∈ Ioc 0 (T : ℝ) →
          K.sigma ij r ω = rawEmbed (rowEmbedding (I := I) N i)
            (row Q D N U.sampler.localDiffusion i).sigma ij r ω := by
      apply Eventually.of_forall
      intro ω ij r hr
      change A (C.sigma ij r ω) = _
      rw [show A (C.sigma ij r ω) =
        if ij.1 = i then U.sampler.localDiffusion.sigma ij.2 r (ω i) else 0 from
          projected_sigma Q D N U.sampler.localDiffusion i ij r ω]
      by_cases hij : ij.1 = i
      · subst i
        rw [if_pos rfl]
        exact (embedFamily_image (rowEmbedding (I := I) N ij.1)
          (fun j => (row Q D N U.sampler.localDiffusion ij.1).sigma j r ω) ij.2).symm
      · rw [if_neg hij]
        symm
        apply embedFamily_outside
        rintro ⟨j,hj⟩
        exact hij (congrArg Prod.fst hj).symm
    have hk := (row Q D N U.sampler.localDiffusion i).localNoise_noiseEmbedding_congr
      (rowEmbedding (I := I) N i) (RawIndependentCopies.driver Q D N) rfl (fun _ _ => rfl) K he
    filter_upwards [hk,C.linearMap_localNoise_on_horizon A] with ω hk hl t ht
    exact (hl t ht).symm.trans (hk t ht)
  filter_upwards [ae_all_iff.mpr hi] with ω hi i t ht
  exact hi i t ht

/-- The literal independent coordinate drifts in physical Hilbert coordinates. -/
def drift (r : ℝ) (ω : Fin N → Ω) : Cloud N Z :=
  ∑ i : Fin N, single (Z := Z) N i
    (M.drift (M.parameter (U.optimizer r)) (state Q D N U r ω i))

@[simp] theorem drift_apply (r : ℝ) (ω : Fin N → Ω) (i : Fin N) :
    drift Q D N U r ω i = M.drift (M.parameter (U.optimizer r)) (state Q D N U r ω i) := by
  classical
  simp [drift,single_apply,Pi.single_apply]

/-- Finite cloud drift remains pathwise Bochner L¹ even if no expected
sampler-drift moment exists. -/
theorem drift_integrable :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      IntervalIntegrable (fun r => drift Q D N U r ω) volume 0 (T : ℝ) := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin N =>
    (RawIndependentCopies.copy Q D N U i).sampler.drift_integrable)] with ω hω
  unfold drift
  rw [intervalIntegrable_iff]
  apply integrable_finsetSum
  intro i _
  apply (single (Z := Z) N i).integrable_comp
  simpa only [RawIndependentCopies.copy_optimizer, state_apply,
    RawIndependentCopies.copy_state, RawIndependentCopies.cloud, IntegrableOn] using
    (intervalIntegrable_iff.mp (hω i))

/-- Coordinate identities assemble the whole original raw equation. This
supporting deterministic lemma is instantiated below with proved computed
noise projection identities, rather than assumed output-noise matching. -/
theorem equation_of_coordinate_noise
    (hnoise : ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q,
      ∀ i : Fin N, ∀ t : ℝ≥0, t ≤ T →
        (diffusion Q D N U.sampler.localDiffusion).localNoise t ω i =
          (RawIndependentCopies.copy Q D N U i).sampler.localDiffusion.localNoise t ω) :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ t ∈ Icc 0 (T : ℝ),
      state Q D N U t ω = state Q D N U 0 ω +
        (∫ r in 0..t, drift Q D N U r ω) +
          (diffusion Q D N U.sampler.localDiffusion).localNoise t.toNNReal ω := by
  filter_upwards [drift_integrable Q D N U,RawIndependentCopies.coordinate_equations Q D N U,
    hnoise] with ω hi he hn t ht
  have hit : IntervalIntegrable (fun r => drift Q D N U r ω) volume 0 t := by
    apply hi.mono_set
    simpa only [uIcc_of_le ht.1,uIcc_of_le T.coe_nonneg] using
      (Icc_subset_Icc le_rfl ht.2 : Icc 0 t ⊆ Icc 0 (T : ℝ))
  apply PiLp.ext
  intro i
  have hproj := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => Z) i).intervalIntegral_comp_comm hit
  have htt : t.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe).mpr ht.2
  change state Q D N U t ω i = state Q D N U 0 ω i +
    (∫ r in 0..t, drift Q D N U r ω) i +
      (diffusion Q D N U.sampler.localDiffusion).localNoise t.toNNReal ω i
  change (∫ r in 0..t, drift Q D N U r ω i) =
    (∫ r in 0..t, drift Q D N U r ω) i at hproj
  rw [hn i t.toNNReal htt,← hproj]
  simpa only [state_apply,PiLp.proj_apply,drift_apply,RawIndependentCopies.cloud] using he i t ht

/-- The actual physical cloud has the derived iid reference marginal.
This is the independent reference cloud, rather than the interacting cloud. -/
theorem state_coordinate_law (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    (IndependentCopies.seeds (J := Fin N) Q).map (fun ω i => state Q D N U t ω i) =
      Measure.pi (fun _ : Fin N => Q.map (U.sampler.state t)) :=
  RawIndependentCopies.cloud_law Q D N U t ht

/-- The literal independently seeded cloud solves its original full raw SDE
with the constructed flattened physical Brownian coefficients. No coefficient,
noise-output, integral-equation, or iid-law matching premise is supplied. -/
theorem equation :
    ∀ᵐ ω ∂IndependentCopies.seeds (J := Fin N) Q, ∀ t ∈ Icc 0 (T : ℝ),
      state Q D N U t ω = state Q D N U 0 ω +
        (∫ r in 0..t, drift Q D N U r ω) +
          (diffusion Q D N U.sampler.localDiffusion).localNoise t.toNNReal ω :=
  equation_of_coordinate_noise Q D N U (coordinate_noise Q D N U)

end PBGSO.RawReferenceCloud
