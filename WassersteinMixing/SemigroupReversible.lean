import WassersteinMixing.SemigroupApproximation
import WassersteinMixing.SemigroupAnchoredMALALaw
import WassersteinMixing.SemigroupPair
import WassersteinMixing.SemigroupMesh

/-! # Self-adjointness of the actual Gibbs Langevin transitions

The canonical MALA approximation has an explicitly reversible anchored law.
Its proved strong observable limit is the actual Brownian Langevin transition,
so self-adjointness passes to that transition without a reversibility premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter Set
open scoped Topology

namespace WassersteinMixing.RandomMALA.Canonical

theorem diffusion_zero_coe (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) :
    diffusion P V hV 0 =ᵐ[probability P V] fun ω ↦ actualInitial P V hV ω.1 := by
  have h := Lp.coeFn_compMeasurePreserving (actualInitial P V hV)
    (measurePreserving_fst (μ := actualProbability P V) (ν := uniformPath))
  rw [diffusion, CanonicalSemigroup.state_zero,
    ← actualInitial_eq_semigroupInitial P V hV]
  convert h using 1 <;> rfl

/-- The actual square-integrable initial/MALA pair inherits the proved
anchored detailed balance identity. -/
theorem mala_pair_swap (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    ((probability P V).map (fun ω ↦
      (diffusion P V hV 0 ω, mala P V hV r hr n ω))).map Prod.swap =
      (probability P V).map (fun ω ↦
        (diffusion P V hV 0 ω, mala P V hV r hr n ω)) := by
  have hpair : (probability P V).map (fun ω ↦
      (diffusion P V hV 0 ω, mala P V hV r hr n ω)) =
      (probability P V).map (fun ω ↦
        (actualInitial P V hV ω.1, (state P V hV r n ω).2)) := by
    apply Measure.map_congr
    filter_upwards [diffusion_zero_coe P V hV, mala_coe P V hV r hr n] with ω h0 hm
    exact Prod.ext h0 hm
  rw [hpair]
  exact anchored_state_swap P V hV r hr n

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Each concrete finite-step MALA compression is self-adjoint, as a proved
consequence of its actual reversible pair law. -/
theorem malaOp_isSelfAdjoint (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (r : ℝ) (hr : 0 < r) (n : ℕ) :
    IsSelfAdjoint (malaOp (𝕜 := 𝕜) (F := F) P V hV r hr n) := by
  exact StationaryObservables.compression_isSelfAdjoint_of_pair_swap (𝕜 := 𝕜)
    (ULA.gibbsMeasure V) (probability P V) (diffusion P V hV 0)
    (mala P V hV r hr n) (diffusion_law P V hV 0) (mala_law P V hV r hr n)
    (mala_pair_swap P V hV r hr n)

end WassersteinMixing.RandomMALA.Canonical

namespace WassersteinMixing.CanonicalSemigroup

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [CompleteSpace F] [NormedSpace ℝ F]

/-- Self-adjointness of the actual Langevin transition follows by strong
limits from the actual Gaussian/uniform Metropolis trajectories. -/
theorem op_isSelfAdjoint (P : Parameters) (V : E P.dimension → ℝ)
    (hV : PotentialAssumptions P V) (t : ℝ) (ht : 0 ≤ t) :
    IsSelfAdjoint (op (𝕜 := 𝕜) (F := F) P V hV t) := by
  let step : ℕ → ℝ := fun n ↦ 1 / ((n + 1 : ℕ) : ℝ)
  have hstep (n : ℕ) : 0 < step n := by dsimp [step]; positivity
  have hmesh : Tendsto step atTop (𝓝 0) := by
    simpa only [step, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let count := fun n ↦ meshCount (step n) t
  apply strongLimit_isSelfAdjoint (l := atTop)
    (fun n ↦ RandomMALA.Canonical.malaOp (𝕜 := 𝕜) (F := F) P V hV (step n) (hstep n) (count n))
    (op P V hV t)
  · intro n
    exact RandomMALA.Canonical.malaOp_isSelfAdjoint P V hV _ (hstep n) _
  · intro f
    exact RandomMALA.Canonical.malaOp_variable_tendsto P V hV step count hstep hmesh t ht
      (fun n ↦ meshCount_elapsed_le _ _ (hstep n) ht) t
      (meshCount_elapsed_tendsto step hstep hmesh t ht) f

end WassersteinMixing.CanonicalSemigroup
