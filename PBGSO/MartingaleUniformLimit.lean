import PBGSO.ClosedIntegralMartingale
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! # Continuous stochastic versions from summable maximal tails
This generic Borel-Cantelli foundation uses actual dense-observation maximal
probabilities and actual continuity of the approximating sample paths.
It assumes neither uniform convergence nor continuity of the limit.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace PBGSO.MartingaleUniformLimit
variable {Ω T H : Type*} [MeasurableSpace Ω] [TopologicalSpace T]
  [NormedAddCommGroup H] [CompleteSpace H]
  (Q : Measure Ω)

/-- The telescoping-series candidate is defined everywhere; its actual
convergence and continuity hold on the single full-measure event proved below. -/
def seriesLimit (f : ℕ → T → Ω → H) (t : T) (ω : Ω) : H :=
  (∑' n, (f (n + 1) t ω - f n t ω)) + f 0 t ω

/-- Summable maximal tail probabilities on a dense observation set imply
actual uniform convergence and continuous limit paths almost surely. -/
theorem ae_uniform_seriesLimit (f : ℕ → T → Ω → H) (S : Set T) (hS : Dense S)
    (δ : ℕ → ℝ) (hδ : Summable δ)
    (hbad : (∑' n, Q {ω | ∃ t ∈ S, δ n ≤ ‖f (n + 1) t ω - f n t ω‖}) ≠ ∞)
    (hc : ∀ᵐ ω ∂Q, ∀ n, Continuous (fun t => f n t ω)) :
    ∀ᵐ ω ∂Q, TendstoUniformly (fun n t => f n t ω) (fun t => seriesLimit f t ω) atTop ∧
      Continuous (fun t => seriesLimit f t ω) := by
  have hBC := ae_eventually_notMem hbad
  filter_upwards [hc, hBC] with ω hcont hevent
  have hb : ∀ᶠ n in atTop, ∀ t : T, ‖f (n + 1) t ω - f n t ω‖ ≤ δ n := by
    filter_upwards [hevent] with n hn
    intro t
    apply hS.induction (P := fun t => ‖f (n + 1) t ω - f n t ω‖ ≤ δ n) (x := t)
    · intro t ht
      exact le_of_lt (lt_of_not_ge (fun h => hn ⟨t, ht, h⟩))
    · exact isClosed_le ((hcont (n + 1)).sub (hcont n)).norm continuous_const
  have hs := tendstoUniformlyOn_tsum_nat_eventually hδ
    (s := Set.univ) (f := fun n t => f (n + 1) t ω - f n t ω)
    (hb.mono (fun _ hn t _ => hn t))
  have hs' : TendstoUniformly (fun N t => ∑ n ∈ Finset.range N, (f (n + 1) t ω - f n t ω))
      (fun t => ∑' n, (f (n + 1) t ω - f n t ω)) atTop := by
    simpa only [tendstoUniformlyOn_univ] using hs
  have h0 : TendstoUniformly (fun _ : ℕ => fun t => f 0 t ω) (fun t => f 0 t ω) atTop :=
    by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      exact Eventually.of_forall (fun _ _ => by simpa only [dist_self] using hε)
  have hu := hs'.add h0
  change TendstoUniformly (fun N t =>
    (∑ n ∈ Finset.range N, (f (n + 1) t ω - f n t ω)) + f 0 t ω)
    (fun t => (∑' n, (f (n + 1) t ω - f n t ω)) + f 0 t ω) atTop at hu
  have hsum (N : ℕ) (t : T) :
      (∑ n ∈ Finset.range N, (f (n + 1) t ω - f n t ω)) + f 0 t ω = f N t ω := by
    rw [Finset.sum_range_sub (fun n => f n t ω) N, sub_add_cancel]
  have hu' : TendstoUniformly (fun n t => f n t ω) (fun t => seriesLimit f t ω) atTop := by
    simpa only [Pi.add_apply, hsum, seriesLimit] using hu
  exact ⟨hu', hu'.continuous (Frequently.of_forall hcont)⟩

end PBGSO.MartingaleUniformLimit

namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (D : Driver (I := I) Q)

/-- For genuine continuous Brownian coordinate paths, every actual stopped
finite predictable sum has a simultaneous continuous sample path. -/
theorem stoppedGridSum_continuous_paths (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (A : Coefficients (Z := Z) Q D τ) (n : ℕ)
    (hB : ∀ᵐ ω ∂Q, ∀ i, Continuous (fun t => D.process i t ω)) :
    ∀ᵐ ω ∂Q, Continuous (fun t => stoppedGridSum Q D τ A n t ω) := by
  filter_upwards [hB] with ω hω
  have he : (fun t => stoppedGridSum Q D τ A n t ω) =
      fun t => ∑ i, BrownianGridIsometry.gridSum (D.process i) (fun k => min t (τ k))
        (fun k => (A k).value i) n ω := by
    funext t
    exact stoppedGridSum_columns_clamp Q D τ hτ A n t ω
  rw [he]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro k _
  exact (((hω i).comp (continuous_id.min continuous_const)).sub
    ((hω i).comp (continuous_id.min continuous_const))).smul continuous_const

end PBGSO.FilteredBrownian
