import WassersteinMixing.SemigroupMALA
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

set_option linter.style.header false
set_option maxHeartbeats 800000

/-! # Reversibility of actual finite-step stationary Markov pairs

Nonnegative two-time correlations prove reversal symmetry of every kernel
power. The power retains its original initial coordinate. These lemmas are
applied below to the actual Gaussian MALA pair, rather than assuming reversible
powers or an abstract self-adjoint transition realization.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped NNReal ENNReal

namespace WassersteinMixing.StationaryKernelPower

variable {E : Type*} [MeasurableSpace E]

/-- Integration of an actual observable against an actual transition kernel. -/
def average (κ : Kernel E E) (f : E → ℝ≥0∞) (x : E) : ℝ≥0∞ := ∫⁻ y, f y ∂κ x

/-- Kernel integration preserves measurability of nonnegative observables. -/
theorem average_measurable (κ : Kernel E E) (f : E → ℝ≥0∞) (hf : Measurable f) :
    Measurable (average κ f) := hf.lintegral_kernel

/-- Every finite iterate of the averaging operation is measurable. -/
theorem average_iterate_measurable (κ : Kernel E E) (f : E → ℝ≥0∞)
    (hf : Measurable f) (n : ℕ) : Measurable ((average κ)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact average_measurable κ _ ih

/-- Actual pair-law reversal implies the nonnegative correlation identity. -/
theorem average_balance (μ : Measure E) [SFinite μ] (κ : Kernel E E)
    [IsSFiniteKernel κ] (hswap : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ)
    (f g : E → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * average κ g x ∂μ) = ∫⁻ x, average κ f x * g x ∂μ := by
  have hs := lintegral_map (μ := μ ⊗ₘ κ)
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
    measurable_swap
  rw [hswap] at hs
  calc
    _ = ∫⁻ p : E × E, f p.1 * g p.2 ∂(μ ⊗ₘ κ) := by
      rw [Measure.lintegral_compProd (f := fun p : E × E ↦ f p.1 * g p.2)
        (by fun_prop)]
      apply lintegral_congr
      intro x
      exact (lintegral_const_mul (f x) hg).symm
    _ = ∫⁻ p : E × E, f p.2 * g p.1 ∂(μ ⊗ₘ κ) := hs
    _ = _ := by
      rw [Measure.lintegral_compProd (f := fun p : E × E ↦ f p.2 * g p.1)
        (by fun_prop)]
      apply lintegral_congr
      intro x
      exact lintegral_mul_const (g x) hf

/-- Finite powers retain correlation reversal. This follows by induction
from one actual balance identity, with no power-reversibility premise. -/
theorem average_iterate_balance (μ : Measure E) [SFinite μ] (κ : Kernel E E)
    [IsSFiniteKernel κ] (hswap : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ)
    (f g : E → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (n : ℕ) :
    (∫⁻ x, f x * ((average κ)^[n] g) x ∂μ) =
      ∫⁻ x, ((average κ)^[n] f) x * g x ∂μ := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      _ = ∫⁻ x, average κ f x * ((average κ)^[n] g) x ∂μ :=
        average_balance μ κ hswap f _ hf (average_iterate_measurable κ g hg n)
      _ = ∫⁻ x, ((average κ)^[n] (average κ f)) x * g x ∂μ :=
        ih _ g (average_measurable κ f hf) hg
      _ = _ := by rw [← Function.iterate_succ_apply]

/-- The actual finite-step kernel, with the identity transition at time zero. -/
def kernelPower (κ : Kernel E E) : ℕ → Kernel E E
  | 0 => Kernel.id
  | n + 1 => kernelPower κ n ∘ₖ κ

instance kernelPower_isMarkov (κ : Kernel E E) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (kernelPower κ n) := by
  induction n with
  | zero => unfold kernelPower; infer_instance
  | succ n ih => unfold kernelPower; infer_instance

/-- Integrating against the finite-step kernel is the actual averaging iterate. -/
theorem kernelPower_average (κ : Kernel E E) (f : E → ℝ≥0∞) (hf : Measurable f)
    (n : ℕ) (x : E) : average (kernelPower κ n) f x = ((average κ)^[n] f) x := by
  induction n generalizing x with
  | zero =>
    change (∫⁻ y, f y ∂Kernel.id x) = f x
    exact Kernel.lintegral_id' hf x
  | succ n ih =>
    rw [kernelPower, Function.iterate_succ_apply']
    unfold average
    rw [Kernel.lintegral_comp _ _ _ hf]
    apply lintegral_congr
    intro y
    exact ih y


variable (μ : Measure E) [IsProbabilityMeasure μ] (κ : Kernel E E) [IsMarkovKernel κ]

/-- Rectangle masses of the anchored finite-step pair are genuine iterated
kernel correlations, rather than an independently postulated power law. -/
theorem kernelPower_rectangle (n : ℕ) (s t : Set E)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ ⊗ₘ kernelPower κ n) (s ×ˢ t) =
      ∫⁻ x, s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x *
        ((average κ)^[n] (t.indicator (fun _ ↦ (1 : ℝ≥0∞)))) x ∂μ := by
  rw [Measure.compProd_apply_prod hs ht, ← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  rw [← kernelPower_average κ _ (measurable_const.indicator ht) n x]
  unfold average
  rw [lintegral_indicator ht]
  by_cases hx : x ∈ s <;> simp [hx]

/-- Every anchored finite-step pair is reversible when the original actual
stationary pair is reversible. No symmetry of powers is assumed. -/
theorem kernelPower_pair_swap
    (hswap : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ) (n : ℕ) :
    (μ ⊗ₘ kernelPower κ n).map Prod.swap = μ ⊗ₘ kernelPower κ n := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply measurable_swap (hs.prod ht), Set.preimage_swap_prod]
  calc
    _ = ∫⁻ x, t.indicator (fun _ ↦ (1 : ℝ≥0∞)) x *
        ((average κ)^[n] (s.indicator (fun _ ↦ (1 : ℝ≥0∞)))) x ∂μ :=
      kernelPower_rectangle μ κ n t s ht hs
    _ = ∫⁻ x, ((average κ)^[n] (t.indicator (fun _ ↦ (1 : ℝ≥0∞)))) x *
        s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x ∂μ :=
      average_iterate_balance μ κ hswap _ _ (measurable_const.indicator ht)
        (measurable_const.indicator hs) n
    _ = _ := by
      simp_rw [mul_comm]
      exact (kernelPower_rectangle μ κ n s t hs ht).symm

/-- The initial anchor of the actual finite-step pair retains the original law. -/
theorem kernelPower_pair_fst (n : ℕ) :
    (μ ⊗ₘ kernelPower κ n).map Prod.fst = μ := by
  exact Measure.fst_compProd μ (kernelPower κ n)

/-- The final state retains the original law as a consequence of proved reversal. -/
theorem kernelPower_pair_snd
    (hswap : (μ ⊗ₘ κ).map Prod.swap = μ ⊗ₘ κ) (n : ℕ) :
    (μ ⊗ₘ kernelPower κ n).map Prod.snd = μ := by
  rw [ULA.marginals_eq_of_swap_invariant _ (kernelPower_pair_swap μ κ hswap n)]
  exact kernelPower_pair_fst μ κ n

end WassersteinMixing.StationaryKernelPower

namespace WassersteinMixing.MALAStationaryPair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [StandardBorelSpace E]

/-- The actual stationary MALA transition kernel, obtained by disintegrating
its proved current/next-state law, not by postulating a reversible operator. -/
def kernel (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) : Kernel E E := by
  have := jointLaw_isProbability V h L hdiff hLip
  exact (jointLaw V h).condKernel

instance kernel_isMarkov (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    IsMarkovKernel (kernel V h L hdiff hLip) := by
  have := jointLaw_isProbability V h L hdiff hLip
  unfold kernel
  infer_instance

/-- Disintegration identifies the kernel's actual stationary pair exactly. -/
theorem kernel_pair_eq (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    ULA.gibbsMeasure V ⊗ₘ kernel V h L hdiff hLip = jointLaw V h := by
  have := jointLaw_isProbability V h L hdiff hLip
  unfold kernel
  calc
    _ = (jointLaw V h).fst ⊗ₘ (jointLaw V h).condKernel := by
      rw [Measure.fst, jointLaw_fst V h L hdiff hLip]
    _ = _ := (jointLaw V h).disintegrate (jointLaw V h).condKernel

/-- The original kernel's reversibility is proved from the Gaussian pair density. -/
theorem kernel_pair_swap (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)] (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) :
    (ULA.gibbsMeasure V ⊗ₘ kernel V h L hdiff hLip).map Prod.swap =
      ULA.gibbsMeasure V ⊗ₘ kernel V h L hdiff hLip := by
  rw [kernel_pair_eq V h L hdiff hLip]
  exact jointLaw_swap V h L hh hdiff hLip

/-- The actual finite-step pair retains the initial Gibbs state as its first
coordinate, and advances the second coordinate through the conditional kernel. -/
def powerJointLaw (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    Measure (E × E) :=
  ULA.gibbsMeasure V ⊗ₘ StationaryKernelPower.kernelPower (kernel V h L hdiff hLip) n

instance powerJointLaw_isProbability (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    IsProbabilityMeasure (powerJointLaw V h L hdiff hLip n) := by
  unfold powerJointLaw
  infer_instance

/-- Exact detailed balance of every actual anchored finite-step MALA pair. -/
theorem powerJointLaw_swap (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)] (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    (powerJointLaw V h L hdiff hLip n).map Prod.swap = powerJointLaw V h L hdiff hLip n :=
  StationaryKernelPower.kernelPower_pair_swap (ULA.gibbsMeasure V)
    (kernel V h L hdiff hLip) (kernel_pair_swap V h L hh hdiff hLip) n

/-- The original initial-state anchor is preserved at every finite step. -/
theorem powerJointLaw_fst (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)]
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    (powerJointLaw V h L hdiff hLip n).map Prod.fst = ULA.gibbsMeasure V :=
  StationaryKernelPower.kernelPower_pair_fst (ULA.gibbsMeasure V)
    (kernel V h L hdiff hLip) n

/-- Every endpoint is stationary as a consequence of the proved anchored reversal. -/
theorem powerJointLaw_snd (V : E → ℝ) (h : ℝ) (L : ℝ≥0)
    [IsProbabilityMeasure (ULA.gibbsMeasure V)] (hh : 0 < h)
    (hdiff : Differentiable ℝ V) (hLip : LipschitzWith L (gradient V)) (n : ℕ) :
    (powerJointLaw V h L hdiff hLip n).map Prod.snd = ULA.gibbsMeasure V :=
  StationaryKernelPower.kernelPower_pair_snd (ULA.gibbsMeasure V)
    (kernel V h L hdiff hLip) (kernel_pair_swap V h L hh hdiff hLip) n

end WassersteinMixing.MALAStationaryPair
