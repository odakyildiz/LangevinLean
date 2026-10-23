import KIPLMC.Exponential
import KIPLMC.Splitting
import KIPLMC.Noise
import UnadjustedLangevin.MarkovLaw
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # Actual kinetic particle chain laws

The independent-noise Markov transition and the pathwise implementation have
the same law. The generic independence proof from ULA is reused for both
kinetic algorithms; no independence of the current state and fresh innovation
is inserted as an extra assumption at every time step.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace KIPLMC

/-- Noise for the two independent OBABO thermostat half-steps. -/
def obaboNoise (N dθ dx : ℕ) : Measure (State N dθ dx × State N dθ dx) :=
  (stdGaussian (State N dθ dx)).prod (stdGaussian (State N dθ dx))

instance obaboNoise_probability (N dθ dx : ℕ) :
    IsProbabilityMeasure (obaboNoise N dθ dx) := by
  unfold obaboNoise
  infer_instance

theorem kiplmc1Step_measurable {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    {L : ℝ≥0} (hN : 0 < N) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (γ h : ℝ) :
    Measurable (Function.uncurry (@kiplmc1Step N dθ dx U γ h)) := by
  have hg : Continuous (@force N dθ dx U) := (force_lipschitz hN hdiff hLip).continuous
  apply Continuous.measurable
  unfold Function.uncurry kiplmc1Step KineticLangevin.exponentialStep
  fun_prop

theorem kiplmc2Step_measurable {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    {L : ℝ≥0} (hN : 0 < N) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (γ h : ℝ) :
    Measurable (Function.uncurry (fun z (ξ : State N dθ dx × State N dθ dx) ↦
      @kiplmc2Step N dθ dx U γ h z ξ.1 ξ.2)) := by
  have hg : Continuous (@force N dθ dx U) := (force_lipschitz hN hdiff hLip).continuous
  apply Continuous.measurable
  unfold Function.uncurry kiplmc2Step KineticLangevin.obaboStep
    KineticLangevin.ornsteinStep KineticLangevin.kickStep KineticLangevin.driftStep
  fun_prop

/-- The exponential-chain law for a specified correlated phase innovation.
The covariance specification and its construction are separate from this
algorithm-independent law identity. -/
def kiplmc1Laws {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (μ η : Measure (State N dθ dx × State N dθ dx)) (n : ℕ) :=
  ULA.markovLaws (kiplmc1Step U γ h) η μ n

/-- The actual KIPLMC1 laws with the constructed correlated Gaussian noise. -/
def kiplmc1GaussianLaws {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (μ : Measure (State N dθ dx × State N dθ dx)) (n : ℕ) :=
  kiplmc1Laws U γ h μ (exponentialNoise N dθ dx γ h) n

/-- The actual independent-Gaussian OBABO law at iteration `n`. -/
def kiplmc2Laws {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (μ : Measure (State N dθ dx × State N dθ dx)) (n : ℕ) :=
  ULA.markovLaws (fun z ξ ↦ kiplmc2Step U γ h z ξ.1 ξ.2) (obaboNoise N dθ dx) μ n

/-- The Algorithm 2 trajectory with both thermostat noise vectors supplied
at every step. -/
def kiplmc2Chain {N dθ dx : ℕ} (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx)
    (noise : ℕ → State N dθ dx × State N dθ dx) (n : ℕ) :=
  ULA.noiseDrivenChain (fun z ξ ↦ kiplmc2Step U γ h z ξ.1 ξ.2) z noise n

theorem kiplmc1Laws_probability {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    {L : ℝ≥0} (hN : 0 < N) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (γ h : ℝ)
    (μ η : Measure (State N dθ dx × State N dθ dx))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure η] (n : ℕ) :
    IsProbabilityMeasure (kiplmc1Laws U γ h μ η n) :=
  ULA.markovLaws_isProbability _ (kiplmc1Step_measurable hN hdiff hLip γ h) μ η n

theorem kiplmc2Laws_probability {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ}
    {L : ℝ≥0} (hN : 0 < N) (hdiff : Differentiable ℝ U)
    (hLip : LipschitzWith L (gradient U)) (γ h : ℝ)
    (μ : Measure (State N dθ dx × State N dθ dx)) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (kiplmc2Laws U γ h μ n) :=
  ULA.markovLaws_isProbability _ (kiplmc2Step_measurable hN hdiff hLip γ h) μ _ n

/-- The explicit KIPLMC1 recursion and the shared generic recursion agree. -/
theorem kiplmc1Chain_eq_noiseDrivenChain {N dθ dx : ℕ}
    (U : IPLA.Joint dθ dx → ℝ) (γ h : ℝ)
    (z : State N dθ dx × State N dθ dx)
    (noise : ℕ → State N dθ dx × State N dθ dx) (n : ℕ) :
    kiplmc1Chain U γ h z noise n =
      ULA.noiseDrivenChain (kiplmc1Step U γ h) z noise n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [kiplmc1Chain, ULA.noiseDrivenChain_succ, ih]

/-- Any independent realization of Algorithm 1 has the same iterated law.
This is a pushforward equality for the actual random variables. -/
theorem kiplmc1Chain_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ} {L : ℝ≥0}
    (hN : 0 < N) (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (γ h : ℝ) (X : Ω → State N dθ dx × State N dθ dx)
    (W : ℕ → Ω → State N dθ dx × State N dθ dx)
    (hX : AEMeasurable X P) (hW : ∀ n, AEMeasurable (W n) P)
    (hind : IndepFun X (fun ω n ↦ W n ω) P) (hiid : iIndepFun W P)
    (η : Measure (State N dθ dx × State N dθ dx)) [IsProbabilityMeasure η]
    (hlaw : ∀ n, P.map (W n) = η) (n : ℕ) :
    P.map (fun ω ↦ kiplmc1Chain U γ h (X ω) (fun k ↦ W k ω) n) =
      kiplmc1Laws U γ h (P.map X) η n := by
  simp_rw [kiplmc1Chain_eq_noiseDrivenChain]
  exact ULA.noiseDrivenChain_law_eq_markovLaws P _
    (kiplmc1Step_measurable hN hdiff hLip γ h) X W hX hW hind hiid η hlaw n

/-- The actual iid standard-Gaussian realization of Algorithm 2 has exactly
the iterated OBABO transition law. Independence within a noise pair is encoded
by its product-Gaussian law, and across steps by `hiid`. -/
theorem kiplmc2Chain_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ} {L : ℝ≥0}
    (hN : 0 < N) (hdiff : Differentiable ℝ U) (hLip : LipschitzWith L (gradient U))
    (γ h : ℝ) (X : Ω → State N dθ dx × State N dθ dx)
    (W : ℕ → Ω → State N dθ dx × State N dθ dx)
    (hX : AEMeasurable X P) (hW : ∀ n, AEMeasurable (W n) P)
    (hind : IndepFun X (fun ω n ↦ W n ω) P) (hiid : iIndepFun W P)
    (hlaw : ∀ n, P.map (W n) = obaboNoise N dθ dx) (n : ℕ) :
    P.map (fun ω ↦ kiplmc2Chain U γ h (X ω) (fun k ↦ W k ω) n) =
      kiplmc2Laws U γ h (P.map X) n :=
  ULA.noiseDrivenChain_law_eq_markovLaws P _
    (kiplmc2Step_measurable hN hdiff hLip γ h) X W hX hW hind hiid _ hlaw n

end KIPLMC
