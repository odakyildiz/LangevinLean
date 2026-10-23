import KineticLangevin.SplittingTarget
import KineticLangevin.SplittingLaw
import KineticLangevin.LpPhaseLaw

/-! # Exact kinetic Gibbs stationarity from the actual initial/noise source

The input hypotheses are explicit laws of the initial state and Brownian
innovation stream. Numerical weak errors, numerical convergence, and the
stationary conclusion are all derived inside the proof.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace KineticLangevin
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] (P : Measure Ω) [IsProbabilityMeasure P]

/-- Any actual continuous kinetic integral solution with the target initial
law and the actual independent OU innovation stream remains Gibbs distributed. -/
theorem kinetic_integral_stationary_of_jointNoise
    (f : E → ℝ) (m : ℝ) (hm : 0<m) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f))
    (initial : Lp E 2 P × Lp E 2 P) (B : ℝ → Lp E 2 P) (hB : Continuous B) (hB0 : B 0=0)
    (hjoint : ∀ h : ℝ≥0, HasLaw
      (fun ω ↦ (lpPhaseCoe P initial ω,fun k : ℕ ↦
        ouInputIncrement γ B ((k : ℝ)*h) h ω))
      ((kineticGibbsTarget f).prod (Measure.infinitePi (fun _ : ℕ ↦ ouThermalLaw (E := E) γ h))) P)
    (Y : ℝ → Lp E 2 P × Lp E 2 P) (hY : Continuous Y) (T : ℝ≥0)
    (heY : ∀ t ∈ Icc 0 (T : ℝ), Y t-initial =
      -(∫ s in 0..t,kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (Y s))+(B t,0)) :
    P.map (lpPhaseCoe P (Y T))=kineticGibbsTarget f := by
  haveI := kineticGibbsTarget_probability f m hm hf hsc
  let G := ULA.lpDrift P (gradient f) hLip
  let K : ℝ := (M : ℝ)*(2*(M : ℝ)+11)/8
  let A : ℝ := ∫ z,‖z.1‖^2+‖gradient f z.2‖^2 ∂kineticGibbsTarget f
  let Sn : ℕ → Lp E 2 P × Lp E 2 P := fun n ↦
    kineticSplitChain G γ ((T : ℝ)/((n+1 : ℕ) : ℝ)) initial B (n+1)
  let δ : ℕ → ℝ := fun n ↦ (2*(T : ℝ)^2*K*A)/((n+1 : ℕ) : ℝ)
  have hδ : Tendsto δ atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat _)
  have hconv : Tendsto Sn atTop (𝓝 (Y T)) :=
    kineticSplitChain_tendsto G M γ (ULA.lpDrift_lipschitz P (gradient f) hLip)
      initial B Y hB hB0 hY T T.coe_nonneg heY
  have hmesh : Tendsto (fun n : ℕ ↦ (T : ℝ)/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr (tendsto_const_div_atTop_nhds_zero_nat (T : ℝ))
  apply measure_map_lpPhase_eq_of_bounded_test_error P (Y T) Sn hconv
    (kineticGibbsTarget f) δ hδ
  intro F hF hFb
  filter_upwards [hmesh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1))] with n hn
  let h : ℝ≥0 := T/((n+1 : ℕ) : ℝ≥0)
  have hc : (h : ℝ)=(T : ℝ)/((n+1 : ℕ) : ℝ) := by simp [h]
  have hh1 : (h : ℝ)≤1 := by rw [hc]; exact hn.le
  let N : ℕ → Lp E 2 P := fun k ↦ ouInputIncrement γ B ((k : ℝ)*h) h
  have hlaw := lp_kineticSplitNoiseChain_law_of_jointLaw P (gradient f) M hLip γ h
    initial N (kineticGibbsTarget f) (ouThermalLaw γ h) (hjoint h) (n+1)
  have hchain : Sn n=kineticSplitNoiseChain G γ h initial N (n+1) := by
    dsimp [Sn]
    rw [← hc,kineticSplitChain_eq_noiseChain]
  rw [← hchain] at hlaw
  have htest : (∫ ω,F (lpPhaseCoe P (Sn n) ω) ∂P)=
      ∫ z,F z ∂ULA.markovLaws (kineticSplitStep (gradient f) γ h)
        (ouThermalLaw γ h) (kineticGibbsTarget f) (n+1) := by
    rw [← hlaw,integral_map (measurable_lpPhaseCoe P (Sn n)).aemeasurable hF.aestronglyMeasurable]
  rw [htest]
  have hw := kineticSplitLaws_stationary_weak_error f m hm M hf hsc hLip
    γ h γ.coe_nonneg h.coe_nonneg hh1 F hF 1 (by norm_num) hFb (n+1)
  convert hw using 1
  dsimp [δ,K,A]
  rw [hc]
  field_simp

end KineticLangevin
