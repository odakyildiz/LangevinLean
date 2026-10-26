import PBGSO.RawIntegralCLM
import PBGSO.RawLocalGauge

/-! # Bounded linear maps of actual locally defined Brownian integrals
The raw transformed diffusion and a shared scaled local energy are explicitly
constructed. All stopped computed integrals commute with the map; genuine
localization then gives the original local-noise identity. No global expected
coefficient square, stochastic-output match or energy formula is an input.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I Z Y : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {T : ℝ≥0}

def RawLocalDiffusion.scaleGauge (L : RawLocalDiffusion (Z := Z) Q D T) (c : ℝ) (hc : 1 ≤ c) :
    RawLocalDiffusion (Z := Z) Q D T where
  sigma := L.sigma
  sigma_strong := L.sigma_strong
  sigma_adapted := L.sigma_adapted
  q r ω := c * L.q r ω
  q_strong := stronglyMeasurable_const.mul L.q_strong
  q_nonneg r ω := mul_nonneg (le_trans zero_le_one hc) (L.q_nonneg r ω)
  q_local ω := (L.q_local ω).const_mul c
  q_progressive t := by
    have hm : StronglyMeasurable[(inferInstance : MeasurableSpace ℝ).prod (D.filtration t)]
        (fun _ : ℝ × Ω => c) := stronglyMeasurable_const
    convert hm.mul (L.q_progressive t) using 1
    funext p
    by_cases h : p.1 ∈ Ioc 0 (t : ℝ) <;> simp [h]
  sigma_control r ω := (L.sigma_control r ω).trans (by
    nlinarith [L.q_nonneg r ω])

def RawLocalDiffusion.linearMap (L : RawLocalDiffusion (Z := Z) Q D T) (A : Z →L[ℝ] Y) :
    RawLocalDiffusion (Z := Y) Q D T where
  sigma i r ω := A (L.sigma i r ω)
  sigma_strong := rawMap_stronglyMeasurable A L.sigma L.sigma_strong
  sigma_adapted := rawMap_adapted Q A D L.sigma L.sigma_adapted
  q := (L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).q
  q_strong := (L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).q_strong
  q_nonneg := (L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).q_nonneg
  q_local := (L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).q_local
  q_progressive := (L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).q_progressive
  sigma_control r ω := by
    calc
      _ ≤ ∑ i, (‖A‖ * ‖L.sigma i r ω‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
      _ = ‖A‖ ^ 2 * ∑ i, ‖L.sigma i r ω‖ ^ 2 := by
        simp_rw [mul_pow]
        rw [Finset.mul_sum]
      _ ≤ ‖A‖ ^ 2 * L.q r ω := mul_le_mul_of_nonneg_left (L.sigma_control r ω) (sq_nonneg _)
      _ ≤ max 1 (‖A‖ ^ 2) * L.q r ω :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (L.q_nonneg r ω)

variable (L : RawLocalDiffusion (Z := Z) Q D T) (A : Z →L[ℝ] Y)

theorem RawLocalDiffusion.linearMap_stop (n : ℕ) (ω : Ω) :
    (L.linearMap A).stop n ω = (L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).stop n ω := rfl

theorem RawLocalDiffusion.linearMap_stoppedSigma (n : ℕ) (i : I) (r : ℝ) (ω : Ω) :
    (L.linearMap A).stoppedSigma n i r ω =
      A ((L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).stoppedSigma n i r ω) := by
  change (if r ≤ ((L.linearMap A).stop n ω : ℝ) then A (L.sigma i r ω) else 0) =
    A (if r ≤ ((L.linearMap A).stop n ω : ℝ) then L.sigma i r ω else 0)
  split_ifs <;> simp

theorem RawLocalDiffusion.linearMap_noise (n : ℕ) (t : ℝ≥0) :
    (L.linearMap A).noise n t = A.compLpL 2 Q
      ((L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).noise n t) := by
  let K := L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)
  have he : ∀ i, Function.uncurry ((L.linearMap A).stoppedSigma n i) =ᵐ[
      (volume.restrict (Ioc 0 (T : ℝ))).prod Q]
        (fun p : ℝ × Ω => A (K.stoppedSigma n i p.1 p.2)) :=
    fun i => Eventually.of_forall (fun p => L.linearMap_stoppedSigma A n i p.1 p.2)
  have hi := rawDiffusionIntegral_congr_ae_coefficients Q D T
    ((L.linearMap A).stoppedSigma n) (fun i r ω => A (K.stoppedSigma n i r ω))
    ((L.linearMap A).stoppedSigma_strong n)
    (rawMap_stronglyMeasurable A (K.stoppedSigma n) (K.stoppedSigma_strong n))
    ((L.linearMap A).stoppedSigma_square n)
    (rawMap_square Q A T (K.stoppedSigma n) (K.stoppedSigma_strong n) (K.stoppedSigma_square n))
    ((L.linearMap A).stoppedSigma_adapted n)
    (rawMap_adapted Q A D (K.stoppedSigma n) (K.stoppedSigma_adapted n)) he t
  exact hi.trans (rawDiffusionIntegral_map Q A D T (K.stoppedSigma n) (K.stoppedSigma_strong n)
    (K.stoppedSigma_square n) (K.stoppedSigma_adapted n) t)

theorem RawLocalDiffusion.linearMap_version_ae (n : ℕ) (t : ℝ≥0) :
    (L.linearMap A).version n t =ᵐ[Q] fun ω =>
      A ((L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).version n t ω) := by
  have h := (L.linearMap A).version_ae n t
  rw [L.linearMap_noise A n t] at h
  exact h.trans ((A.coeFn_compLpL _).trans
    (((L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)).version_ae n t).symm.fun_comp A))

/-- Actual local integration commutes with every bounded linear state map. -/
theorem RawLocalDiffusion.linearMap_localNoise_ae (t : ℝ≥0) (ht : t ≤ T) :
    (L.linearMap A).localNoise t =ᵐ[Q] fun ω => A (L.localNoise t ω) := by
  let K := L.scaleGauge (max 1 (‖A‖ ^ 2)) (le_max_left _ _)
  have hg : ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → K.localNoise t ω = L.localNoise t ω :=
    K.localNoise_gauge_congr_of_eq L (fun i r ω => rfl)
  filter_upwards [ae_all_iff.mpr (fun n => L.linearMap_version_ae A n t),
    (L.linearMap A).version_eventually_localNoise, K.version_eventually_localNoise,hg]
      with ω hn hl hk hg
  obtain ⟨n,hnl,hnk⟩ := ((hl t ht).and (hk t ht)).exists
  exact hnl.symm.trans ((hn n).trans (congrArg A (hnk.trans (hg t ht))))

theorem RawLocalDiffusion.linearMap_localNoise_on_horizon :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → (L.linearMap A).localNoise t ω = A (L.localNoise t ω) := by
  let H := Iic T
  letI : Nonempty H := ⟨⟨0,by simp [H]⟩⟩
  let τ := TopologicalSpace.denseSeq H
  filter_upwards [(L.linearMap A).localNoise_continuous,L.localNoise_continuous,
    ae_all_iff.mpr (fun n => L.linearMap_localNoise_ae A (τ n).val (τ n).property)] with ω hl hk hn
  have hc : Continuous (fun t : H => (L.linearMap A).localNoise t.val ω) := hl.comp continuous_subtype_val
  have hc' : Continuous (fun t : H => A (L.localNoise t.val ω)) :=
    A.continuous.comp (hk.comp continuous_subtype_val)
  have he := (TopologicalSpace.denseRange_denseSeq H).equalizer hc hc' (funext hn)
  intro t ht
  exact congrFun he (⟨t,ht⟩ : H)

/-- Any original raw target coefficient realization has this same mapped
local noise, regardless of the chosen primitive local-energy gauge. -/
theorem RawLocalDiffusion.localNoise_linearMap_congr
    (K : RawLocalDiffusion (Z := Y) Q D T)
    (hσ : ∀ᵐ ω ∂Q, ∀ i r, r ∈ Ioc 0 (T : ℝ) → K.sigma i r ω = A (L.sigma i r ω)) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → K.localNoise t ω = A (L.localNoise t ω) := by
  filter_upwards [K.localNoise_gauge_congr_on_horizon (L.linearMap A) hσ,
    L.linearMap_localNoise_on_horizon A] with ω hg hl
  intro t ht
  exact (hg t ht).trans (hl t ht)

end PBGSO.FilteredBrownian
