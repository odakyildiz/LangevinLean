import ProximalLangevin.MYPGDNoise
import ProximalLangevin.SplittingTransport
import UnadjustedLangevin.InitialExtension
import UnadjustedLangevin.Recurrence

set_option linter.style.header false

/-! # Genuine Gaussian coupling for the algorithm without parameter noise

A fresh product Gaussian is used at every Markov transition. Both algorithms
use its latent coordinates; only MYIPLA uses its parameter coordinates.
The recurrence is derived from this concrete coupling.
-/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace
namespace ProximalLangevin
open ULA

section Moments
variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
  (P : Measure A) [IsProbabilityMeasure P]

/-- Globally Lipschitz maps preserve finite quadratic moments on a probability space. -/
theorem memLp_lipschitz_comp {D : E → E} {r : ℝ≥0} (hD : LipschitzWith r D)
    {X : A → E} (hX : MemLp X 2 P) : MemLp (fun x => D (X x)) 2 P := by
  have hc := (centered_lipschitz hD).comp_memLp (by simp) hX
  convert hc.add (memLp_const (D 0)) using 1
  funext x
  simp only [Function.comp_apply, Pi.add_apply, sub_add_cancel]

variable [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

omit [IsProbabilityMeasure P] [CompleteSpace E] in
/-- Direct finite-cost transport estimate for an actual L² pair. -/
theorem wasserstein_sq_le_integral_pair (X Y : A → E) (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    wasserstein2 (P.map X) (P.map Y) ≠ ⊤ ∧
    wasserstein2Real (P.map X) (P.map Y) ^ 2 ≤ ∫ x, ‖X x - Y x‖ ^ 2 ∂P := by
  let X' := hX.toLp X
  let Y' := hY.toLp Y
  have hx : P.map X' = P.map X := Measure.map_congr hX.coeFn_toLp
  have hy : P.map Y' = P.map Y := Measure.map_congr hY.coeFn_toLp
  have hb := wasserstein2_le_Lp_cost P X' Y'
  have hr := wasserstein2_le_Lp_cost_real P X' Y'
  rw [hx, hy] at hb hr
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb, ?_⟩
  have hs : wasserstein2Real (P.map X) (P.map Y)^2 ≤ ‖X'-Y'‖^2 :=
    (sq_le_sq₀ ENNReal.toReal_nonneg (norm_nonneg _)).mpr hr
  rw [lp_norm_sq_eq_integral P] at hs
  convert hs using 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub X' Y', hX.coeFn_toLp, hY.coeFn_toLp] with x hd hx hy
  rw [hd]
  simp only [Pi.sub_apply]
  change ‖X x-Y x‖^2 = ‖(hX.toLp X) x-(hY.toLp Y) x‖^2
  rw [hx, hy]

end Moments

section GaussianMaps
variable {N dθ dx : ℕ} {D : IPLA.State N dθ dx → IPLA.State N dθ dx}
    {r : ℝ≥0} (hD : LipschitzWith r D) (a : ℝ)

/-- The deterministic map followed by latent-only Gaussian noise. -/
def latentGaussianUpdate (D : IPLA.State N dθ dx → IPLA.State N dθ dx) (a : ℝ)
    (x z : IPLA.State N dθ dx) : IPLA.State N dθ dx := D x + a • latentNoiseCLM z

/-- The same map followed by full Gaussian noise. -/
def fullGaussianUpdate (D : IPLA.State N dθ dx → IPLA.State N dθ dx) (a : ℝ)
    (x z : IPLA.State N dθ dx) : IPLA.State N dθ dx := D x + a • z

include hD

theorem latentGaussianUpdate_measurable :
    Measurable (Function.uncurry (latentGaussianUpdate D a)) :=
  (hD.continuous.measurable.comp measurable_fst).add
    ((@latentNoiseCLM N dθ dx).continuous.measurable.comp measurable_snd |>.const_smul a)

theorem fullGaussianUpdate_measurable :
    Measurable (Function.uncurry (fullGaussianUpdate D a)) :=
  (hD.continuous.measurable.comp measurable_fst).add (measurable_snd.const_smul a)

theorem latentGaussianStep_memLp (μ : Measure (IPLA.State N dθ dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) :
    MemLp (fun x => x) 2
      (markovStep (latentGaussianUpdate D a) (stdGaussian (IPLA.State N dθ dx)) μ) := by
  apply (memLp_map_measure_iff (by fun_prop)
    (latentGaussianUpdate_measurable hD a).aemeasurable).mpr
  exact ((memLp_lipschitz_comp μ hD hμ).comp_fst _).add
    (((@latentNoiseCLM N dθ dx).comp_memLp'
      (IsGaussian.memLp_id _ 2 (by norm_num))).comp_snd μ |>.const_smul a)

theorem fullGaussianStep_memLp (μ : Measure (IPLA.State N dθ dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) :
    MemLp (fun x => x) 2
      (markovStep (fullGaussianUpdate D a) (stdGaussian (IPLA.State N dθ dx)) μ) := by
  apply (memLp_map_measure_iff (by fun_prop)
    (fullGaussianUpdate_measurable hD a).aemeasurable).mpr
  exact ((memLp_lipschitz_comp μ hD hμ).comp_fst _).add
    ((IsGaussian.memLp_id _ 2 (by norm_num)).comp_snd μ |>.const_smul a)

/-- Actual latent-noise and full-noise one-step laws admit the stated
squared coupling bound. The independent centered parameter noise supplies
exactly `a²*dθ`, and has no mixed contribution. -/
theorem latent_full_markov_coupling_sq
    (μ ν : Measure (IPLA.State N dθ dx)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x => x) 2 μ) (hν : MemLp (fun x => x) 2 ν)
    (c : Coupling μ ν) :
    wasserstein2
      (markovStep (latentGaussianUpdate D a) (stdGaussian _) μ)
      (markovStep (fullGaussianUpdate D a) (stdGaussian _) ν) ≠ ⊤ ∧
    wasserstein2Real
      (markovStep (latentGaussianUpdate D a) (stdGaussian _) μ)
      (markovStep (fullGaussianUpdate D a) (stdGaussian _) ν) ^ 2 ≤
      (r : ℝ)^2 * (couplingCost c.joint).toReal^2 + a^2*(dθ : ℝ) := by
  have := c.isProbabilityMeasure
  let Q := stdGaussian (IPLA.State N dθ dx)
  let P := c.joint.prod Q
  have hX : MemLp (fun p : IPLA.State N dθ dx × IPLA.State N dθ dx => p.1) 2 c.joint := by
    have h := hμ
    rw [← c.fst] at h
    exact h.comp_of_map measurable_fst.aemeasurable
  have hY : MemLp (fun p : IPLA.State N dθ dx × IPLA.State N dθ dx => p.2) 2 c.joint := by
    have h := hν
    rw [← c.snd] at h
    exact h.comp_of_map measurable_snd.aemeasurable
  let g := fun p : IPLA.State N dθ dx × IPLA.State N dθ dx => D p.1 - D p.2
  have hg : MemLp g 2 c.joint :=
    (memLp_lipschitz_comp c.joint hD hX).sub (memLp_lipschitz_comp c.joint hD hY)
  let F := fun p : (IPLA.State N dθ dx × IPLA.State N dθ dx) × IPLA.State N dθ dx =>
    latentGaussianUpdate D a p.1.1 p.2
  let H := fun p : (IPLA.State N dθ dx × IPLA.State N dθ dx) × IPLA.State N dθ dx =>
    fullGaussianUpdate D a p.1.2 p.2
  have hF : MemLp F 2 P :=
    ((memLp_lipschitz_comp c.joint hD hX).comp_fst Q).add
      (((@latentNoiseCLM N dθ dx).comp_memLp'
        (IsGaussian.memLp_id Q 2 (by norm_num))).comp_snd c.joint |>.const_smul a)
  have hH : MemLp H 2 P :=
    ((memLp_lipschitz_comp c.joint hD hY).comp_fst Q).add
      ((IsGaussian.memLp_id Q 2 (by norm_num)).comp_snd c.joint |>.const_smul a)
  have hFlaw : P.map F = markovStep (latentGaussianUpdate D a) Q μ :=
    initialExtension_map c Q _ (latentGaussianUpdate_measurable hD a)
  have hHlaw : P.map H = markovStep (fullGaussianUpdate D a) Q ν := by
    have hmap : P.map (fun p => (p.1.2, p.2)) = ν.prod Q := by
      change (c.joint.prod Q).map (Prod.map Prod.snd id) = _
      simpa only [c.snd, Measure.map_id] using
        (Measure.map_prod_map c.joint Q measurable_snd measurable_id).symm
    rw [markovStep, ← hmap,
      Measure.map_map (fullGaussianUpdate_measurable hD a) (by fun_prop)]
    rfl
  have hbase := wasserstein_sq_le_integral_pair P F H hF hH
  rw [hFlaw, hHlaw] at hbase
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  have hid (p) : F p - H p = g p.1 + (-a) • parameterNoiseCLM p.2 := by
    dsimp [F, H, g, latentGaussianUpdate, fullGaussianUpdate, latentNoiseCLM]
    simp only [sub_apply, ContinuousLinearMap.id_apply]
    module
  simp_rw [hid]
  rw [integral_add_parameterNoise_sq c.joint g hg, neg_sq]
  have hi : (∫ p, ‖g p‖^2 ∂c.joint) ≤
      (r : ℝ)^2 * ∫ p : IPLA.State N dθ dx × IPLA.State N dθ dx, ‖p.1-p.2‖^2 ∂c.joint := by
    rw [← integral_const_mul]
    apply integral_mono (hg.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    · exact ((hX.sub hY).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul _
    · intro p
      have hh := hD.norm_sub_le p.1 p.2
      dsimp [g]
      nlinarith [norm_nonneg (D p.1-D p.2), norm_nonneg (p.1-p.2)]
  have hnorm : (∫ p : IPLA.State N dθ dx × IPLA.State N dθ dx,
      ‖p.1-p.2‖^2 ∂c.joint) = (couplingCost c.joint).toReal^2 := by
    let X := (hX.sub hY).toLp
      (fun p : IPLA.State N dθ dx × IPLA.State N dθ dx => p.1-p.2)
    have hn := lp_norm_sq_eq_integral c.joint X
    rw [Lp.norm_toLp] at hn
    change (couplingCost c.joint).toReal^2 = _ at hn
    rw [hn]
    exact (integral_congr_ae ((hX.sub hY).coeFn_toLp.fun_comp fun v => ‖v‖^2)).symm
  rw [hnorm] at hi
  exact add_le_add hi le_rfl

end GaussianMaps
end ProximalLangevin
