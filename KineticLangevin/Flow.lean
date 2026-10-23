import KineticLangevin.Dynamics
import UnadjustedLangevin.LangevinUniqueness
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

/-! # Continuous dependence of the actual kinetic solution flow

The additive forcing is a concrete continuous path. We first prove stability
when both the initial condition and the entire forcing path vary. Compact
velocity paths are extended by clipping time to the horizon and subtracting
their value at zero. The resulting canonical kinetic solution is selected
from the proved Picard construction, not postulated. Its endpoint is jointly
Lipschitz in the initial phase and the compact forcing path.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Continuous additive integral solutions depend continuously on both their
initial condition and a uniformly perturbed additive forcing. -/
theorem additive_integral_input_stability
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (x y : E) (B C Y Z : ℝ → E)
    (hB : Continuous B) (hC : Continuous C) (hY : Continuous Y) (hZ : Continuous Z)
    (T D : ℝ) (hD : 0 ≤ D)
    (hinput : ∀ t ∈ Icc 0 T, ‖B t - C t‖ ≤ D)
    (hYe : ∀ t ∈ Icc 0 T, Y t - x = -(∫ s in 0..t, g (Y s)) + B t)
    (hZe : ∀ t ∈ Icc 0 T, Z t - y = -(∫ s in 0..t, g (Z s)) + C t)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖Y t - Z t‖ ≤ (‖x - y‖ + D) * Real.exp (((L : ℝ) + 1) * t) := by
  let F : ℝ → E := fun s ↦ Y s - Z s - (B s - C s)
  let G : ℝ → E := fun s ↦ (x - y) -
    ((∫ r in 0..s, g (Y r)) - ∫ r in 0..s, g (Z r))
  have hFG : ∀ s ∈ Icc 0 T, F s = G s := by
    intro s hs
    have hy := hYe s hs
    have hz := hZe s hs
    dsimp [F, G]
    rw [sub_eq_iff_eq_add] at hy hz
    rw [hy, hz]
    abel
  have hcY : Continuous (fun s ↦ g (Y s)) := hg.continuous.comp hY
  have hcZ : Continuous (fun s ↦ g (Z s)) := hg.continuous.comp hZ
  have hder : ∀ s ∈ Ico 0 T,
      HasDerivWithinAt F (-(g (Y s) - g (Z s))) (Ici s) s := by
    intro s hs
    have hiY := intervalIntegral.integral_hasDerivAt_right
      (hcY.intervalIntegrable 0 s) (hcY.stronglyMeasurableAtFilter volume (𝓝 s)) hcY.continuousAt
    have hiZ := intervalIntegral.integral_hasDerivAt_right
      (hcZ.intervalIntegrable 0 s) (hcZ.stronglyMeasurableAtFilter volume (𝓝 s)) hcZ.continuousAt
    have hd : HasDerivAt G (-(g (Y s) - g (Z s))) s := by
      convert (hasDerivAt_const s (x - y)).sub (hiY.sub hiZ) using 1
      simp
    have hevent : F =ᶠ[𝓝[Ici s] s] G := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hs.2)] with r hr hrt
      exact hFG r ⟨hs.1.trans hr, hrt.le⟩
    exact hd.hasDerivWithinAt.congr_of_eventuallyEq hevent (hFG s ⟨hs.1, hs.2.le⟩)
  have hnorm (s : ℝ) (hs : s ∈ Icc 0 T) : ‖Y s - Z s‖ ≤ ‖F s‖ + D := by
    have he : Y s - Z s = F s + (B s - C s) := by dsimp [F]; abel
    rw [he]
    exact (norm_add_le _ _).trans (by linarith [hinput s hs])
  have hb (s : ℝ) (hs : s ∈ Ico 0 T) :
      ‖-(g (Y s) - g (Z s))‖ ≤ ((L : ℝ) + 1) * ‖F s‖ + ((L : ℝ) + 1) * D := by
    have hLip := hg.norm_sub_le (Y s) (Z s)
    have hmul := mul_le_mul_of_nonneg_left (hnorm s ⟨hs.1,hs.2.le⟩) L.coe_nonneg
    rw [norm_neg]
    nlinarith [norm_nonneg (F s)]
  have hF0 : F 0 = x - y := by
    simpa only [G, intervalIntegral.integral_same, sub_self, sub_zero] using
      hFG 0 ⟨le_rfl, ht.1.trans ht.2⟩
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := F) (f' := fun s ↦ -(g (Y s) - g (Z s)))
    (δ := ‖x-y‖) (K := (L : ℝ)+1) (ε := ((L : ℝ)+1)*D)
    ((hY.sub hZ).sub (hB.sub hC)).continuousOn hder (by rw [hF0]) hb t ht
  have hK : (L : ℝ) + 1 ≠ 0 := by positivity
  rw [gronwallBound_of_K_ne_0 hK, sub_zero] at hgr
  have hcancel : (((L : ℝ) + 1) * D) / ((L : ℝ) + 1) = D := by field_simp
  rw [hcancel] at hgr
  have hn := hnorm t ht
  nlinarith

/-- Continuous velocity forcing on a fixed compact horizon, with its sup norm. -/
abbrev VelocityForcing (T : ℝ) := C(Icc (0 : ℝ) T, E)

/-- Extend a compact forcing by clipped time and normalize its initial value. -/
def normalizedForcing (T : ℝ) (hT : 0 ≤ T) (B : VelocityForcing (E := E) T)
    (t : ℝ) : E := B (projIcc 0 T hT t) - B ⟨0, ⟨le_rfl, hT⟩⟩

theorem continuous_normalizedForcing (T : ℝ) (hT : 0 ≤ T)
    (B : VelocityForcing (E := E) T) : Continuous (normalizedForcing T hT B) :=
  (B.continuous.comp continuous_projIcc).sub continuous_const

@[simp] theorem normalizedForcing_zero (T : ℝ) (hT : 0 ≤ T)
    (B : VelocityForcing (E := E) T) : normalizedForcing T hT B 0 = 0 := by
  simp [normalizedForcing]

/-- The normalized extension is Lipschitz in the compact-path sup norm. -/
theorem normalizedForcing_sub_le (T : ℝ) (hT : 0 ≤ T)
    (B C : VelocityForcing (E := E) T) (t : ℝ) :
    ‖normalizedForcing T hT B t - normalizedForcing T hT C t‖ ≤ 2 * ‖B - C‖ := by
  have h1 := (B-C).norm_coe_le_norm (projIcc 0 T hT t)
  have h0 := (B-C).norm_coe_le_norm ⟨0,⟨le_rfl,hT⟩⟩
  have he : normalizedForcing T hT B t - normalizedForcing T hT C t =
      (B-C) (projIcc 0 T hT t) - (B-C) ⟨0,⟨le_rfl,hT⟩⟩ := by
    simp only [normalizedForcing, ContinuousMap.sub_apply]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

/-- A canonical actual kinetic path, selected from the proved existence theorem. -/
def kineticFlow (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (initial : E × E) (B : VelocityForcing (E := E) T) :
    ℝ → E × E :=
  Classical.choose (exists_kinetic_integral g L γ u hg initial (normalizedForcing T hT B)
    (continuous_normalizedForcing T hT B) (normalizedForcing_zero T hT B) T hT)

theorem kineticFlow_spec (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (initial : E × E) (B : VelocityForcing (E := E) T) :
    Continuous (kineticFlow g L γ u hg T hT initial B) ∧
      kineticFlow g L γ u hg T hT initial B 0 = initial ∧
      ∀ t ∈ Icc 0 T,
        kineticFlow g L γ u hg T hT initial B t - initial =
          -(∫ s in 0..t, kineticNegativeDrift g γ u (kineticFlow g L γ u hg T hT initial B s)) +
            (normalizedForcing T hT B t, 0) :=
  Classical.choose_spec (exists_kinetic_integral g L γ u hg initial (normalizedForcing T hT B)
    (continuous_normalizedForcing T hT B) (normalizedForcing_zero T hT B) T hT)


/-- Any other continuous solution of the same actual integral equation
agrees with the selected flow on the horizon. -/
theorem kineticFlow_eq_of_integral (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (initial : E × E) (B : VelocityForcing (E := E) T)
    (Y : ℝ → E × E) (hY : Continuous Y)
    (heY : ∀ t ∈ Icc 0 T, Y t - initial =
      -(∫ s in 0..t, kineticNegativeDrift g γ u (Y s)) + (normalizedForcing T hT B t,0)) :
    EqOn (kineticFlow g L γ u hg T hT initial B) Y (Icc 0 T) := by
  have hs := kineticFlow_spec g L γ u hg T hT initial B
  exact ULA.langevin_integral_unique (kineticNegativeDrift g γ u) (γ + u * L + 1)
    (kineticNegativeDrift_lipschitz g L γ u hg) initial
    (fun t ↦ (normalizedForcing T hT B t,0)) _ Y hs.1 hY T hT hs.2.2 heY

/-- The selected kinetic paths inherit the proved two-input stability estimate. -/
theorem kineticFlow_input_stability (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (initial other : E × E)
    (B C : VelocityForcing (E := E) T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    ‖kineticFlow g L γ u hg T hT initial B t - kineticFlow g L γ u hg T hT other C t‖ ≤
      (‖initial-other‖ + 2 * ‖B-C‖) *
        Real.exp (((γ + u * L + 1 : ℝ≥0) : ℝ) * t + t) := by
  have hs := kineticFlow_spec g L γ u hg T hT initial B
  have hs' := kineticFlow_spec g L γ u hg T hT other C
  have hb : ∀ s ∈ Icc 0 T,
      ‖(normalizedForcing T hT B s, (0 : E)) - (normalizedForcing T hT C s, 0)‖ ≤
        2 * ‖B-C‖ := by
    intro s _
    change max ‖normalizedForcing T hT B s - normalizedForcing T hT C s‖ ‖(0 : E) - 0‖ ≤ _
    simpa only [sub_self, norm_zero, max_eq_left (norm_nonneg _)] using
      normalizedForcing_sub_le T hT B C s
  have he := additive_integral_input_stability (kineticNegativeDrift g γ u)
    (γ + u * L + 1) (kineticNegativeDrift_lipschitz g L γ u hg)
    initial other (fun s ↦ (normalizedForcing T hT B s, 0))
    (fun s ↦ (normalizedForcing T hT C s, 0))
    (kineticFlow g L γ u hg T hT initial B) (kineticFlow g L γ u hg T hT other C)
    ((continuous_normalizedForcing T hT B).prodMk continuous_const)
    ((continuous_normalizedForcing T hT C).prodMk continuous_const)
    hs.1 hs'.1 T (2 * ‖B-C‖) (by positivity) hb hs.2.2 hs'.2.2 t ht
  simpa only [add_mul, one_mul] using he

/-- At each time on the horizon, the actual solution endpoint is jointly
Lipschitz in initialization and the compact velocity-noise path. -/
theorem kineticFlow_endpoint_lipschitz (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    LipschitzWith ⟨3 * Real.exp (((γ + u * L + 1 : ℝ≥0) : ℝ) * t + t), by positivity⟩
      (fun p : (E × E) × VelocityForcing (E := E) T ↦
        kineticFlow g L γ u hg T hT p.1 p.2 t) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have he := kineticFlow_input_stability g L γ u hg T hT p.1 q.1 p.2 q.2 t ht
  have h1 : ‖p.1 - q.1‖ ≤ ‖p-q‖ := by simpa using norm_fst_le (p-q)
  have h2 : ‖p.2 - q.2‖ ≤ ‖p-q‖ := by simpa using norm_snd_le (p-q)
  simp only [dist_eq_norm]
  change ‖kineticFlow g L γ u hg T hT p.1 p.2 t -
    kineticFlow g L γ u hg T hT q.1 q.2 t‖ ≤
      (3 * Real.exp (((γ + u * L + 1 : ℝ≥0) : ℝ) * t + t)) * ‖p-q‖
  have hsum : ‖p.1-q.1‖ + 2 * ‖p.2-q.2‖ ≤ 3 * ‖p-q‖ := by linarith
  have hm := mul_le_mul_of_nonneg_right hsum
    (Real.exp_pos (((γ + u * L + 1 : ℝ≥0) : ℝ) * t + t)).le
  exact he.trans (by nlinarith [hm])

/-- Measurability follows from proved continuity of the concrete solution map. -/
theorem kineticFlow_endpoint_continuous (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    Continuous (fun p : (E × E) × VelocityForcing (E := E) T ↦
      kineticFlow g L γ u hg T hT p.1 p.2 t) :=
  (kineticFlow_endpoint_lipschitz g L γ u hg T hT t ht).continuous

/-- The entire constructed kinetic path, restricted to the compact horizon. -/
def kineticFlowPath (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (p : (E × E) × VelocityForcing (E := E) T) :
    C(Icc (0 : ℝ) T, E × E) :=
  ⟨fun t ↦ kineticFlow g L γ u hg T hT p.1 p.2 t,
    (kineticFlow_spec g L γ u hg T hT p.1 p.2).1.comp continuous_subtype_val⟩

/-- The actual solution is jointly continuous as an entire compact path,
not merely separately continuous at a fixed endpoint. -/
theorem kineticFlowPath_lipschitz (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) :
    LipschitzWith ⟨3 * Real.exp (((γ + u * L + 1 : ℝ≥0) : ℝ) * T + T), by positivity⟩
      (kineticFlowPath g L γ u hg T hT) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [dist_eq_norm]
  change ‖kineticFlowPath g L γ u hg T hT p - kineticFlowPath g L γ u hg T hT q‖ ≤
    (3 * Real.exp (((γ + u * L + 1 : ℝ≥0) : ℝ) * T + T)) * ‖p-q‖
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  change ‖kineticFlow g L γ u hg T hT p.1 p.2 t -
    kineticFlow g L γ u hg T hT q.1 q.2 t‖ ≤ _
  have he := (kineticFlow_endpoint_lipschitz g L γ u hg T hT t t.2).norm_sub_le p q
  have hexp : Real.exp (((γ + u * L + 1 : ℝ≥0) : ℝ) * (t : ℝ) + t) ≤
      Real.exp (((γ + u * L + 1 : ℝ≥0) : ℝ) * T + T) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left t.2.2 (NNReal.coe_nonneg (γ + u * L + 1))
    linarith [t.2.2]
  have hmul := mul_le_mul_of_nonneg_right hexp (norm_nonneg (p-q))
  change _ ≤ (3 * Real.exp (((γ + u * L + 1 : ℝ≥0) : ℝ) * (t : ℝ) + t)) * ‖p-q‖ at he
  nlinarith

theorem kineticFlowPath_continuous (g : E → E) (L γ u : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) : Continuous (kineticFlowPath g L γ u hg T hT) :=
  (kineticFlowPath_lipschitz g L γ u hg T hT).continuous

end KineticLangevin
