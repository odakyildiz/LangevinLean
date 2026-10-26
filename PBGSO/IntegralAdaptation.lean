import PBGSO.FilteredBrownianPullback
import PBGSO.ParticleProcess
import PBGSO.ParticleBrownianInput
import PBGSO.GlobalIntegral
import PBGSO.AdditiveWeakRealization
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # Adaptation derived from actual Lipschitz integral equations
Closed measurable L² subspaces are invariant under pointwise lifted drifts.
Restricting Picard to a fixed past subspace, then using actual common-input
uniqueness, proves the selected trajectory is measurable in that past. No
projection is assumed to commute with a nonlinear drift.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace PBGSO.IntegralAdaptation

section InvariantSubspace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual integral trajectories stay in any complete invariant linear
subspace containing their initial state and every input value in the past.
Existence is constructed inside that subspace and uniqueness identifies it
with the supplied trajectory; no nonlinear conditional-projection identity
is used. -/
theorem integral_mem_subspace
    (V : Submodule ℝ E) [CompleteSpace V]
    (f : E → E) (L : ℝ≥0) (hf : LipschitzWith L f)
    (hV : ∀ x ∈ V, f x ∈ V)
    (Y B : ℝ → E) (hY : Continuous Y) (hB : Continuous B) (hB0 : B 0 = 0)
    (heq : ∀ r, 0 ≤ r → Y r - Y 0 = (∫ u in 0..r, f (Y u)) + B r)
    (t : ℝ) (ht : 0 ≤ t) (hinit : Y 0 ∈ V)
    (hinput : ∀ r ∈ Icc 0 t, B r ∈ V) : Y t ∈ V := by
  let fV : V → V := fun x ↦ ⟨f x, hV x x.property⟩
  have hfV : LipschitzWith L fV := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact hf.dist_le_mul x y
  let clamp : ℝ → ℝ := fun r ↦ min (max 0 r) t
  have hc : Continuous clamp := (continuous_const.max continuous_id).min continuous_const
  have hclamp (r : ℝ) : clamp r ∈ Icc 0 t := by
    exact ⟨le_min (le_max_left _ _) ht, min_le_right _ _⟩
  let Bv : ℝ → V := fun r ↦ ⟨B (clamp r), hinput _ (hclamp r)⟩
  have hBv : Continuous Bv := (hB.comp hc).subtype_mk _
  have hBv0 : Bv 0 = 0 := by
    apply Subtype.ext
    change B (min (max 0 0) t) = 0
    simpa only [max_self, min_eq_left ht] using hB0
  obtain ⟨X, hX, hX0, hXe⟩ := exists_global_integral_solution fV L hfV ⟨Y 0, hinit⟩ Bv hBv hBv0
  let W : ℝ → E := fun r ↦ V.subtypeL (X r)
  have hW : Continuous W := V.subtypeL.continuous.comp hX
  have hW0 : W 0 = Y 0 := by simp only [W, hX0]; rfl
  have hWe : ∀ r ∈ Icc 0 t, W r - Y 0 = (∫ u in 0..r, f (W u)) + B r := by
    intro r hr
    have hi : IntervalIntegrable (fun u ↦ fV (X u)) volume 0 r :=
      (hfV.continuous.comp hX).intervalIntegrable 0 r
    have hh := congrArg V.subtypeL (hXe r hr.1)
    rw [map_sub, map_add, ← V.subtypeL.intervalIntegral_comp_comm hi] at hh
    change W r - Y 0 = (∫ u in 0..r, f (W u)) + B (clamp r) at hh
    simpa only [clamp, max_eq_right hr.1, min_eq_left hr.2] using hh
  have he := ULA.langevin_integral_unique (fun x ↦ -f x) L hf.neg (Y 0) B Y W hY hW t ht
    (fun r hr ↦ by simpa only [intervalIntegral.integral_neg, neg_neg] using heq r hr.1)
    (fun r hr ↦ by simpa only [intervalIntegral.integral_neg, neg_neg] using hWe r hr)
  rw [he ⟨ht, le_rfl⟩]
  exact (X t).property

end InvariantSubspace
end PBGSO.IntegralAdaptation

namespace PBGSO.IntegralAdaptation
section Preservation
variable {Ω E K : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- An actual pointwise lifted Lipschitz field preserves every measurable
L² subspace. This uses its proved representative identity. -/
theorem lpDrift_mem_lpMeas
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (U : Lp E 2 Q) (hU : U ∈ lpMeas E ℝ m 2 Q) :
    ULA.lpDrift Q g hg U ∈ lpMeas E ℝ m 2 Q := by
  apply (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mpr
  have h : AEStronglyMeasurable[m] U Q :=
    (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mp hU
  have hc : AEStronglyMeasurable[m] (fun ω ↦ g (U ω)) Q :=
    hg.continuous.comp_aestronglyMeasurable h
  exact hc.congr (ULA.lpDrift_coe Q g hg U).symm

/-- Primitive lifted maps preserve current-past measurability. -/
theorem liftMap_mem_lpMeas (f : E → K) (L : ℝ≥0) (hf : LipschitzWith L f)
    (U : Lp E 2 Q) (hU : U ∈ lpMeas E ℝ m 2 Q) :
    liftMap Q f hf U ∈ lpMeas K ℝ m 2 Q := by
  apply (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mpr
  have h : AEStronglyMeasurable[m] U Q :=
    (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mp hU
  have hc : AEStronglyMeasurable[m] (fun ω ↦ f (U ω)) Q :=
    hf.continuous.comp_aestronglyMeasurable h
  exact hc.congr (liftMap_coe Q f hf U).symm

end Preservation

section Lp
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The actual Lipschitz integral process is measurable in each current
past whenever its initial variable and additive input are. The supplied
trajectory need not have been constructed with an adaptedness premise. -/
theorem lifted_integral_aestronglyAdapted
    (g : E → E) (L : ℝ≥0) (hg : LipschitzWith L g)
    (F : Filtration ℝ≥0 mΩ) (Y B : ℝ → Lp E 2 Q)
    (hY : Continuous Y) (hB : Continuous B) (hB0 : B 0 = 0)
    (heq : ∀ r, 0 ≤ r → Y r - Y 0 =
      (∫ u in 0..r, ULA.lpDrift Q g hg (Y u)) + B r)
    (hinit : AEStronglyMeasurable[F 0] (Y 0) Q)
    (hinput : ∀ r : ℝ≥0, AEStronglyMeasurable[F r] (B r) Q)
    (t : ℝ≥0) : AEStronglyMeasurable[F t] (Y t) Q := by
  let V := lpMeas E ℝ (F t) 2 Q
  letI : Fact (F t ≤ mΩ) := ⟨F.le t⟩
  apply (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mp
  apply integral_mem_subspace V (ULA.lpDrift Q g hg) L (ULA.lpDrift_lipschitz Q g hg)
    (fun x hx ↦ lpDrift_mem_lpMeas (F t) Q g L hg x hx)
    Y B hY hB hB0 heq (t : ℝ) t.coe_nonneg
  · exact (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mpr
      (AEStronglyMeasurable.mono (F.mono (by positivity)) hinit)
  · intro r hr
    have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hr.2
    have hm := AEStronglyMeasurable.mono (F.mono hrt) (hinput r.toNNReal)
    exact (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mpr (by
      simpa only [Real.coe_toNNReal r hr.1] using hm)

/-- A strongly adapted representative is constructed from the proved
current-past measurability of an actual L² process. Its equality with the
original L² representative is asserted separately at each time. -/
def adaptedRepresentative (F : Filtration ℝ≥0 mΩ) (Y : ℝ≥0 → Lp E 2 Q)
    (hY : ∀ t, AEStronglyMeasurable[F t] (Y t) Q) (t : ℝ≥0) : Ω → E :=
  (hY t).mk (Y t)

theorem adaptedRepresentative_stronglyAdapted (F : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 → Lp E 2 Q) (hY : ∀ t, AEStronglyMeasurable[F t] (Y t) Q) :
    StronglyAdapted F (adaptedRepresentative Q F Y hY) :=
  fun t ↦ (hY t).stronglyMeasurable_mk

theorem adaptedRepresentative_ae (F : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 → Lp E 2 Q) (hY : ∀ t, AEStronglyMeasurable[F t] (Y t) Q) (t : ℝ≥0) :
    adaptedRepresentative Q F Y hY t =ᵐ[Q] Y t := (hY t).ae_eq_mk.symm

end Lp

section MeanField
variable {Ω A Z G : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The actual selected mean-field sampler trajectory is current-past
measurable, derived from its original equations and primitive Lipschitz data.
Its optimiser is deterministic; the entire nonlinear field is treated inside
an invariant product subspace rather than conditionally projected. -/
theorem meanField_aestronglyAdapted
    (L : LipschitzDynamics A Z G) (F : Filtration ℝ≥0 mΩ)
    (Y : ℝ → A × Lp Z 2 Q) (B : ℝ → Lp Z 2 Q)
    (HY : IsGlobalAdditiveIntegralSolution Q L Y B)
    (hB : Continuous B) (hB0 : B 0 = 0)
    (hinit : AEStronglyMeasurable[F 0] (Y 0).2 Q)
    (hinput : ∀ r : ℝ≥0, AEStronglyMeasurable[F r] (B r) Q)
    (t : ℝ≥0) : AEStronglyMeasurable[F t] (Y t).2 Q := by
  let V : Submodule ℝ (A × Lp Z 2 Q) :=
    (lpMeas Z ℝ (F t) 2 Q).comap (ContinuousLinearMap.snd ℝ A (Lp Z 2 Q)).toLinearMap
  have hc : IsClosed (V : Set (A × Lp Z 2 Q)) :=
    (isClosed_aestronglyMeasurable (F.le t)).preimage continuous_snd
  letI : CompleteSpace V := hc.completeSpace_coe
  have hinput' : Continuous (fun r ↦ ((0 : A), B r)) := continuous_const.prodMk hB
  have hB0' : ((0 : A), B 0) = 0 := by simp [hB0]
  have hfield : ∀ x ∈ V, L.field Q x ∈ V := by
    intro x hx
    exact liftMap_mem_lpMeas (F t) Q (L.sampler x.1) L.samplerLip (L.sampler_state x.1) x.2 hx
  have hmem : Y t ∈ V := integral_mem_subspace V (L.field Q) L.fieldLip
    (L.field_lipschitz Q) hfield Y (fun r ↦ (0, B r)) HY.continuous hinput' hB0'
    HY.equation t t.coe_nonneg
    ((mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mpr
      (AEStronglyMeasurable.mono (F.mono (by positivity)) hinit))
    (by
      intro r hr
      change B r ∈ lpMeas Z ℝ (F t) 2 Q
      have hrt : r.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hr.2
      have hm := AEStronglyMeasurable.mono (F.mono hrt) (hinput r.toNNReal)
      exact (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mpr (by
        simpa only [Real.coe_toNNReal r hr.1] using hm))
  change (Y t).2 ∈ lpMeas Z ℝ (F t) 2 Q at hmem
  exact (mem_lpMeas_iff_aestronglyMeasurable (𝕜 := ℝ)).mp hmem

end MeanField
end PBGSO.IntegralAdaptation


namespace PBGSO.IntegralAdaptation
section Brownian
variable {Ω E I : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The original constant-diffusion Brownian input is current-past
measurable for every actual filtered Brownian Driver. -/
theorem samplerBrownianInput_aestronglyMeasurable
    (D : FilteredBrownian.Driver (I := I) Q) (K : EuclideanSpace ℝ I →L[ℝ] E)
    (t : ℝ≥0) : AEStronglyMeasurable[D.filtration t]
      (samplerBrownianInput Q K D.process D.brownian 0 t) Q := by
  have hcoords (s : ℝ≥0) (hs : s ≤ t) :
      StronglyMeasurable[D.filtration t] (ULA.brownianCoordinates D.process s) := by
    have hm : @Measurable Ω (I → ℝ) (D.filtration t) inferInstance
        (fun ω i ↦ D.process i s ω) :=
      (@measurable_pi_iff Ω I (fun _ ↦ ℝ) (D.filtration t) (fun _ ↦ inferInstance)
        (fun ω i ↦ D.process i s ω)).mpr
        (fun i ↦ ((D.adapted i s).mono (D.filtration.mono hs)).measurable)
    exact (PiLp.continuous_toLp 2 (fun _ : I ↦ ℝ)).comp_stronglyMeasurable hm.stronglyMeasurable
  have hm : StronglyMeasurable[D.filtration t]
      (fun ω ↦ K (Real.sqrt 2 •
        (ULA.brownianCoordinates D.process t ω - ULA.brownianCoordinates D.process 0 ω))) :=
    K.continuous.comp_stronglyMeasurable
      (((hcoords t le_rfl).sub (hcoords 0 (by positivity))).const_smul (Real.sqrt 2))
  apply hm.aestronglyMeasurable.congr
  simpa only [zero_add, Real.toNNReal_coe, Real.toNNReal_zero] using
    (samplerBrownianInput_coe Q K D.process D.brownian 0 t).symm

/-- Any actual selected particle integral trajectory with primitive
Lipschitz maps is adapted up to its genuine L² representatives. -/
theorem particle_integral_aestronglyAdapted
    {A Z G : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : LipschitzDynamics A Z G) (N : ℕ) (hN : 0 < N)
    (F : Filtration ℝ≥0 mΩ) (Y B : ℝ → Lp (A × (Fin N → Z)) 2 Q)
    (hY : Continuous Y) (hB : Continuous B) (hB0 : B 0 = 0)
    (heq : ∀ r, 0 ≤ r → Y r - Y 0 =
      (∫ u in 0..r, ULA.lpDrift Q (L.particleField N)
        (L.particleField_lipschitz N hN) (Y u)) + B r)
    (hinit : AEStronglyMeasurable[F 0] (Y 0) Q)
    (hinput : ∀ r : ℝ≥0, AEStronglyMeasurable[F r] (B r) Q)
    (t : ℝ≥0) : AEStronglyMeasurable[F t] (Y t) Q :=
  lifted_integral_aestronglyAdapted Q (L.particleField N) L.fieldLip
    (L.particleField_lipschitz N hN) F Y B hY hB hB0 heq hinit hinput t

end Brownian
end PBGSO.IntegralAdaptation
