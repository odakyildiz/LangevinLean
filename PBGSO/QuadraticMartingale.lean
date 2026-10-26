import PBGSO.AdditiveJointBridge
import Mathlib.Probability.Martingale.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Quadratic expected energy from martingale increment structure

The energy derivative is a conclusion, not a process assumption. The
stochastic input is a martingale with its weighted increment isometry.
Construction of the multiplicative stochastic integral is separate.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
open Filter Set MeasureTheory
open scoped Topology NNReal ENNReal BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.QuadraticMartingale

section Algebra
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem bilinear_increment (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (x y : H) :
    B y y - B x x = 2 * B x (y - x) + B (y - x) (y - x) := by
  simp only [map_sub, sub_apply]
  rw [hB y x]
  ring

/-- Exact forward quadratic expansion after martingale orthogonality
and the weighted increment isometry; no differential equation for the
quadratic energy is assumed. -/
theorem quadratic_increment_forward (B : H →L[ℝ] H →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (X A M : ℝ → H) (v : ℝ → ℝ)
    (s t : ℝ) (hs : X s = A s + M s) (ht : X t = A t + M t)
    (ho : B (X s) (M t - M s) = 0)
    (hv : B (M t - M s) (M t - M s) = v t - v s) :
    B (X t) (X t) - B (X s) (X s) =
      2 * B (X s) (A t - A s) + B (A t - A s) (A t - A s) +
        2 * B (A t - A s) (M t - M s) + (v t - v s) := by
  rw [bilinear_increment B hB]
  have hdiff : X t - X s = (A t - A s) + (M t - M s) := by rw [hs, ht]; abel
  rw [hdiff]
  simp only [map_add, add_apply, ho, add_zero]
  rw [hB (M t - M s) (A t - A s), hv]
  ring

/-- A differentiable finite-variation part plus a continuous martingale
part has the claimed quadratic derivative once martingale orthogonality
and increment isometry are supplied. Both one-sided expansions are proved,
so this gives the full derivative within nonnegative time. -/
theorem quadratic_hasDerivWithinAt
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (X A M : ℝ → H) (v : ℝ → ℝ)
    (hdecomp : ∀ r, 0 ≤ r → X r = A r + M r)
    (horth : ∀ s t, 0 ≤ s → s ≤ t → B (X s) (M t - M s) = 0)
    (hvar : ∀ s t, 0 ≤ s → s ≤ t →
      B (M t - M s) (M t - M s) = v t - v s)
    (t : ℝ) (ht : 0 ≤ t) (b : H) (a : ℝ)
    (hX : ContinuousWithinAt X (Ici 0) t)
    (hM : ContinuousWithinAt M (Ici 0) t)
    (hA : HasDerivWithinAt A b (Ici 0) t)
    (hv : HasDerivWithinAt v a (Ici 0) t) :
    HasDerivWithinAt (fun r => B (X r) (X r)) (2 * B (X t) b + a) (Ici 0) t := by
  let l := 𝓝[Ici 0 \ {t}] t
  have hsl : Tendsto (slope A t) l (𝓝 b) := hasDerivWithinAt_iff_tendsto_slope.mp hA
  have hsv : Tendsto (slope v t) l (𝓝 a) := hasDerivWithinAt_iff_tendsto_slope.mp hv
  have hlimX : Tendsto X l (𝓝 (X t)) := hX.mono_left (nhdsWithin_mono _ (show Ici (0 : ℝ) \ {t} ⊆ Ici 0 from sdiff_subset))
  have hlimA : Tendsto (fun r => A r - A t) l (𝓝 0) := by
    simpa only [sub_self] using
      (hA.continuousWithinAt.mono_left (nhdsWithin_mono _ (show Ici (0 : ℝ) \ {t} ⊆ Ici 0 from sdiff_subset))).sub (tendsto_const_nhds (x := A t))
  have hlimM : Tendsto (fun r => M r - M t) l (𝓝 0) := by
    simpa only [sub_self] using
      (hM.mono_left (nhdsWithin_mono _ (show Ici (0 : ℝ) \ {t} ⊆ Ici 0 from sdiff_subset))).sub (tendsto_const_nhds (x := M t))
  have hDA : Tendsto (fun r => B (slope A t r) (A r - A t)) l (𝓝 0) := by
    simpa only [Function.comp_def, Function.uncurry_def, map_zero] using
      (B.continuous₂.tendsto (b, 0)).comp (hsl.prodMk_nhds hlimA)
  have hDM : Tendsto (fun r => B (slope A t r) (M r - M t)) l (𝓝 0) := by
    simpa only [Function.comp_def, Function.uncurry_def, map_zero] using
      (B.continuous₂.tendsto (b, 0)).comp (hsl.prodMk_nhds hlimM)
  have hlead : Tendsto (fun r => B (X t) (slope A t r)) l (𝓝 (B (X t) b)) :=
    ((B (X t)).continuous.tendsto b).comp hsl
  have hlead' : Tendsto (fun r => B (X r) (slope A t r)) l (𝓝 (B (X t) b)) :=
    (B.continuous₂.tendsto (X t, b)).comp (hlimX.prodMk_nhds hsl)
  let plus : ℝ → ℝ := fun r => 2 * B (X t) (slope A t r) +
    B (slope A t r) (A r - A t) + 2 * B (slope A t r) (M r - M t) + slope v t r
  let minus : ℝ → ℝ := fun r => 2 * B (X r) (slope A t r) -
    B (slope A t r) (A r - A t) - 2 * B (slope A t r) (M r - M t) + slope v t r
  have hp : Tendsto plus l (𝓝 (2 * B (X t) b + a)) := by
    simpa only [plus, mul_zero, add_zero] using
      (((hlead.const_mul 2).add hDA).add (hDM.const_mul 2)).add hsv
  have hm : Tendsto minus l (𝓝 (2 * B (X t) b + a)) := by
    simpa only [minus, mul_zero, sub_zero] using
      (((hlead'.const_mul 2).sub hDA).sub (hDM.const_mul 2)).add hsv
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hpiece := hp.if' (p := fun r => r ∈ Ici t) hm
  apply hpiece.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : 0 ≤ r := hr.1
  have hrne : r ≠ t := by simpa only [mem_singleton_iff] using hr.2
  have hden : r - t ≠ 0 := sub_ne_zero.mpr hrne
  split_ifs with htr
  · have he := quadratic_increment_forward B hB X A M v t r (hdecomp t ht)
      (hdecomp r hr0) (horth t r ht htr) (hvar t r ht htr)
    dsimp [plus]
    simp only [slope, vsub_eq_sub, map_smul, smul_apply,
      smul_eq_mul]
    rw [he]
    ring
  · have hrt : r ≤ t := le_of_lt (lt_of_not_ge htr)
    have he := quadratic_increment_forward B hB X A M v r t (hdecomp r hr0)
      (hdecomp t ht) (horth r t hr0 hrt) (hvar r t hr0 hrt)
    have ha : A t - A r = -(A r - A t) := (neg_sub _ _).symm
    have hM' : M t - M r = -(M r - M t) := (neg_sub _ _).symm
    rw [ha, hM'] at he
    simp only [map_neg, neg_apply, neg_neg] at he
    dsimp [minus]
    simp only [slope, vsub_eq_sub, map_smul, smul_apply,
      smul_eq_mul]
    have he' : B (X r) (X r) - B (X t) (X t) =
        2 * B (X r) (A r - A t) - B (A r - A t) (A r - A t) -
        2 * B (A r - A t) (M r - M t) + (v r - v t) := by linarith
    rw [he']
    ring

/-- Actual Bochner drift and quadratic-variation integrals discharge the
auxiliary derivative premises in the increment theorem. -/
theorem quadratic_hasDerivWithinAt_of_integral [CompleteSpace H]
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (X drift M : ℝ → H) (a : ℝ → ℝ)
    (hX : Continuous X) (hM : Continuous M) (hb : Continuous drift) (ha : Continuous a)
    (heq : ∀ r, 0 ≤ r → X r = X 0 + (∫ u in (0 : ℝ)..r, drift u) + M r)
    (horth : ∀ s t, 0 ≤ s → s ≤ t → B (X s) (M t - M s) = 0)
    (hvar : ∀ s t, 0 ≤ s → s ≤ t →
      B (M t - M s) (M t - M s) = ∫ u in s..t, a u)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => B (X r) (X r))
      (2 * B (X t) (drift t) + a t) (Ici 0) t := by
  let A : ℝ → H := fun r => X 0 + ∫ u in (0 : ℝ)..r, drift u
  let v : ℝ → ℝ := fun r => ∫ u in (0 : ℝ)..r, a u
  have hA : HasDerivAt A (drift t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hb.intervalIntegrable _ _)
      (hb.stronglyMeasurableAtFilter _ _) hb.continuousAt).const_add _
  have hv : HasDerivAt v (a t) t :=
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
      (ha.stronglyMeasurableAtFilter _ _) ha.continuousAt
  apply quadratic_hasDerivWithinAt B hB X A M v heq horth _ t ht (drift t) (a t)
    hX.continuousWithinAt hM.continuousWithinAt hA.hasDerivWithinAt hv.hasDerivWithinAt
  intro s r hs hsr
  rw [hvar s r hs hsr]
  exact (intervalIntegral.integral_interval_sub_left (ha.intervalIntegrable 0 r)
    (ha.intervalIntegrable 0 s)).symm

end Algebra
section Martingale
variable {Ω Z : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z] [MeasurableSpace Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q] (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- The actual L² conditional expectation of martingale increments is zero.
The martingale can use any adapted representatives of the L² classes. -/
theorem martingale_condExpL2 (M : ℝ → Lp Z 2 Q) (m : ℝ → Ω → Z)
    (hm : Martingale m ℱ Q) (hrep : ∀ t, m t =ᵐ[Q] M t)
    (s t : ℝ) (hst : s ≤ t) :
    (condExpL2 Z ℝ (ℱ.le s) (M t) : Lp Z 2 Q) = M s := by
  apply Lp.ext
  have hCE : (condExpL2 Z ℝ (ℱ.le s) (M t) : Ω → Z) =ᵐ[Q]
      Q[(M t) | ℱ s] := by
    simpa only [Lp.toLp_coeFn] using
      (Lp.memLp (M t)).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le s)
  exact hCE.trans ((condExp_congr_ae (hrep t).symm).trans
    ((hm.condExp_ae_eq hst).trans (hrep s)))

/-- Weighted L² energy pairing is an actual bounded bilinear form. -/
def weightedPairing (W : Z →L[ℝ] Z) : Lp Z 2 Q →L[ℝ] Lp Z 2 Q →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ _) (W.compLpL 2 Q)

@[simp] theorem weightedPairing_apply (W : Z →L[ℝ] Z) (X Y : Lp Z 2 Q) :
    weightedPairing Q W X Y = ⟪X, W.compLpL 2 Q Y⟫_ℝ := rfl

theorem weightedPairing_left (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ) (X Y : Lp Z 2 Q) :
    weightedPairing Q W X Y = ⟪W.compLpL 2 Q X, Y⟫_ℝ := by
  rw [weightedPairing_apply, lp_weighted_pairing_eq_integral]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [W.coeFn_compLpL X] with ω hω
  rw [hω]
  exact hW _ _

theorem weightedPairing_symmetric (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ) (X Y : Lp Z 2 Q) :
    weightedPairing Q W X Y = weightedPairing Q W Y X := by
  rw [weightedPairing_left Q W hW, weightedPairing_apply, real_inner_comm]

/-- Martingale conditional expectations and adaptedness of the current
state imply the actual weighted increment orthogonality. -/
theorem martingale_weighted_increment_orthogonal
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (X M : ℝ → Lp Z 2 Q) (m : ℝ → Ω → Z)
    (hm : Martingale m ℱ Q) (hrep : ∀ t, m t =ᵐ[Q] M t)
    (hX : ∀ t, AEStronglyMeasurable[ℱ t] (X t) Q)
    (s t : ℝ) (hst : s ≤ t) :
    weightedPairing Q W (X s) (M t - M s) = 0 := by
  have hadapt : AEStronglyMeasurable[ℱ s] (W.compLpL 2 Q (X s)) Q := by
    apply (W.continuous.comp_aestronglyMeasurable (hX s)).congr
    exact (W.coeFn_compLpL (X s)).symm
  have hcond : (condExpL2 Z ℝ (ℱ.le s) (M t - M s) : Lp Z 2 Q) = 0 := by
    simp only [map_sub, Submodule.coe_sub]
    rw [martingale_condExpL2 Q ℱ M m hm hrep s t hst,
      martingale_condExpL2 Q ℱ M m hm hrep s s le_rfl, sub_self]
  have hinner := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (ℱ.le s)
    (M t - M s) (W.compLpL 2 Q (X s)) hadapt
  rw [hcond, inner_zero_left] at hinner
  rw [weightedPairing_left Q W hW, real_inner_comm, ← hinner]

/-- The actual residual after subtracting the Bochner drift integral. -/
def martingaleResidual (X drift : ℝ → Lp Z 2 Q) (t : ℝ) : Lp Z 2 Q :=
  X t - X 0 - ∫ r in (0 : ℝ)..t, drift r

theorem martingaleResidual_continuous (X drift : ℝ → Lp Z 2 Q)
    (hX : Continuous X) (hb : Continuous drift) :
    Continuous (martingaleResidual Q X drift) :=
  (hX.sub continuous_const).sub
    (intervalIntegral.differentiable_integral_of_continuous hb).continuous

theorem martingaleResidual_decomposition (X drift : ℝ → Lp Z 2 Q) (t : ℝ) :
    X t = X 0 + (∫ r in (0 : ℝ)..t, drift r) + martingaleResidual Q X drift t := by
  dsimp [martingaleResidual]
  abel

/-- Expected diffusion energy of the actual L² diffusion columns. The
columns can depend on the current state and on the full interacting state. -/
def diffusionEnergy {I : Type*} [Fintype I] (W : Z →L[ℝ] Z)
    (σ : ℝ → I → Lp Z 2 Q) (t : ℝ) : ℝ :=
  ∑ i, weightedPairing Q W (σ t i) (σ t i)

theorem diffusionEnergy_continuous {I : Type*} [Fintype I] (W : Z →L[ℝ] Z)
    (σ : ℝ → I → Lp Z 2 Q) (hσ : ∀ i, Continuous (fun t => σ t i)) :
    Continuous (diffusionEnergy Q W σ) := by
  apply continuous_finsetSum
  intro i _
  exact (weightedPairing Q W).continuous₂.comp₂ (hσ i) (hσ i)

/-- An expected quadratic forward identity derived from primitive
martingale and increment-isometry structure of the actual drift residual.
The stochastic integral is not constructed by this theorem: its standard
weighted L² isometry remains explicit. No quadratic energy derivative or
generator equation is assumed. -/
theorem expected_energy_hasDerivWithinAt {I : Type*} [Fintype I]
    (W : Z →L[ℝ] Z) (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (X drift : ℝ → Lp Z 2 Q) (σ : ℝ → I → Lp Z 2 Q)
    (hX : Continuous X) (hb : Continuous drift)
    (hσ : ∀ i, Continuous (fun t => σ t i))
    (m : ℝ → Ω → Z) (hm : Martingale m ℱ Q)
    (hrep : ∀ t, m t =ᵐ[Q] martingaleResidual Q X drift t)
    (hAdapt : ∀ t, AEStronglyMeasurable[ℱ t] (X t) Q)
    (hIsometry : ∀ s t, 0 ≤ s → s ≤ t →
      weightedPairing Q W (martingaleResidual Q X drift t - martingaleResidual Q X drift s)
        (martingaleResidual Q X drift t - martingaleResidual Q X drift s) =
          ∫ r in s..t, diffusionEnergy Q W σ r)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun r => ∫ ω, ⟪X r ω, W (X r ω)⟫_ℝ ∂Q)
      (2 * (∫ ω, ⟪X t ω, W (drift t ω)⟫_ℝ ∂Q) +
        ∑ i, ∫ ω, ⟪σ t i ω, W (σ t i ω)⟫_ℝ ∂Q) (Ici 0) t := by
  have h := quadratic_hasDerivWithinAt_of_integral
    (weightedPairing Q W) (weightedPairing_symmetric Q W hW)
    X drift (martingaleResidual Q X drift) (diffusionEnergy Q W σ)
    hX (martingaleResidual_continuous Q X drift hX hb) hb
    (diffusionEnergy_continuous Q W σ hσ)
    (fun r _ => martingaleResidual_decomposition Q X drift r)
    (fun s r _ hsr => martingale_weighted_increment_orthogonal Q ℱ W hW X
      (martingaleResidual Q X drift) m hm hrep hAdapt s r hsr)
    hIsometry t ht
  simpa only [weightedPairing_apply, lp_weighted_pairing_eq_integral, diffusionEnergy] using h

end Martingale
end PBGSO.QuadraticMartingale
