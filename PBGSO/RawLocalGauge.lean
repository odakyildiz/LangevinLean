import PBGSO.RawLocalIntegral

/-! # Actual local Itô noise is independent of the local-energy gauge
Two locally square-integrable raw diffusion fields equal on one event over
the entire horizon give identical actual glued noise. The proof compares
double-stopped computed integrals and exhausts both genuine stopping gauges.
No global expected diffusion-square moment or drift assumption is used.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators
namespace PBGSO.FilteredBrownian
variable {Ω I Z : Type*} [mΩ : MeasurableSpace Ω] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  {Q : Measure Ω} [IsProbabilityMeasure Q]
  {D : Driver (I := I) Q} {T : ℝ≥0}
  (L K : RawLocalDiffusion (Z := Z) Q D T)

private def doubleField (n m : ℕ) (i : I) : ℝ → Ω → Z :=
  LocalizedDiffusion.stoppedField (K.stop m) (L.stoppedSigma n i)

private theorem doubleField_strong (n m : ℕ) (i : I) :
    StronglyMeasurable (Function.uncurry (doubleField L K n m i)) :=
  LocalizedDiffusion.stoppedField_stronglyMeasurable (K.stop m) (K.stop_measurable m)
    (L.stoppedSigma n i) (L.stoppedSigma_strong n i)

private theorem doubleField_adapted (n m : ℕ) (t : ℝ≥0) (i : I) :
    AEStronglyMeasurable[D.filtration t] (doubleField L K n m i t) Q :=
  LocalizedDiffusion.stoppedField_adapted D.filtration (K.stop m) (K.stop_stopping m)
    (L.stoppedSigma n i) Q (fun t => L.stoppedSigma_adapted n t i) t

private theorem doubleField_square (n m : ℕ) (i : I) :
    Integrable (fun p : ℝ × Ω => ‖doubleField L K n m i p.1 p.2‖ ^ 2)
      ((volume.restrict (Ioc 0 (T : ℝ))).prod Q) := by
  apply (L.stoppedSigma_square n i).mono'
    (((doubleField_strong L K n m i).norm.pow 2).aestronglyMeasurable)
  exact Eventually.of_forall (fun p => by
    change ‖‖doubleField L K n m i p.1 p.2‖ ^ 2‖ ≤ ‖L.stoppedSigma n i p.1 p.2‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases h : p.1 ≤ (K.stop m p.2 : ℝ)
    · simp [doubleField,LocalizedDiffusion.stoppedField,h]
    · simp [doubleField,LocalizedDiffusion.stoppedField,h,sq_nonneg])

variable (hσ : ∀ᵐ ω ∂Q, ∀ i r, r ∈ Ioc 0 (T : ℝ) → L.sigma i r ω = K.sigma i r ω)
include hσ

private theorem doubleField_congr_ae (n m : ℕ) (i : I) :
    Function.uncurry (doubleField L K n m i) =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod Q]
      Function.uncurry (doubleField K L m n i) := by
  apply (Measure.ae_prod_iff_ae_ae
    ((doubleField_strong L K n m i).measurableSet_eq_fun
      (doubleField_strong K L m n i))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  filter_upwards [hσ] with ω hω
  by_cases hl : r ≤ (L.stop n ω : ℝ) <;> by_cases hk : r ≤ (K.stop m ω : ℝ) <;>
    simp [doubleField,RawLocalDiffusion.stoppedSigma,LocalizedDiffusion.stoppedField,hl,hk,hω i r hr]

/-- Each pair of actual stopped martingale versions agrees after stopping
at the other local gauge. All coefficient equalities are derived from raw
fields, and both completed stochastic integrals are actually constructed. -/
theorem RawLocalDiffusion.version_double_stopped_congr (n m : ℕ) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0,
      L.version n (min t (K.stop m ω)) ω = K.version m (min t (L.stop n ω)) ω := by
  obtain ⟨N,hNm,hNc,hN⟩ := rawDiffusionIntegral_exists_continuous_martingale Q D T
    (doubleField L K n m) (doubleField_strong L K n m) (doubleField_square L K n m)
    (doubleField_adapted L K n m)
  have heq (t : ℝ≥0) := rawDiffusionIntegral_congr_ae_coefficients Q D T
    (doubleField L K n m) (doubleField K L m n)
    (doubleField_strong L K n m) (doubleField_strong K L m n)
    (doubleField_square L K n m) (doubleField_square K L m n)
    (doubleField_adapted L K n m) (doubleField_adapted K L m n)
    (doubleField_congr_ae L K hσ n m) t
  have hN' (t : ℝ≥0) : N t =ᵐ[Q] rawDiffusionIntegral Q D T
      (doubleField K L m n) (doubleField_strong K L m n) (doubleField_square K L m n)
      (doubleField_adapted K L m n) t :=
    (hN t).trans (Eventually.of_forall (fun ω => congrArg (fun A : Lp Z 2 Q => A ω) (heq t)))
  have hL := rawDiffusionIntegral_stopped_version Q D T (K.stop m) (K.stop_bound m)
    (K.stop_stopping m) (L.stoppedSigma n) (doubleField L K n m)
    (L.stoppedSigma_strong n) (L.stoppedSigma_square n) (L.stoppedSigma_adapted n)
    (doubleField_strong L K n m) (doubleField_square L K n m) (doubleField_adapted L K n m)
    (fun _ _ _ => rfl) (L.version n) N (L.version_ae n) hN (L.version_continuous n) hNc
  have hK := rawDiffusionIntegral_stopped_version Q D T (L.stop n) (L.stop_bound n)
    (L.stop_stopping n) (K.stoppedSigma m) (doubleField K L m n)
    (K.stoppedSigma_strong m) (K.stoppedSigma_square m) (K.stoppedSigma_adapted m)
    (doubleField_strong K L m n) (doubleField_square K L m n) (doubleField_adapted K L m n)
    (fun _ _ _ => rfl) (K.version m) N (K.version_ae m) hN' (K.version_continuous m) hNc
  filter_upwards [hL,hK] with ω hl hk
  intro t
  exact (hl t).symm.trans (hk t)

/-- The actual local Brownian integral depends on the raw diffusion field,
not the chosen local-energy gauge. One AE event covers all horizon times.
Global expected square integrability is not an input. -/
theorem RawLocalDiffusion.localNoise_gauge_congr_on_horizon :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → L.localNoise t ω = K.localNoise t ω := by
  have hdouble : ∀ᵐ ω ∂Q, ∀ n m : ℕ, ∀ t : ℝ≥0,
      L.version n (min t (K.stop m ω)) ω = K.version m (min t (L.stop n ω)) ω :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun m => L.version_double_stopped_congr K hσ n m))
  filter_upwards [hdouble,L.localNoise_stopped,K.localNoise_stopped] with ω hω hl hk
  obtain ⟨n,hn⟩ := (L.stop_eventually_horizon ω).exists
  obtain ⟨m,hm⟩ := (K.stop_eventually_horizon ω).exists
  intro t ht
  have hd := hω n m t
  have hln := hl n t ht
  have hkm := hk m t ht
  simp only [hn,hm,min_eq_left ht] at hd hln hkm
  exact hln.symm.trans (hd.trans hkm)

/-- The corresponding deterministic-time identity for the original raw
local noise processes. -/
theorem RawLocalDiffusion.localNoise_gauge_congr_ae (t : ℝ≥0) (ht : t ≤ T) :
    L.localNoise t =ᵐ[Q] K.localNoise t :=
  (L.localNoise_gauge_congr_on_horizon K hσ).mono (fun _ h => h t ht)

omit hσ in
/-- Literal equality of raw coefficients is a direct special case. The
local integrability/stopping gauges may be completely different. -/
theorem RawLocalDiffusion.localNoise_gauge_congr_of_eq
    (he : ∀ i r ω, L.sigma i r ω = K.sigma i r ω) :
    ∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t ≤ T → L.localNoise t ω = K.localNoise t ω :=
  L.localNoise_gauge_congr_on_horizon K (Eventually.of_forall (fun ω i r _ => he i r ω))

end PBGSO.FilteredBrownian
