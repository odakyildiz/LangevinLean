import KineticLangevin.CoupledSegments
import KineticLangevin.IntegralCoupling
import UnadjustedLangevin.LpDrift

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology
namespace KineticLangevin
variable {Ω Ξ H : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {P : Measure Ω} {Q : Measure Ξ} [IsFiniteMeasure P] [IsFiniteMeasure Q]
  (φ : Ξ → Ω) (hφ : MeasurePreserving φ Q P)

/-- The actual source change is a continuous linear pullback on L². -/
def sourcePullback : Lp H 2 P →L[ℝ] Lp H 2 Q :=
  (Lp.compMeasurePreservingₗᵢ ℝ φ hφ).toContinuousLinearMap

/-- Pullback acts on the two physical phase coordinates separately. -/
def phasePullback : (Lp H 2 P × Lp H 2 P) →L[ℝ] (Lp H 2 Q × Lp H 2 Q) :=
  ((sourcePullback φ hφ).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((sourcePullback φ hφ).comp (ContinuousLinearMap.snd ℝ _ _))

/-- Pullback representatives are the actual compositions with the source map. -/
theorem sourcePullback_coe (X : Lp H 2 P) : sourcePullback φ hφ X =ᵐ[Q] fun ξ => X (φ ξ) :=
  Lp.coeFn_compMeasurePreserving X hφ

/-- The two-coordinate pullback has the corresponding pointwise phase representative. -/
theorem phasePullback_coe (S : Lp H 2 P × Lp H 2 P) :
    (fun ξ => ((phasePullback φ hφ S).1 ξ,(phasePullback φ hφ S).2 ξ)) =ᵐ[Q]
      fun ξ => (S.1 (φ ξ),S.2 (φ ξ)) := by
  filter_upwards [sourcePullback_coe φ hφ S.1,sourcePullback_coe φ hφ S.2] with ξ hv hx
  exact Prod.ext hv hx

/-- A genuine measure-preserving pullback preserves every output law. -/
theorem sourcePullback_map [MeasurableSpace H] [BorelSpace H] (X : Lp H 2 P) :
    Q.map (sourcePullback φ hφ X) = P.map X := by
  rw [Measure.map_congr (sourcePullback_coe φ hφ X)]
  change Q.map ((X : Ω → H) ∘ φ) = _
  rw [← Measure.map_map (Lp.stronglyMeasurable X).measurable hφ.measurable,hφ.map_eq]

/-- Composing actual source pullbacks agrees with pulling back along the composed projection. -/
theorem sourcePullback_comp {Ζ : Type*} [MeasurableSpace Ζ] {R : Measure Ζ} [IsFiniteMeasure R]
    (ψ : Ζ → Ξ) (hψ : MeasurePreserving ψ R Q) (X : Lp H 2 P) :
    sourcePullback ψ hψ (sourcePullback φ hφ X) = sourcePullback (φ ∘ ψ) (hφ.comp hψ) X := by
  apply Lp.ext
  have he := hψ.quasiMeasurePreserving.ae_eq_comp (sourcePullback_coe φ hφ X)
  filter_upwards [sourcePullback_coe ψ hψ (sourcePullback φ hφ X),
    sourcePullback_coe (φ ∘ ψ) (hφ.comp hψ) X,he] with ζ h1 h2 he
  exact h1.trans (he.trans h2.symm)

/-- Applying the actual vector field to random variables commutes with measure-preserving source changes. -/
theorem lpDrift_sourcePullback (g : H → H) (M : ℝ≥0) (hg : LipschitzWith M g) (X : Lp H 2 P) :
    ULA.lpDrift Q g hg (sourcePullback φ hφ X) = sourcePullback φ hφ (ULA.lpDrift P g hg X) := by
  apply Lp.ext
  have hsource := hφ.quasiMeasurePreserving.ae_eq_comp (ULA.lpDrift_coe P g hg X)
  filter_upwards [ULA.lpDrift_coe Q g hg (sourcePullback φ hφ X),
    Lp.coeFn_compMeasurePreserving X hφ,
    Lp.coeFn_compMeasurePreserving (ULA.lpDrift P g hg X) hφ,hsource]
    with ξ htarget hX hGX hsource
  change ULA.lpDrift Q g hg (sourcePullback φ hφ X) ξ = _ at htarget
  rw [htarget]
  change g (sourcePullback φ hφ X ξ) = _
  rw [show sourcePullback φ hφ X ξ = X (φ ξ) from hX]
  exact (show (sourcePullback φ hφ (ULA.lpDrift P g hg X)) ξ = g (X (φ ξ)) from hGX.trans hsource).symm

/-- The physical kinetic drift commutes with the same source pullback. -/
theorem kineticDrift_phasePullback (g : H → H) (M : ℝ≥0) (hg : LipschitzWith M g)
    (γ u : ℝ) (S : Lp H 2 P × Lp H 2 P) :
    kineticNegativeDrift (ULA.lpDrift Q g hg) γ u (phasePullback φ hφ S) =
      phasePullback φ hφ (kineticNegativeDrift (ULA.lpDrift P g hg) γ u S) := by
  apply Prod.ext
  · change γ • sourcePullback φ hφ S.1 + u • ULA.lpDrift Q g hg (sourcePullback φ hφ S.2) =
      sourcePullback φ hφ (γ • S.1+u • ULA.lpDrift P g hg S.2)
    rw [map_add,map_smul,map_smul,lpDrift_sourcePullback φ hφ]
  · change -(sourcePullback φ hφ S.1) = sourcePullback φ hφ (-S.1)
    exact (map_neg _ _).symm

/-- Pulling back a genuine integral solution gives the genuine kinetic equation on the new source. -/
theorem kinetic_integral_sourcePullback (g : H → H) (M γ u : ℝ≥0) (hg : LipschitzWith M g)
    (Y : ℝ → Lp H 2 P × Lp H 2 P) (B : ℝ → Lp H 2 P) (hY : Continuous Y) (T : ℝ)
    (heq : ∀ t ∈ Icc 0 T, Y t-Y 0 =
      -(∫ s in 0..t,kineticNegativeDrift (ULA.lpDrift P g hg) γ u (Y s))+(B t,0))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    phasePullback φ hφ (Y t)-phasePullback φ hφ (Y 0) =
      -(∫ s in 0..t,kineticNegativeDrift (ULA.lpDrift Q g hg) γ u (phasePullback φ hφ (Y s)))+
        (sourcePullback φ hφ (B t),0) := by
  have hc : Continuous (fun s => kineticNegativeDrift (ULA.lpDrift P g hg) γ u (Y s)) :=
    (kineticNegativeDrift_lipschitz (ULA.lpDrift P g hg) M γ u (ULA.lpDrift_lipschitz P g hg)).continuous.comp hY
  have he := congrArg (phasePullback φ hφ) (heq t ht)
  rw [map_sub,map_add,map_neg,← (phasePullback φ hφ).intervalIntegral_comp_comm (hc.intervalIntegrable _ _)] at he
  simp_rw [← kineticDrift_phasePullback φ hφ g M hg γ u] at he
  have hn : phasePullback φ hφ (B t,0)=(sourcePullback φ hφ (B t),0) := by
    change (sourcePullback φ hφ (B t),sourcePullback φ hφ 0)=_
    rw [map_zero]
  rwa [hn] at he

/-- The actual selected kinetic integral flow commutes with a measure-preserving change of probability source. -/
theorem kineticSegmentFlow_sourcePullback (g : H → H) (M γ u : ℝ≥0) (hg : LipschitzWith M g)
    (T : ℝ) (hT : 0 ≤ T) (initial : Lp H 2 P × Lp H 2 P)
    (B : ℝ → Lp H 2 P) (hB : Continuous B) (hB0 : B 0=0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    kineticSegmentFlow (ULA.lpDrift Q g hg) M γ u (ULA.lpDrift_lipschitz Q g hg) T hT
      (phasePullback φ hφ initial) (fun s => sourcePullback φ hφ (B s)) ((sourcePullback φ hφ).continuous.comp hB) t =
      phasePullback φ hφ
        (kineticSegmentFlow (ULA.lpDrift P g hg) M γ u (ULA.lpDrift_lipschitz P g hg) T hT initial B hB t) := by
  let Y := kineticSegmentFlow (ULA.lpDrift P g hg) M γ u (ULA.lpDrift_lipschitz P g hg) T hT initial B hB
  let Z := kineticSegmentFlow (ULA.lpDrift Q g hg) M γ u (ULA.lpDrift_lipschitz Q g hg) T hT
    (phasePullback φ hφ initial) (fun s => sourcePullback φ hφ (B s)) ((sourcePullback φ hφ).continuous.comp hB)
  have hsY := kineticSegmentFlow_spec (ULA.lpDrift P g hg) M γ u (ULA.lpDrift_lipschitz P g hg)
    T hT initial B hB hB0
  have hB0' : sourcePullback φ hφ (B 0)=0 := by rw [hB0,map_zero]
  have hsZ := kineticSegmentFlow_spec (ULA.lpDrift Q g hg) M γ u (ULA.lpDrift_lipschitz Q g hg)
    T hT (phasePullback φ hφ initial) (fun s => sourcePullback φ hφ (B s))
    ((sourcePullback φ hφ).continuous.comp hB) hB0'
  have hc : Continuous (fun s => kineticNegativeDrift (ULA.lpDrift P g hg) γ u (Y s)) :=
    (kineticNegativeDrift_lipschitz (ULA.lpDrift P g hg) M γ u (ULA.lpDrift_lipschitz P g hg)).continuous.comp hsY.1
  have heZ : ∀ s ∈ Icc 0 T, Z s-Z 0 =
      -(∫ r in 0..s, kineticNegativeDrift (ULA.lpDrift Q g hg) γ u (Z r)) + (sourcePullback φ hφ (B s),0) := by
    intro s hs
    simpa only [Z,hsZ.2.1] using hsZ.2.2 s hs
  have heY : ∀ s ∈ Icc 0 T, phasePullback φ hφ (Y s)-phasePullback φ hφ (Y 0) =
      -(∫ r in 0..s, kineticNegativeDrift (ULA.lpDrift Q g hg) γ u (phasePullback φ hφ (Y r))) +
        (sourcePullback φ hφ (B s),0) := by
    intro s hs
    have he := congrArg (phasePullback φ hφ) (hsY.2.2 s hs)
    rw [map_sub,map_add,map_neg,← (phasePullback φ hφ).intervalIntegral_comp_comm (hc.intervalIntegrable _ _)] at he
    simp_rw [← kineticDrift_phasePullback φ hφ g M hg γ u] at he
    change phasePullback φ hφ (Y s)-phasePullback φ hφ initial = _ at he
    have hnoise : phasePullback φ hφ (B s,0) = (sourcePullback φ hφ (B s),0) := by
      change (sourcePullback φ hφ (B s),sourcePullback φ hφ 0) = _
      rw [map_zero]
    rw [hnoise] at he
    have hY0 : Y 0=initial := hsY.2.1
    rw [hY0]
    exact he
  have hstart : Z 0=phasePullback φ hφ (Y 0) := by
    have hy0 : Y 0=initial := hsY.2.1
    have hz0 : Z 0=phasePullback φ hφ initial := hsZ.2.1
    rw [hy0,hz0]
  exact integral_solution_unique (kineticNegativeDrift (ULA.lpDrift Q g hg) γ u) (γ+u*M+1)
    (kineticNegativeDrift_lipschitz (ULA.lpDrift Q g hg) M γ u (ULA.lpDrift_lipschitz Q g hg))
    Z (fun s => phasePullback φ hφ (Y s)) (fun s => (sourcePullback φ hφ (B s),0))
    hsZ.1 ((phasePullback φ hφ).continuous.comp hsY.1) T heZ heY hstart t ht

end KineticLangevin
