import KineticLangevin.FlowPullback
import KineticLangevin.LpGeneralContraction
import KineticLangevin.ProductLaw
import UnadjustedLangevin.TransportMoments
import UnadjustedLangevin.InitialCoupling

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin.ProductContinuous
variable {S H : Type*} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  (Q : Measure S) [IsProbabilityMeasure Q]

/-- The independent initial position and actual common velocity/noise source. -/
abbrev probability (μ : Measure H) := μ.prod Q

/-- The actual initial phase on the independent source. -/
def initial (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ) (V : Lp H 2 Q) :
    Lp H 2 (probability Q μ) × Lp H 2 (probability Q μ) :=
  (sourcePullback (Prod.snd : H×S → S) measurePreserving_snd V,
   (hμ.comp_measurePreserving measurePreserving_fst).toLp Prod.fst)

/-- Pull the genuine continuous additive noise onto the independent position/noise product. -/
def input (μ : Measure H) [IsProbabilityMeasure μ] (B : ℝ → Lp H 2 Q) (t : ℝ) : Lp H 2 (probability Q μ) :=
  sourcePullback (Prod.snd : H×S → S) measurePreserving_snd (B t)

/-- The actual selected kinetic diffusion on the independent initial-state/noise source. -/
def flow (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ)
    (V : Lp H 2 Q) (B : ℝ → Lp H 2 Q) (hB : Continuous B)
    (g : H → H) (M γ : ℝ≥0) (hg : LipschitzWith M g) (T : ℝ) (hT : 0 ≤ T) :
    ℝ → Lp H 2 (probability Q μ) × Lp H 2 (probability Q μ) :=
  kineticSegmentFlow (ULA.lpDrift (probability Q μ) g hg) M γ 1 (ULA.lpDrift_lipschitz _ _ hg)
    T hT (initial Q μ hμ V) (input Q μ B)
    ((sourcePullback (Prod.snd : H×S → S) measurePreserving_snd).continuous.comp hB)

/-- The continuous position law is the actual pushforward of the selected Brownian-driven L² solution. -/
def positionLaw (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ)
    (V : Lp H 2 Q) (B : ℝ → Lp H 2 Q) (hB : Continuous B)
    (g : H → H) (M γ : ℝ≥0) (hg : LipschitzWith M g) (T : ℝ) (hT : 0 ≤ T) : Measure H :=
  (probability Q μ).map (flow Q μ hμ V B hB g M γ hg T hT T).2

theorem flow_spec (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ)
    (V : Lp H 2 Q) (B : ℝ → Lp H 2 Q) (hB : Continuous B) (hB0 : B 0=0)
    (g : H → H) (M γ : ℝ≥0) (hg : LipschitzWith M g) (T : ℝ) (hT : 0 ≤ T) :
    Continuous (flow Q μ hμ V B hB g M γ hg T hT) ∧
      flow Q μ hμ V B hB g M γ hg T hT 0 = initial Q μ hμ V ∧
      ∀ t ∈ Icc 0 T, flow Q μ hμ V B hB g M γ hg T hT t - flow Q μ hμ V B hB g M γ hg T hT 0 =
        -(∫ s in 0..t,kineticNegativeDrift (ULA.lpDrift (probability Q μ) g hg) γ 1
          (flow Q μ hμ V B hB g M γ hg T hT s))+(input Q μ B t,0) := by
  have hb0 : input Q μ B 0=0 := by unfold input;rw [hB0,map_zero]
  have hs := kineticSegmentFlow_spec (ULA.lpDrift (probability Q μ) g hg) M γ 1 (ULA.lpDrift_lipschitz _ _ hg)
    T hT (initial Q μ hμ V) (input Q μ B)
    ((sourcePullback (Prod.snd : H×S → S) measurePreserving_snd).continuous.comp hB) hb0
  refine ⟨hs.1,hs.2.1,?_⟩
  intro t ht
  simpa only [flow,hs.2.1,NNReal.coe_one] using hs.2.2 t ht

/-- The actual continuous position output is a probability measure. -/
theorem positionLaw_probability (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ)
    (V : Lp H 2 Q) (B : ℝ → Lp H 2 Q) (hB : Continuous B)
    (g : H → H) (M γ : ℝ≥0) (hg : LipschitzWith M g) (T : ℝ) (hT : 0 ≤ T) :
    IsProbabilityMeasure (positionLaw Q μ hμ V B hB g M γ hg T hT) := by
  exact (Measure.isProbabilityMeasure_map_iff (Lp.aestronglyMeasurable _).aemeasurable).mpr inferInstance

/-- The actual continuous solution has a finite second moment as an L² random vector. -/
theorem positionLaw_memLp (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ)
    (V : Lp H 2 Q) (B : ℝ → Lp H 2 Q) (hB : Continuous B)
    (g : H → H) (M γ : ℝ≥0) (hg : LipschitzWith M g) (T : ℝ) (hT : 0 ≤ T) :
    MemLp (id : H → H) 2 (positionLaw Q μ hμ V B hB g M γ hg T hT) := by
  exact (memLp_map_measure_iff (by fun_prop) (Lp.aestronglyMeasurable _).aemeasurable).mpr (Lp.memLp _)

section Coupling
variable {μ ν : Measure H} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
local instance coupling_probability (c : ULA.Coupling μ ν) : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
local instance extension_probability (c : ULA.Coupling μ ν) : IsProbabilityMeasure (ULA.initialExtension c Q) :=
  ULA.initialExtension_isProbabilityMeasure c Q

def leftProjection (p : (H×H)×S) : H×S := (p.1.1,p.2)
def rightProjection (p : (H×H)×S) : H×S := (p.1.2,p.2)

theorem leftProjection_preserving (c : ULA.Coupling μ ν) :
    MeasurePreserving (leftProjection (H := H) (S := S)) (ULA.initialExtension c Q) (probability Q μ) :=
  ⟨measurable_fst.fst.prodMk measurable_snd,ULA.initialExtension_initial_noise c Q⟩

theorem rightProjection_preserving (c : ULA.Coupling μ ν) :
    MeasurePreserving (rightProjection (H := H) (S := S)) (ULA.initialExtension c Q) (probability Q ν) := by
  refine ⟨measurable_fst.snd.prodMk measurable_snd,?_⟩
  change (c.joint.prod Q).map (Prod.map Prod.snd id) = _
  simpa only [c.snd,Measure.map_id] using (Measure.map_prod_map c.joint Q measurable_snd measurable_id).symm

/-- Both actual position marginals pull the same source variable back to precisely the same L² variable. -/
theorem common_source_pullback (c : ULA.Coupling μ ν) (Z : Lp H 2 Q) :
    sourcePullback leftProjection (leftProjection_preserving Q c)
      (sourcePullback (Prod.snd : H×S → S) measurePreserving_snd Z) =
      sourcePullback (Prod.snd : (H×H)×S → S) measurePreserving_snd Z ∧
    sourcePullback rightProjection (rightProjection_preserving Q c)
      (sourcePullback (Prod.snd : H×S → S) measurePreserving_snd Z) =
      sourcePullback (Prod.snd : (H×H)×S → S) measurePreserving_snd Z := by
  constructor <;> rw [sourcePullback_comp] <;> rfl

/-- The initial phase representatives are the common velocity and their original position coordinate. -/
theorem initial_coe (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ) (V : Lp H 2 Q) :
    (fun p => lpPhaseCoe (probability Q μ) (initial Q μ hμ V) p) =ᵐ[probability Q μ] fun p : H×S => (V p.2,p.1) := by
  filter_upwards [sourcePullback_coe (Prod.snd : H×S → S) (measurePreserving_snd : MeasurePreserving Prod.snd (probability Q μ) Q) V,
    (hμ.comp_measurePreserving (measurePreserving_fst : MeasurePreserving Prod.fst (probability Q μ) μ)).coeFn_toLp]
    with p hv hx
  exact Prod.ext hv hx

/-- The actual arbitrary-shift mixing bound for one supplied initial coupling. -/
theorem positionLaw_bound_of_coupling (c : ULA.Coupling μ ν)
    (hμ : MemLp (id : H → H) 2 μ) (hν : MemLp (id : H → H) 2 ν)
    (V : Lp H 2 Q) (B : ℝ → Lp H 2 Q) (hB : Continuous B) (hB0 : B 0=0)
    (f : H → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hmM : m ≤ (M : ℝ)) (hd : 0 < (γ : ℝ)-2*a) (T : ℝ) (hT : 0 ≤ T) :
    ULA.wasserstein2Real (positionLaw Q μ hμ V B hB (gradient f) M γ hLip T hT)
      (positionLaw Q ν hν V B hB (gradient f) M γ hLip T hT) ≤
      (Real.sqrt (2*(((γ : ℝ)-a)^2+a^2))/((γ : ℝ)-2*a) *
        Real.exp (max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2)/((γ : ℝ)-2*a)*T)) * (ULA.couplingCost c.joint).toReal := by
  let P := ULA.initialExtension c Q
  let Y := flow Q μ hμ V B hB (gradient f) M γ hLip T hT
  let Z := flow Q ν hν V B hB (gradient f) M γ hLip T hT
  let L := phasePullback (H := H) leftProjection (leftProjection_preserving Q c)
  let R := phasePullback (H := H) rightProjection (rightProjection_preserving Q c)
  let A := fun t => L (Y t)
  let C := fun t => R (Z t)
  let W : ℝ → Lp H 2 P × Lp H 2 P := fun t => (sourcePullback (Prod.snd : (H×H)×S → S)
    (measurePreserving_snd : MeasurePreserving Prod.snd P Q) (B t),(0 : Lp H 2 P))
  have hY := flow_spec Q μ hμ V B hB hB0 (gradient f) M γ hLip T hT
  have hZ := flow_spec Q ν hν V B hB hB0 (gradient f) M γ hLip T hT
  have hA : Continuous A := L.continuous.comp hY.1
  have hC : Continuous C := R.continuous.comp hZ.1
  have heA : ∀ t ∈ Icc 0 T,A t-A 0 =
      -(∫ s in 0..t,kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (A s))+W t := by
    intro t ht
    have he := kinetic_integral_sourcePullback leftProjection (leftProjection_preserving Q c)
      (gradient f) M γ 1 hLip Y (input Q μ B) hY.1 T (by simpa only [NNReal.coe_one] using hY.2.2) t ht
    simpa only [input,(common_source_pullback Q c (B t)).1,NNReal.coe_one] using he
  have heC : ∀ t ∈ Icc 0 T,C t-C 0 =
      -(∫ s in 0..t,kineticNegativeDrift (ULA.lpDrift P (gradient f) hLip) γ 1 (C s))+W t := by
    intro t ht
    have he := kinetic_integral_sourcePullback rightProjection (rightProjection_preserving Q c)
      (gradient f) M γ 1 hLip Z (input Q ν B) hZ.1 T (by simpa only [NNReal.coe_one] using hZ.2.2) t ht
    simpa only [input,(common_source_pullback Q c (B t)).2,NNReal.coe_one] using he
  have hvelocity : (A 0).1=(C 0).1 := by
    change sourcePullback leftProjection (leftProjection_preserving Q c) (Y 0).1 =
      sourcePullback rightProjection (rightProjection_preserving Q c) (Z 0).1
    have hy0 : Y 0=initial Q μ hμ V := hY.2.1
    have hz0 : Z 0=initial Q ν hν V := hZ.2.1
    rw [hy0,hz0]
    exact (common_source_pullback Q c V).1.trans (common_source_pullback Q c V).2.symm
  have hcost : ‖(A 0).2-(C 0).2‖=(ULA.couplingCost c.joint).toReal := by
    have hleft := (leftProjection_preserving Q c).quasiMeasurePreserving.ae_eq_comp (initial_coe Q μ hμ V)
    have hright := (rightProjection_preserving Q c).quasiMeasurePreserving.ae_eq_comp (initial_coe Q ν hν V)
    have hcL := phasePullback_coe leftProjection (leftProjection_preserving Q c) (initial Q μ hμ V)
    have hcR := phasePullback_coe rightProjection (rightProjection_preserving Q c) (initial Q ν hν V)
    have he : ((A 0).2-(C 0).2 : Lp H 2 P) =ᵐ[P] fun p : (H×H)×S => p.1.1-p.1.2 := by
      filter_upwards [Lp.coeFn_sub (A 0).2 (C 0).2,hleft,hright,hcL,hcR] with p hsub hl hr hcl hcr
      rw [hsub,Pi.sub_apply]
      have hv0 : A 0=L (initial Q μ hμ V) := congrArg L hY.2.1
      have hz0 : C 0=R (initial Q ν hν V) := congrArg R hZ.2.1
      rw [hv0,hz0]
      have hl' := congrArg (Prod.snd : H×H → H) hl
      have hr' := congrArg (Prod.snd : H×H → H) hr
      have hcl' := congrArg (Prod.snd : H×H → H) hcl
      have hcr' := congrArg (Prod.snd : H×H → H) hcr
      exact congrArg₂ (fun x y : H => x-y) (hcl'.trans hl') (hcr'.trans hr')
    rw [Lp.norm_def,eLpNorm_congr_ae he,ULA.initialExtension_cost c Q]
  have hdec := lp_kinetic_integral_position_decay_general P f m a M γ hf hsc hLip hmM hd
    A C W hA hC T heA heC hvelocity T ⟨hT,le_rfl⟩
  rw [hcost] at hdec
  have hALaw : P.map (A T).2 = positionLaw Q μ hμ V B hB (gradient f) M γ hLip T hT :=
    sourcePullback_map leftProjection (leftProjection_preserving Q c) (Y T).2
  have hCLaw : P.map (C T).2 = positionLaw Q ν hν V B hB (gradient f) M γ hLip T hT :=
    sourcePullback_map rightProjection (rightProjection_preserving Q c) (Z T).2
  have hw := ULA.wasserstein2_le_Lp_cost_real P (A T).2 (C T).2
  rw [hALaw,hCLaw] at hw
  exact hw.trans hdec

/-- The full arbitrary-shift continuous mixing estimate with the genuine initial position Wasserstein distance. -/
theorem positionLaw_wasserstein2_general
    (hμ : MemLp (id : H → H) 2 μ) (hν : MemLp (id : H → H) 2 ν)
    (V : Lp H 2 Q) (B : ℝ → Lp H 2 Q) (hB : Continuous B) (hB0 : B 0=0)
    (f : H → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith M (gradient f))
    (hmM : m ≤ (M : ℝ)) (hd : 0 < (γ : ℝ)-2*a) (T : ℝ) (hT : 0 ≤ T) :
    ULA.wasserstein2Real (positionLaw Q μ hμ V B hB (gradient f) M γ hLip T hT)
      (positionLaw Q ν hν V B hB (gradient f) M γ hLip T hT) ≤
      (Real.sqrt (2*(((γ : ℝ)-a)^2+a^2))/((γ : ℝ)-2*a) *
        Real.exp (max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2)/((γ : ℝ)-2*a)*T)) * ULA.wasserstein2Real μ ν := by
  let Lμ := positionLaw Q μ hμ V B hB (gradient f) M γ hLip T hT
  let Lν := positionLaw Q ν hν V B hB (gradient f) M γ hLip T hT
  haveI : IsProbabilityMeasure Lμ := positionLaw_probability Q μ hμ V B hB (gradient f) M γ hLip T hT
  haveI : IsProbabilityMeasure Lν := positionLaw_probability Q ν hν V B hB (gradient f) M γ hLip T hT
  have hfinite : ULA.wasserstein2 μ ν ≠ ⊤ := ULA.wasserstein2_ne_top_of_memLp μ ν hμ hν
  have houtfinite : ULA.wasserstein2 Lμ Lν ≠ ⊤ := ULA.wasserstein2_ne_top_of_memLp Lμ Lν
    (positionLaw_memLp Q μ hμ V B hB (gradient f) M γ hLip T hT)
    (positionLaw_memLp Q ν hν V B hB (gradient f) M γ hLip T hT)
  let q : ℝ≥0 := ⟨Real.sqrt (2*(((γ : ℝ)-a)^2+a^2))/((γ : ℝ)-2*a) *
    Real.exp (max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2)/((γ : ℝ)-2*a)*T),by positivity⟩
  have hq : (q : ℝ) = Real.sqrt (2*(((γ : ℝ)-a)^2+a^2))/((γ : ℝ)-2*a) *
      Real.exp (max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2)/((γ : ℝ)-2*a)*T) := rfl
  have hb := ULA.wasserstein2_affine_bound_real_of_finite_couplings μ ν Lμ Lν q 0 hfinite houtfinite
    (fun c hc => by simpa only [Lμ,Lν,hq,NNReal.coe_zero,add_zero] using
      positionLaw_bound_of_coupling Q c hμ hν V B hB hB0 f m a M γ hf hsc hLip hmM hd T hT)
  simpa only [Lμ,Lν,hq,NNReal.coe_zero,add_zero] using hb

end Coupling
end KineticLangevin.ProductContinuous
