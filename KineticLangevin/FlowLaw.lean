import KineticLangevin.Flow
import KineticLangevin.SynchronousFlow
import UnadjustedLangevin.InitialExtension
import UnadjustedLangevin.InitialCoupling

/-! # Actual kinetic output laws and their Wasserstein contraction

The initial position and the velocity/continuous-forcing source are combined
by an explicit independent product. Every initial coupling is extended by the
same source. Its two output marginals and unchanged initial coupling cost are
proved, so output-law independence is derived rather than postulated.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace KineticLangevin

section RandomMaps
variable {H S : Type*} [NormedAddCommGroup H] [MeasurableSpace H]
  [BorelSpace H] [SecondCountableTopology H] [MeasurableSpace S]

/-- The actual output law of a measurable random map with independent input. -/
def randomMapLaw (F : H × S → H) (μ : Measure H) (Q : Measure S) : Measure H :=
  (μ.prod Q).map F

/-- The second output marginal on an arbitrary coupling extension. -/
theorem initialExtension_reference_map {μ ν : Measure H} [IsProbabilityMeasure μ]
    (c : ULA.Coupling μ ν) (Q : Measure S) [SFinite Q]
    (F : H × S → H) (hF : Measurable F) :
    (ULA.initialExtension c Q).map (fun p ↦ F (p.1.2,p.2)) = randomMapLaw F ν Q := by
  have := c.isProbabilityMeasure
  have hproj : (ULA.initialExtension c Q).map (fun p ↦ (p.1.2,p.2)) = ν.prod Q := by
    change (c.joint.prod Q).map (Prod.map Prod.snd id) = _
    simpa only [c.snd, Measure.map_id] using
      (Measure.map_prod_map c.joint Q measurable_snd measurable_id).symm
  rw [randomMapLaw, ← hproj, Measure.map_map hF
    (measurable_fst.snd.prodMk measurable_snd)]
  rfl

/-- A derived pathwise contraction transfers to the actual independent-product
laws and their genuine Wasserstein infimum, without an optimal-coupling axiom. -/
theorem randomMapLaw_wasserstein2_le (F : H × S → H) (hF : Measurable F)
    (q : ℝ≥0) (hcontract : ∀ x y s, ‖F (x,s) - F (y,s)‖ ≤ (q : ℝ) * ‖x-y‖)
    (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure S) [IsProbabilityMeasure Q] :
    ULA.wasserstein2 (randomMapLaw F μ Q) (randomMapLaw F ν Q) ≤
      (q : ℝ≥0∞) * ULA.wasserstein2 μ ν := by
  have hfamily (c : ULA.Coupling μ ν) :
      ULA.wasserstein2 (randomMapLaw F μ Q) (randomMapLaw F ν Q) ≤
        (q : ℝ≥0∞) * ULA.couplingCost c.joint + 0 := by
    let P := ULA.initialExtension c Q
    let X : (H × H) × S → H := fun p ↦ F (p.1.1,p.2)
    let Y : (H × H) × S → H := fun p ↦ F (p.1.2,p.2)
    have hX : Measurable X := hF.comp (measurable_fst.fst.prodMk measurable_snd)
    have hY : Measurable Y := hF.comp (measurable_fst.snd.prodMk measurable_snd)
    have hXLaw : P.map X = randomMapLaw F μ Q := ULA.initialExtension_map c Q F hF
    have hYLaw : P.map Y = randomMapLaw F ν Q := initialExtension_reference_map c Q F hF
    have hc := ULA.eLpNorm_contraction P (fun p ↦ X p - Y p)
      (fun p ↦ p.1.1 - p.1.2) q (hX.sub hY).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p ↦ hcontract p.1.1 p.1.2 p.2)
    have hw := ULA.wasserstein2_le_random_cost P X Y hX hY
    rw [hXLaw,hYLaw] at hw
    have hcost : eLpNorm (fun p : (H × H) × S ↦ p.1.1 - p.1.2) 2 P =
        ULA.couplingCost c.joint := ULA.initialExtension_cost c Q
    rw [hcost] at hc
    simpa only [add_zero] using hw.trans hc
  have hnonempty : Nonempty (ULA.Coupling μ ν) :=
    ⟨{ joint := μ.prod ν, fst := by simp, snd := by simp }⟩
  simpa only [add_zero] using ULA.wasserstein2_affine_bound_of_all_couplings
    μ ν (randomMapLaw F μ Q) (randomMapLaw F ν Q) q 0 hnonempty hfamily

/-- Independent probability inputs and a measurable endpoint give a probability law. -/
theorem randomMapLaw_probability (F : H × S → H) (hF : Measurable F)
    (μ : Measure H) [IsProbabilityMeasure μ] (Q : Measure S) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (randomMapLaw F μ Q) := by
  unfold randomMapLaw
  exact (Measure.isProbabilityMeasure_map_iff hF.aemeasurable).mpr inferInstance

/-- Finite initial transport permits the usual real-valued law estimate;
finiteness of the output is a consequence of the proved extended bound. -/
theorem randomMapLaw_wasserstein2Real_le (F : H × S → H) (hF : Measurable F)
    (q : ℝ≥0) (hcontract : ∀ x y s, ‖F (x,s)-F (y,s)‖ ≤ (q : ℝ)*‖x-y‖)
    (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure S) [IsProbabilityMeasure Q] (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) :
    ULA.wasserstein2Real (randomMapLaw F μ Q) (randomMapLaw F ν Q) ≤
      (q : ℝ) * ULA.wasserstein2Real μ ν := by
  have hb := randomMapLaw_wasserstein2_le F hF q hcontract μ ν Q
  have hprod : (q : ℝ≥0∞) * ULA.wasserstein2 μ ν ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hfinite
  have hr := ENNReal.toReal_mono hprod hb
  simpa only [ULA.wasserstein2Real, ENNReal.toReal_mul, ENNReal.coe_toReal] using hr

end RandomMaps

section KineticLaws
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

local instance velocityForcing_measurable (T : ℝ) : MeasurableSpace (VelocityForcing (E := E) T) := borel _
local instance velocityForcing_borel (T : ℝ) : BorelSpace (VelocityForcing (E := E) T) := ⟨rfl⟩

/-- Initial position first; shared velocity and the compact forcing path form
one independent source, with no distributional conclusion in its definition. -/
def kineticPositionMap (g : E → E) (L γ : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ)
    (p : E × (E × VelocityForcing (E := E) T)) : E :=
  (kineticFlow g L γ 1 hg T hT (p.2.1,p.1) p.2.2 t).2

theorem kineticPositionMap_continuous (g : E → E) (L γ : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    Continuous (kineticPositionMap g L γ hg T hT t) := by
  exact ((kineticFlow_endpoint_continuous g L γ 1 hg T hT t ht).comp
    ((continuous_snd.fst.prodMk continuous_fst).prodMk continuous_snd.snd)).snd

theorem kineticPositionMap_measurable (g : E → E) (L γ : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measurable (kineticPositionMap g L γ hg T hT t) :=
  (kineticPositionMap_continuous g L γ hg T hT t ht).measurable

/-- The actual kinetic endpoint map contracts position from the potential
assumptions; its integral equation supplies the noise-cancelled dynamics. -/
theorem kineticPositionMap_contract (f : E → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ)^2)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (x y : E) (s : E × VelocityForcing (E := E) T) :
    ‖kineticPositionMap (gradient f) M γ hLip T hT t (x,s) -
      kineticPositionMap (gradient f) M γ hLip T hT t (y,s)‖ ≤
      (Real.sqrt 2 * Real.exp ((-m / γ) * t)) * ‖x-y‖ := by
  have hY := kineticFlow_spec (gradient f) M γ 1 hLip T hT (s.1,x) s.2
  have hZ := kineticFlow_spec (gradient f) M γ 1 hLip T hT (s.1,y) s.2
  have heY : ∀ r ∈ Icc 0 T,
      kineticFlow (gradient f) M γ 1 hLip T hT (s.1,x) s.2 r -
        kineticFlow (gradient f) M γ 1 hLip T hT (s.1,x) s.2 0 =
      -(∫ u in 0..r, kineticNegativeDrift (gradient f) γ 1
        (kineticFlow (gradient f) M γ 1 hLip T hT (s.1,x) s.2 u)) +
        (normalizedForcing T hT s.2 r,0) := by
    intro r hr
    rw [hY.2.1]
    exact hY.2.2 r hr
  have heZ : ∀ r ∈ Icc 0 T,
      kineticFlow (gradient f) M γ 1 hLip T hT (s.1,y) s.2 r -
        kineticFlow (gradient f) M γ 1 hLip T hT (s.1,y) s.2 0 =
      -(∫ u in 0..r, kineticNegativeDrift (gradient f) γ 1
        (kineticFlow (gradient f) M γ 1 hLip T hT (s.1,y) s.2 u)) +
        (normalizedForcing T hT s.2 r,0) := by
    intro r hr
    rw [hZ.2.1]
    exact hZ.2.2 r hr
  have hc := kinetic_integral_position_decay f m M γ hdiff hsc hLip hmM hγ hfriction
    _ _ (fun r ↦ (normalizedForcing T hT s.2 r,0)) hY.1 hZ.1 T heY heZ
    (by rw [hY.2.1,hZ.2.1]) t ht
  simpa only [kineticPositionMap,hY.2.1,hZ.2.1] using hc

/-- Full arbitrary-shift contraction of the actual selected endpoint map. -/
theorem kineticPositionMap_contract_general (f : E → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hd : 0 < (γ : ℝ) - 2 * a)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (x y : E) (s : E × VelocityForcing (E := E) T) :
    ‖kineticPositionMap (gradient f) M γ hLip T hT t (x,s) -
      kineticPositionMap (gradient f) M γ hLip T hT t (y,s)‖ ≤
      (Real.sqrt (2 * (((γ : ℝ)-a)^2+a^2)) / ((γ : ℝ)-2*a) *
        Real.exp ((max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2) / ((γ : ℝ)-2*a))*t)) * ‖x-y‖ := by
  have hY := kineticFlow_spec (gradient f) M γ 1 hLip T hT (s.1,x) s.2
  have hZ := kineticFlow_spec (gradient f) M γ 1 hLip T hT (s.1,y) s.2
  have heY : ∀ r ∈ Icc 0 T,
      kineticFlow (gradient f) M γ 1 hLip T hT (s.1,x) s.2 r -
        kineticFlow (gradient f) M γ 1 hLip T hT (s.1,x) s.2 0 =
      -(∫ u in 0..r, kineticNegativeDrift (gradient f) γ 1
        (kineticFlow (gradient f) M γ 1 hLip T hT (s.1,x) s.2 u)) +
        (normalizedForcing T hT s.2 r,0) := by
    intro r hr
    rw [hY.2.1]
    exact hY.2.2 r hr
  have heZ : ∀ r ∈ Icc 0 T,
      kineticFlow (gradient f) M γ 1 hLip T hT (s.1,y) s.2 r -
        kineticFlow (gradient f) M γ 1 hLip T hT (s.1,y) s.2 0 =
      -(∫ u in 0..r, kineticNegativeDrift (gradient f) γ 1
        (kineticFlow (gradient f) M γ 1 hLip T hT (s.1,y) s.2 u)) +
        (normalizedForcing T hT s.2 r,0) := by
    intro r hr
    rw [hZ.2.1]
    exact hZ.2.2 r hr
  have hc := kinetic_integral_position_decay_general f m a M γ hdiff hsc hLip hmM hd
    _ _ (fun r ↦ (normalizedForcing T hT s.2 r,0)) hY.1 hZ.1 T heY heZ
    (by rw [hY.2.1,hZ.2.1]) t ht
  simpa only [kineticPositionMap,hY.2.1,hZ.2.1] using hc

/-- The concrete independent-product law of the kinetic position endpoint. -/
def kineticPositionLaw (g : E → E) (L γ : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (μ : Measure E)
    (Q : Measure (E × VelocityForcing (E := E) T)) : Measure E :=
  randomMapLaw (kineticPositionMap g L γ hg T hT t) μ Q

/-- The kinetic law-to-law bound with the true Wasserstein infimum. It holds
for every fixed law of shared initial velocity and continuous forcing,
independent of initial position. No stationarity assertion is used. -/
theorem kineticPositionLaw_wasserstein2 (f : E → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ)^2)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (E × VelocityForcing (E := E) T)) [IsProbabilityMeasure Q] :
    ULA.wasserstein2 (kineticPositionLaw (gradient f) M γ hLip T hT t μ Q)
      (kineticPositionLaw (gradient f) M γ hLip T hT t ν Q) ≤
        ENNReal.ofReal (Real.sqrt 2 * Real.exp ((-m / γ) * t)) * ULA.wasserstein2 μ ν := by
  have hq : 0 ≤ Real.sqrt 2 * Real.exp ((-m / γ) * t) := by positivity
  rw [ENNReal.ofReal_eq_coe_nnreal hq]
  exact randomMapLaw_wasserstein2_le (kineticPositionMap (gradient f) M γ hLip T hT t)
      (kineticPositionMap_measurable (gradient f) M γ hLip T hT t ht)
      ⟨_,hq⟩ (kineticPositionMap_contract f m M γ hdiff hsc hLip hmM hγ hfriction T hT t ht)
      μ ν Q

/-- The kinetic position endpoint is an actual probability law. -/
theorem kineticPositionLaw_probability (g : E → E) (L γ : ℝ≥0) (hg : LipschitzWith L g)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (Q : Measure (E × VelocityForcing (E := E) T)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (kineticPositionLaw g L γ hg T hT t μ Q) :=
  randomMapLaw_probability _ (kineticPositionMap_measurable g L γ hg T hT t ht) μ Q

/-- Real-valued continuous kinetic law-to-law contraction with finite initial
Wasserstein distance and no stationary-reference premise. -/
theorem kineticPositionLaw_wasserstein2Real (f : E → ℝ) (m : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < (γ : ℝ)) (hfriction : m + (M : ℝ) ≤ (γ : ℝ)^2)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (E × VelocityForcing (E := E) T)) [IsProbabilityMeasure Q]
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) :
    ULA.wasserstein2Real (kineticPositionLaw (gradient f) M γ hLip T hT t μ Q)
      (kineticPositionLaw (gradient f) M γ hLip T hT t ν Q) ≤
        Real.sqrt 2 * Real.exp ((-m / γ) * t) * ULA.wasserstein2Real μ ν := by
  exact randomMapLaw_wasserstein2Real_le
    (kineticPositionMap (gradient f) M γ hLip T hT t)
    (kineticPositionMap_measurable (gradient f) M γ hLip T hT t ht)
    ⟨_,by positivity⟩
    (kineticPositionMap_contract f m M γ hdiff hsc hLip hmM hγ hfriction T hT t ht)
    μ ν Q hfinite

/-- Theorem 1's full explicit prefactor and exponent for actual kinetic
position laws, with arbitrary invertible shifted coordinates. -/
theorem kineticPositionLaw_wasserstein2_general (f : E → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hd : 0 < (γ : ℝ)-2*a)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (E × VelocityForcing (E := E) T)) [IsProbabilityMeasure Q] :
    ULA.wasserstein2 (kineticPositionLaw (gradient f) M γ hLip T hT t μ Q)
      (kineticPositionLaw (gradient f) M γ hLip T hT t ν Q) ≤
      ENNReal.ofReal (Real.sqrt (2 * (((γ : ℝ)-a)^2+a^2)) / ((γ : ℝ)-2*a) *
        Real.exp ((max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2) / ((γ : ℝ)-2*a))*t)) *
        ULA.wasserstein2 μ ν := by
  have hq : 0 ≤ Real.sqrt (2 * (((γ : ℝ)-a)^2+a^2)) / ((γ : ℝ)-2*a) *
      Real.exp ((max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2) / ((γ : ℝ)-2*a))*t) := by positivity
  rw [ENNReal.ofReal_eq_coe_nnreal hq]
  exact randomMapLaw_wasserstein2_le (kineticPositionMap (gradient f) M γ hLip T hT t)
    (kineticPositionMap_measurable (gradient f) M γ hLip T hT t ht) ⟨_,hq⟩
    (kineticPositionMap_contract_general f m a M γ hdiff hsc hLip hmM hd T hT t ht) μ ν Q

/-- Real-valued full explicit kinetic law estimate, with the finite initial
transport premise needed to interpret the Wasserstein distance as a real. -/
theorem kineticPositionLaw_wasserstein2Real_general (f : E → ℝ) (m a : ℝ) (M γ : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (hLip : LipschitzWith M (gradient f)) (hmM : m ≤ (M : ℝ))
    (hd : 0 < (γ : ℝ)-2*a)
    (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : t ∈ Icc 0 T)
    (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure (E × VelocityForcing (E := E) T)) [IsProbabilityMeasure Q]
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) :
    ULA.wasserstein2Real (kineticPositionLaw (gradient f) M γ hLip T hT t μ Q)
      (kineticPositionLaw (gradient f) M γ hLip T hT t ν Q) ≤
      (Real.sqrt (2 * (((γ : ℝ)-a)^2+a^2)) / ((γ : ℝ)-2*a) *
        Real.exp ((max (a^2-m) ((M : ℝ)-((γ : ℝ)-a)^2) / ((γ : ℝ)-2*a))*t)) *
        ULA.wasserstein2Real μ ν := by
  exact randomMapLaw_wasserstein2Real_le (kineticPositionMap (gradient f) M γ hLip T hT t)
    (kineticPositionMap_measurable (gradient f) M γ hLip T hT t ht) ⟨_,by positivity⟩
    (kineticPositionMap_contract_general f m a M γ hdiff hsc hLip hmM hd T hT t ht) μ ν Q hfinite

end KineticLaws
end KineticLangevin
