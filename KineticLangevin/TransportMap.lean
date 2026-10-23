import UnadjustedLangevin.InitialCoupling
import UnadjustedLangevin.InitialExtension

noncomputable section
set_option linter.style.header false
open MeasureTheory
open scoped ENNReal NNReal
namespace KineticLangevin
variable {H K : Type*} [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] [NormedAddCommGroup K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K]

theorem wasserstein2_map_lipschitz (T : H → K) (hT : Measurable T) (q : ℝ≥0)
    (hLip : ∀ x y, ‖T x - T y‖ ≤ (q : ℝ) * ‖x-y‖)
    (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ULA.wasserstein2 (μ.map T) (ν.map T) ≤ (q : ℝ≥0∞) * ULA.wasserstein2 μ ν := by
  letI : Nonempty (ULA.Coupling μ ν) := ⟨{joint:=μ.prod ν,fst:=by simp,snd:=by simp}⟩
  have hfamily (c : ULA.Coupling μ ν) :
      ULA.wasserstein2 (μ.map T) (ν.map T) ≤ (q : ℝ≥0∞) * ULA.couplingCost c.joint := by
    have hX : Measurable (fun p : H × H ↦ T p.1) := hT.comp measurable_fst
    have hY : Measurable (fun p : H × H ↦ T p.2) := hT.comp measurable_snd
    have hw := ULA.wasserstein2_le_random_cost c.joint (fun p ↦ T p.1) (fun p ↦ T p.2) hX hY
    have hfirst : c.joint.map (fun p ↦ T p.1) = μ.map T := by
      calc
        _ = (c.joint.map Prod.fst).map T := (Measure.map_map hT measurable_fst).symm
        _ = _ := congrArg (fun ρ ↦ ρ.map T) c.fst
    have hsecond : c.joint.map (fun p ↦ T p.2) = ν.map T := by
      calc
        _ = (c.joint.map Prod.snd).map T := (Measure.map_map hT measurable_snd).symm
        _ = _ := congrArg (fun ρ ↦ ρ.map T) c.snd
    rw [hfirst,hsecond] at hw
    have hc : eLpNorm (fun p : H × H ↦ T p.1 - T p.2) 2 c.joint ≤
        (q : ℝ≥0∞) * eLpNorm (fun p : H × H ↦ p.1 - p.2) 2 c.joint := by
      simpa only [ENNReal.smul_def,smul_eq_mul,Pi.sub_def] using
        eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (hX.sub hY).aestronglyMeasurable
          ((ae_of_all c.joint (fun p ↦ hLip p.1 p.2)).mono (fun _ h ↦ by exact_mod_cast h)) 2
    exact hw.trans hc
  have hInf := le_iInf hfamily
  simpa only [ULA.wasserstein2,ENNReal.mul_iInf (fun h ↦ (ENNReal.coe_ne_top h).elim)] using hInf

theorem wasserstein2Real_map_lipschitz (T : H → K) (hT : Measurable T) (q : ℝ≥0)
    (hLip : ∀ x y, ‖T x - T y‖ ≤ (q : ℝ) * ‖x-y‖)
    (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : ULA.wasserstein2 μ ν ≠ ⊤) :
    ULA.wasserstein2Real (μ.map T) (ν.map T) ≤ (q : ℝ) * ULA.wasserstein2Real μ ν := by
  have hb := wasserstein2_map_lipschitz T hT q hLip μ ν
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinite) hb
  simpa only [ULA.wasserstein2Real,ENNReal.toReal_mul,ENNReal.coe_toReal] using hr

theorem wasserstein2_randomMap_lipschitz {S : Type*} [MeasurableSpace S]
    (F : H × S → K) (hF : Measurable F) (q : ℝ≥0)
    (hLip : ∀ x y s, ‖F (x,s) - F (y,s)‖ ≤ (q : ℝ) * ‖x-y‖)
    (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure S) [IsProbabilityMeasure Q] :
    ULA.wasserstein2 ((μ.prod Q).map F) ((ν.prod Q).map F) ≤
      (q : ℝ≥0∞) * ULA.wasserstein2 μ ν := by
  letI : Nonempty (ULA.Coupling μ ν) := ⟨{joint:=μ.prod ν,fst:=by simp,snd:=by simp}⟩
  have hfamily (c : ULA.Coupling μ ν) :
      ULA.wasserstein2 ((μ.prod Q).map F) ((ν.prod Q).map F) ≤ (q : ℝ≥0∞) * ULA.couplingCost c.joint := by
    let P := ULA.initialExtension c Q
    have hX : Measurable (fun p : (H × H) × S ↦ F (p.1.1,p.2)) := hF.comp (measurable_fst.fst.prodMk measurable_snd)
    have hY : Measurable (fun p : (H × H) × S ↦ F (p.1.2,p.2)) := hF.comp (measurable_fst.snd.prodMk measurable_snd)
    have hw := ULA.wasserstein2_le_random_cost P _ _ hX hY
    rw [ULA.initialExtension_map c Q F hF] at hw
    have hproj : P.map (fun p ↦ (p.1.2,p.2)) = ν.prod Q := by
      have := c.isProbabilityMeasure
      change (c.joint.prod Q).map (Prod.map Prod.snd id) = _
      simpa only [c.snd,Measure.map_id] using (Measure.map_prod_map c.joint Q measurable_snd measurable_id).symm
    have hYlaw : P.map (fun p ↦ F (p.1.2,p.2)) = (ν.prod Q).map F := by
      rw [← hproj,Measure.map_map hF (measurable_fst.snd.prodMk measurable_snd)]
      rfl
    rw [hYlaw] at hw
    have hc : eLpNorm (fun p : (H × H) × S ↦ F (p.1.1,p.2) - F (p.1.2,p.2)) 2 P ≤
        (q : ℝ≥0∞) * eLpNorm (fun p : (H × H) × S ↦ p.1.1-p.1.2) 2 P := by
      simpa only [ENNReal.smul_def,smul_eq_mul,Pi.sub_def] using
        eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (hX.sub hY).aestronglyMeasurable
          ((ae_of_all P (fun p ↦ hLip p.1.1 p.1.2 p.2)).mono (fun _ h ↦ by exact_mod_cast h)) 2
    rw [ULA.initialExtension_cost c Q] at hc
    exact hw.trans hc
  have hInf := le_iInf hfamily
  simpa only [ULA.wasserstein2,ENNReal.mul_iInf (fun h ↦ (ENNReal.coe_ne_top h).elim)] using hInf

end KineticLangevin
