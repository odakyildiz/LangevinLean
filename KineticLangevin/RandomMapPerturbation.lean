import KineticLangevin.FlowLaw
import UnadjustedLangevin.Recurrence
import UnadjustedLangevin.MarkovLaw

noncomputable section
set_option linter.style.header false
open MeasureTheory
open scoped NNReal ENNReal
namespace KineticLangevin
variable {H S : Type*} [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
  [SecondCountableTopology H] [MeasurableSpace S]

theorem randomMapLaw_affine_wasserstein2 (F G : H × S → H) (hF : Measurable F) (hG : Measurable G)
    (q b : ℝ≥0) (hcontract : ∀ x y s, ‖F (x,s) - F (y,s)‖ ≤ (q : ℝ) * ‖x-y‖)
    (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Q : Measure S) [IsProbabilityMeasure Q]
    (hlocal : eLpNorm (fun p ↦ G p - F p) 2 (ν.prod Q) ≤ (b : ℝ≥0∞)) :
    ULA.wasserstein2 (randomMapLaw F μ Q) (randomMapLaw G ν Q) ≤
      (q : ℝ≥0∞) * ULA.wasserstein2 μ ν + (b : ℝ≥0∞) := by
  have hfamily (c : ULA.Coupling μ ν) :
      ULA.wasserstein2 (randomMapLaw F μ Q) (randomMapLaw G ν Q) ≤
        (q : ℝ≥0∞) * ULA.couplingCost c.joint + (b : ℝ≥0∞) := by
    let P := ULA.initialExtension c Q
    let X : (H × H) × S → H := fun p ↦ p.1.1
    let Y : (H × H) × S → H := fun p ↦ p.1.2
    let X' : (H × H) × S → H := fun p ↦ F (p.1.1,p.2)
    let Y' : (H × H) × S → H := fun p ↦ G (p.1.2,p.2)
    let A : (H × H) × S → H := fun p ↦ F (p.1.1,p.2) - F (p.1.2,p.2)
    let V : (H × H) × S → H := fun p ↦ G (p.1.2,p.2) - F (p.1.2,p.2)
    have hX' : Measurable X' := hF.comp (measurable_fst.fst.prodMk measurable_snd)
    have hY' : Measurable Y' := hG.comp (measurable_fst.snd.prodMk measurable_snd)
    have hA : AEStronglyMeasurable A P :=
      (hX'.sub (hF.comp (measurable_fst.snd.prodMk measurable_snd))).aestronglyMeasurable
    have hidentity : ∀ᵐ p ∂P, X' p - Y' p = A p - V p := ae_of_all _ (fun p ↦ by dsimp [X',Y',A,V];abel)
    have hc : ∀ᵐ p ∂P, ‖A p‖ ≤ (q : ℝ) * ‖X p - Y p‖ :=
      ae_of_all _ (fun p ↦ hcontract p.1.1 p.1.2 p.2)
    have hw := ULA.synchronous_wasserstein_bound P X Y X' Y' A V q hX' hY' hA hidentity hc
    rw [ULA.initialExtension_map c Q F hF, initialExtension_reference_map c Q G hG] at hw
    have hcost : eLpNorm (fun p : (H × H) × S ↦ X p - Y p) 2 P = ULA.couplingCost c.joint :=
      ULA.initialExtension_cost c Q
    rw [hcost] at hw
    have hproj : P.map (fun p ↦ (p.1.2,p.2)) = ν.prod Q := by
      have := c.isProbabilityMeasure
      change (c.joint.prod Q).map (Prod.map Prod.snd id) = _
      simpa only [c.snd,Measure.map_id] using (Measure.map_prod_map c.joint Q measurable_snd measurable_id).symm
    have hD : Measurable (fun p : H × S ↦ G p - F p) := hG.sub hF
    have hpair : Measurable (fun p : (H × H) × S ↦ (p.1.2,p.2)) :=
      measurable_fst.snd.prodMk measurable_snd
    have he := eLpNorm_map_measure (μ := P) (p := 2) (g := fun p : H × S ↦ G p - F p)
      hD.aestronglyMeasurable hpair.aemeasurable
    rw [hproj] at he
    have he' : eLpNorm (fun p : H × S ↦ G p - F p) 2 (ν.prod Q) = eLpNorm V 2 P := by
      simpa only [V,Function.comp_def] using he
    have hV : eLpNorm V 2 P ≤ (b : ℝ≥0∞) := he'.symm.trans_le hlocal
    exact hw.trans (add_le_add le_rfl hV)
  exact ULA.wasserstein2_affine_bound_of_all_couplings μ ν _ _ q b
    ⟨{joint := μ.prod ν,fst := by simp,snd := by simp}⟩ hfamily

theorem markovLaws_bias_of_invariant_comparator (F G : H × S → H) (hF : Measurable F) (hG : Measurable G)
    (q b : ℝ≥0) (hq : (q : ℝ) < 1)
    (hcontract : ∀ x y s, ‖F (x,s) - F (y,s)‖ ≤ (q : ℝ) * ‖x-y‖)
    (μ π : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (Q : Measure S) [IsProbabilityMeasure Q]
    (hinvariant : randomMapLaw G π Q = π)
    (hlocal : eLpNorm (fun p ↦ G p - F p) 2 (π.prod Q) ≤ (b : ℝ≥0∞))
    (hfinite : ULA.wasserstein2 μ π ≠ ⊤) (n : ℕ) :
    ULA.wasserstein2Real (ULA.markovLaws (fun x s ↦ F (x,s)) Q μ n) π ≤
      (q : ℝ) ^ n * ULA.wasserstein2Real μ π + (b : ℝ) / (1 - (q : ℝ)) := by
  let K := fun x s ↦ F (x,s)
  have hK : Measurable (Function.uncurry K) := by
    convert hF using 1
    funext p
    rfl
  have hstep (k : ℕ) :
      ULA.wasserstein2 (ULA.markovLaws K Q μ (k+1)) π ≤
        (q : ℝ≥0∞) * ULA.wasserstein2 (ULA.markovLaws K Q μ k) π + (b : ℝ≥0∞) := by
    haveI := ULA.markovLaws_isProbability K hK μ Q k
    have hb := randomMapLaw_affine_wasserstein2 F G hF hG q b hcontract
      (ULA.markovLaws K Q μ k) π Q hlocal
    rw [hinvariant] at hb
    exact hb
  have hf : ∀ k, ULA.wasserstein2 (ULA.markovLaws K Q μ k) π ≠ ⊤ := by
    intro k
    induction k with
    | zero => exact hfinite
    | succ k ih =>
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top ih,ENNReal.coe_ne_top⟩) (hstep k)
  let e : ℕ → ℝ := fun k ↦ ULA.wasserstein2Real (ULA.markovLaws K Q μ k) π
  have hrec (k : ℕ) : e (k+1) ≤ (q : ℝ) * e k + (b : ℝ) := by
    have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top (hf k),ENNReal.coe_ne_top⟩) (hstep k)
    simpa only [e,ULA.wasserstein2Real,ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top (hf k)) ENNReal.coe_ne_top,
      ENNReal.toReal_mul,ENNReal.coe_toReal] using hr
  exact ULA.affine_recurrence_bound e q b q.coe_nonneg hq b.coe_nonneg hrec n

theorem markovLaws_ne_top_of_invariant_comparator (F G : H × S → H) (hF : Measurable F) (hG : Measurable G)
    (q b : ℝ≥0) (hcontract : ∀ x y s, ‖F (x,s) - F (y,s)‖ ≤ (q : ℝ) * ‖x-y‖)
    (μ π : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (Q : Measure S) [IsProbabilityMeasure Q] (hinvariant : randomMapLaw G π Q = π)
    (hlocal : eLpNorm (fun p ↦ G p - F p) 2 (π.prod Q) ≤ (b : ℝ≥0∞))
    (hfinite : ULA.wasserstein2 μ π ≠ ⊤) (n : ℕ) :
    ULA.wasserstein2 (ULA.markovLaws (fun x s ↦ F (x,s)) Q μ n) π ≠ ⊤ := by
  let K := fun x s ↦ F (x,s)
  have hK : Measurable (Function.uncurry K) := by convert hF using 1;funext p;rfl
  induction n with
  | zero => exact hfinite
  | succ n ih =>
    haveI := ULA.markovLaws_isProbability K hK μ Q n
    have hb := randomMapLaw_affine_wasserstein2 F G hF hG q b hcontract
      (ULA.markovLaws K Q μ n) π Q hlocal
    rw [hinvariant] at hb
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top ih,ENNReal.coe_ne_top⟩) hb

end KineticLangevin
