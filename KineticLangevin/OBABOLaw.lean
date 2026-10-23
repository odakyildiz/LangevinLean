import KineticLangevin.OBABOContraction
import KineticLangevin.FlowLaw
import UnadjustedLangevin.MarkovLaw

/-! # Actual OBABO laws in the contracting Hilbert coordinates

The weighted energy is realized by an explicit invertible linear coordinate
change. The actual independent-noise Markov laws commute with that change.
The pathwise contraction is passed through every input coupling and the true
Wasserstein infimum; no optimal coupling or law identity is postulated.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance phaseLp_measurable : MeasurableSpace (WithLp 2 (E × E)) := borel _
local instance phaseLp_borel : BorelSpace (WithLp 2 (E × E)) := ⟨rfl⟩

def weightedPhaseInverse (a b : ℝ) (y : WithLp 2 (E × E)) : E × E :=
  ((Real.sqrt (a - b ^ 2))⁻¹ • y.ofLp.2,
    y.ofLp.1 - b • ((Real.sqrt (a - b ^ 2))⁻¹ • y.ofLp.2))

theorem weightedPhaseTransform_sub (a b : ℝ) (s t : E × E) :
    weightedPhaseTransform a b (s - t) = weightedPhaseTransform a b s - weightedPhaseTransform a b t := by
  apply WithLp.ofLp_injective 2
  ext <;> simp only [weightedPhaseTransform, WithLp.ofLp_toLp, WithLp.ofLp_sub,
    Prod.fst_sub, Prod.snd_sub] <;> module

theorem weightedPhaseTransform_inverse (a b : ℝ) (hab : b ^ 2 < a)
    (y : WithLp 2 (E × E)) : weightedPhaseTransform a b (weightedPhaseInverse a b y) = y := by
  have hc : Real.sqrt (a - b ^ 2) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.mpr hab)).ne'
  apply WithLp.ofLp_injective 2
  change (_, _) = y.ofLp
  ext
  · dsimp [weightedPhaseInverse]
    module
  · dsimp [weightedPhaseInverse]
    rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem weightedPhaseInverse_transform (a b : ℝ) (hab : b ^ 2 < a) (s : E × E) :
    weightedPhaseInverse a b (weightedPhaseTransform a b s) = s := by
  have hc : Real.sqrt (a - b ^ 2) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.mpr hab)).ne'
  dsimp [weightedPhaseInverse, weightedPhaseTransform]
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  ext <;> simp

theorem weightedPhaseTransform_continuous (a b : ℝ) : Continuous (@weightedPhaseTransform E _ _ a b) := by
  exact (WithLp.prod_continuous_toLp 2 E E).comp (by fun_prop)

theorem weightedPhaseInverse_continuous (a b : ℝ) : Continuous (@weightedPhaseInverse E _ _ a b) := by
  have hc := WithLp.prod_continuous_ofLp 2 E E
  exact (hc.snd.const_smul _).prodMk (hc.fst.sub ((hc.snd.const_smul _).const_smul _))

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def weightedObaboStep (g : E → E) (γ L h σ : ℝ)
    (y : WithLp 2 (E × E)) (ξ : E × E) : WithLp 2 (E × E) :=
  weightedPhaseTransform (1 / L) (1 / γ)
    (obaboStep g h (obaboDamping γ h) σ (weightedPhaseInverse (1 / L) (1 / γ) y) ξ.1 ξ.2)

theorem weightedObaboStep_continuous (g : E → E) (hg : Continuous g) (γ L h σ : ℝ) :
    Continuous (Function.uncurry (weightedObaboStep g γ L h σ)) := by
  apply (weightedPhaseTransform_continuous (1 / L) (1 / γ)).comp
  unfold obaboStep ornsteinStep kickStep driftStep
  have hI : Continuous (fun p : WithLp 2 (E × E) × (E × E) ↦ weightedPhaseInverse (1 / L) (1 / γ) p.1) :=
    (weightedPhaseInverse_continuous (E := E) (1 / L) (1 / γ)).comp continuous_fst
  fun_prop

theorem obabo_metric_strict (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L)
    (hfriction : 4 * L ≤ γ ^ 2) : (1 / γ) ^ 2 < 1 / L := by
  have hmetric := obabo_metric_condition γ L hγ hL hfriction
  have hp : 0 < (1 / γ) ^ 2 := sq_pos_of_pos (by positivity)
  linarith

theorem weightedObaboStep_contract (f : E → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) (hm : 0 ≤ m) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (y z : WithLp 2 (E × E)) (ξ : E × E) :
    ‖weightedObaboStep (gradient f) γ M h σ y ξ - weightedObaboStep (gradient f) γ M h σ z ξ‖ ≤
      Real.sqrt (1 - m * h / (3 * γ)) * ‖y - z‖ := by
  have hab := obabo_metric_strict γ M hγ hM hfriction
  have he := obaboStep_synchronous_contraction f m γ h σ M hdiff hsc hLip hm hmM hγ hM hh hfriction hstep
    (weightedPhaseInverse (1 / (M : ℝ)) (1 / γ) y) (weightedPhaseInverse (1 / (M : ℝ)) (1 / γ) z) ξ.1 ξ.2
  rw [← weightedPhaseNorm_sq _ _ hab.le, ← weightedPhaseNorm_sq _ _ hab.le] at he
  unfold weightedPhaseNorm at he
  rw [weightedPhaseTransform_sub, weightedPhaseTransform_sub,
    weightedPhaseTransform_inverse _ _ hab y, weightedPhaseTransform_inverse _ _ hab z] at he
  have hs := obabo_step_size_consequences γ M m h hγ hh hmM hfriction hstep
  have hq := obabo_contraction_factor_nonneg γ M m h hγ hh hmM hfriction hs.1
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hq]
  exact he

section Conjugacy
variable {H K Z : Type*} [MeasurableSpace H] [MeasurableSpace K] [MeasurableSpace Z]

theorem markovLaws_map_conjugacy (F : H → Z → H) (G : K → Z → K) (T : H → K)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (hT : Measurable T) (hconj : ∀ x ξ, T (F x ξ) = G (T x) ξ)
    (μ : Measure H) (η : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure η] (n : ℕ) :
    (ULA.markovLaws F η μ n).map T = ULA.markovLaws G η (μ.map T) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let ρ := ULA.markovLaws F η μ n
    letI : IsProbabilityMeasure ρ := ULA.markovLaws_isProbability F hF μ η n
    have hpair : Measurable (fun p : H × Z ↦ (T p.1, p.2)) :=
      (hT.comp measurable_fst).prodMk measurable_snd
    have hprod : (ρ.map T).prod η = (ρ.prod η).map (fun p ↦ (T p.1, p.2)) := by
      have hr := Measure.map_prod_map ρ η hT measurable_id
      rw [Prod.map_def] at hr
      simpa only [Measure.map_id, id_eq] using hr
    change ((ρ.prod η).map (Function.uncurry F)).map T =
      ((ULA.markovLaws G η (μ.map T) n).prod η).map (Function.uncurry G)
    rw [← ih, hprod, Measure.map_map hT hF,
      Measure.map_map hG hpair]
    congr 1
    funext p
    exact hconj p.1 p.2
end Conjugacy

def obaboLaws (g : E → E) (γ h σ : ℝ) (η : Measure (E × E)) (μ : Measure (E × E)) (n : ℕ) :=
  ULA.markovLaws (fun z ξ ↦ obaboStep g h (obaboDamping γ h) σ z ξ.1 ξ.2) η μ n

def weightedObaboLaws (g : E → E) (γ L h σ : ℝ) (η : Measure (E × E))
    (μ : Measure (WithLp 2 (E × E))) (n : ℕ) :=
  ULA.markovLaws (weightedObaboStep g γ L h σ) η μ n

theorem obaboLaws_weighted_map (g : E → E) (hg : Continuous g) (γ L h σ : ℝ)
    (hγ : 0 < γ) (hL : 0 < L) (hfriction : 4 * L ≤ γ ^ 2)
    (η μ : Measure (E × E)) [IsProbabilityMeasure η] [IsProbabilityMeasure μ] (n : ℕ) :
    (obaboLaws g γ h σ η μ n).map (weightedPhaseTransform (1 / L) (1 / γ)) =
      weightedObaboLaws g γ L h σ η (μ.map (weightedPhaseTransform (1 / L) (1 / γ))) n := by
  apply markovLaws_map_conjugacy
  · apply Continuous.measurable
    unfold Function.uncurry obaboStep ornsteinStep kickStep driftStep
    fun_prop
  · exact (weightedObaboStep_continuous g hg γ L h σ).measurable
  · exact (weightedPhaseTransform_continuous (1 / L) (1 / γ)).measurable
  · intro z ξ
    unfold weightedObaboStep
    rw [weightedPhaseInverse_transform _ _ (obabo_metric_strict γ L hγ hL hfriction)]

def obaboContractionRate (m γ h : ℝ) : ℝ≥0 :=
  ⟨Real.sqrt (1 - m * h / (3 * γ)), Real.sqrt_nonneg _⟩

theorem weightedObaboLaws_wasserstein2 (f : E → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) (hm : 0 ≤ m) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (η : Measure (E × E)) [IsProbabilityMeasure η]
    (μ ν : Measure (WithLp 2 (E × E))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (n : ℕ) :
    ULA.wasserstein2 (weightedObaboLaws (gradient f) γ M h σ η μ n)
      (weightedObaboLaws (gradient f) γ M h σ η ν n) ≤
      (obaboContractionRate m γ h : ℝ≥0∞) ^ n *
        ULA.wasserstein2 μ ν := by
  let q := obaboContractionRate m γ h
  let F := weightedObaboStep (gradient f) γ M h σ
  have hF : Measurable (Function.uncurry F) :=
    (weightedObaboStep_continuous (gradient f) hLip.continuous γ M h σ).measurable
  have hcontract : ∀ x y ξ, ‖F x ξ - F y ξ‖ ≤ (q : ℝ) * ‖x-y‖ :=
    weightedObaboStep_contract f m γ h σ M hdiff hsc hLip hm hmM hγ hM hh hfriction hstep
  change ULA.wasserstein2 (ULA.markovLaws F η μ n) (ULA.markovLaws F η ν n) ≤
    (q : ℝ≥0∞) ^ n * ULA.wasserstein2 μ ν
  induction n with
  | zero => simp [ULA.markovLaws]
  | succ n ih =>
    letI := ULA.markovLaws_isProbability F hF μ η n
    letI := ULA.markovLaws_isProbability F hF ν η n
    have hw := randomMapLaw_wasserstein2_le (Function.uncurry F) hF q hcontract
      (ULA.markovLaws F η μ n) (ULA.markovLaws F η ν n) η
    change ULA.wasserstein2 (ULA.markovStep F η (ULA.markovLaws F η μ n))
      (ULA.markovStep F η (ULA.markovLaws F η ν n)) ≤ _
    calc
      _ ≤ (q : ℝ≥0∞) * ULA.wasserstein2 (ULA.markovLaws F η μ n) (ULA.markovLaws F η ν n) := hw
      _ ≤ (q : ℝ≥0∞) * ((q : ℝ≥0∞) ^ n * ULA.wasserstein2 μ ν) := by gcongr
      _ = _ := by rw [pow_succ];ring

theorem obaboLaws_weighted_wasserstein2 (f : E → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) (hm : 0 ≤ m) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (η μ ν : Measure (E × E)) [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (n : ℕ) :
    ULA.wasserstein2
      ((obaboLaws (gradient f) γ h σ η μ n).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
      ((obaboLaws (gradient f) γ h σ η ν n).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) ≤
      (obaboContractionRate m γ h : ℝ≥0∞) ^ n *
        ULA.wasserstein2 (μ.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
          (ν.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) := by
  let T := weightedPhaseTransform (E := E) (1 / (M : ℝ)) (1 / γ)
  have hT : Measurable T := (weightedPhaseTransform_continuous (1 / (M : ℝ)) (1 / γ)).measurable
  letI : IsProbabilityMeasure (μ.map T) := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  letI : IsProbabilityMeasure (ν.map T) := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).mpr inferInstance
  rw [obaboLaws_weighted_map (gradient f) hLip.continuous γ M h σ hγ hM hfriction η μ n,
    obaboLaws_weighted_map (gradient f) hLip.continuous γ M h σ hγ hM hfriction η ν n]
  exact weightedObaboLaws_wasserstein2 f m γ h σ M hdiff hsc hLip hm hmM hγ hM hh hfriction hstep η (μ.map T) (ν.map T) n

theorem obaboLaws_weighted_wasserstein2Real (f : E → ℝ) (m γ h σ : ℝ) (M : ℝ≥0)
    (hdiff : Differentiable ℝ f) (hsc : StrongConvexOn Set.univ m f)
    (hLip : LipschitzWith M (gradient f)) (hm : 0 ≤ m) (hmM : m ≤ (M : ℝ))
    (hγ : 0 < γ) (hM : 0 < (M : ℝ)) (hh : 0 ≤ h)
    (hfriction : 4 * (M : ℝ) ≤ γ ^ 2) (hstep : 33 * γ ^ 3 * h ≤ m)
    (η μ ν : Measure (E × E)) [IsProbabilityMeasure η] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hfinite : ULA.wasserstein2 (μ.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
      (ν.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) ≠ ⊤) (n : ℕ) :
    ULA.wasserstein2Real
      ((obaboLaws (gradient f) γ h σ η μ n).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
      ((obaboLaws (gradient f) γ h σ η ν n).map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) ≤
      (obaboContractionRate m γ h : ℝ) ^ n *
        ULA.wasserstein2Real (μ.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
          (ν.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) := by
  have hb := obaboLaws_weighted_wasserstein2 f m γ h σ M hdiff hsc hLip hm hmM hγ hM hh hfriction hstep η μ ν n
  have hprod : (obaboContractionRate m γ h : ℝ≥0∞) ^ n *
      ULA.wasserstein2 (μ.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ)))
        (ν.map (weightedPhaseTransform (1 / (M : ℝ)) (1 / γ))) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) hfinite
  have hr := ENNReal.toReal_mono hprod hb
  simpa only [ULA.wasserstein2Real, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal] using hr

end KineticLangevin
