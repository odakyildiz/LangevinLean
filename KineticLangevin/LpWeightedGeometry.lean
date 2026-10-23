import KineticLangevin.OBABOLaw
import KineticLangevin.KineticSplittingLp

/-! # The actual weighted L² phase lift

The Euclidean pair is constructed with continuous linear injections. Its L²
norm is exactly the Euclidean combination of the component L² norms. This
identifies the source-metric L² local error with the actual transport cost of
finite-dimensional weighted phase representatives.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory
open scoped RealInnerProductSpace NNReal ENNReal
namespace KineticLangevin
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] (P : Measure Ω)

def phaseInl : E →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E E)

def phaseInr : E →L[ℝ] WithLp 2 (E × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ E E)

def lpEuclideanPair (A B : Lp E 2 P) : Lp (WithLp 2 (E × E)) 2 P :=
  (phaseInl (E := E)).compLpL 2 P A + (phaseInr (E := E)).compLpL 2 P B

theorem lpEuclideanPair_coe (A B : Lp E 2 P) :
    lpEuclideanPair P A B =ᵐ[P] fun ω ↦ WithLp.toLp 2 (A ω,B ω) := by
  filter_upwards [Lp.coeFn_add ((phaseInl (E := E)).compLpL 2 P A) ((phaseInr (E := E)).compLpL 2 P B),
    ContinuousLinearMap.coeFn_compLpL (phaseInl (E := E)) A,
    ContinuousLinearMap.coeFn_compLpL (phaseInr (E := E)) B] with ω hadd hA hB
  change (lpEuclideanPair P A B : Ω → WithLp 2 (E × E)) ω = _
  rw [show (lpEuclideanPair P A B : Ω → WithLp 2 (E × E)) ω =
    ((phaseInl (E := E)).compLpL 2 P A) ω + ((phaseInr (E := E)).compLpL 2 P B) ω from hadd]
  rw [hA,hB]
  apply WithLp.ofLp_injective 2
  ext <;> simp [phaseInl,phaseInr]

theorem lpEuclideanPair_norm_sq (A B : Lp E 2 P) :
    ‖lpEuclideanPair P A B‖ ^ 2 = ‖A‖ ^ 2 + ‖B‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ ω, ⟪A ω,A ω⟫ + ⟪B ω,B ω⟫ ∂P := by
      apply integral_congr_ae
      filter_upwards [lpEuclideanPair_coe P A B] with ω hω
      rw [hω]
      rfl
    _ = (∫ ω, ⟪A ω,A ω⟫ ∂P) + ∫ ω, ⟪B ω,B ω⟫ ∂P :=
      integral_add (L2.integrable_inner A A) (L2.integrable_inner B B)
    _ = _ := by rw [← L2.inner_def, ← L2.inner_def, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

def lpWeightedTransform (a b : ℝ) (S : Lp E 2 P × Lp E 2 P) : Lp (WithLp 2 (E × E)) 2 P :=
  lpEuclideanPair P (S.2 + b • S.1) (Real.sqrt (a - b ^ 2) • S.1)

theorem lpWeightedTransform_coe (a b : ℝ) (S : Lp E 2 P × Lp E 2 P) :
    lpWeightedTransform P a b S =ᵐ[P] fun ω ↦ weightedPhaseTransform a b (lpPhaseCoe P S ω) := by
  filter_upwards [lpEuclideanPair_coe P (S.2 + b • S.1) (Real.sqrt (a - b ^ 2) • S.1),
    Lp.coeFn_add S.2 (b • S.1), Lp.coeFn_smul b S.1, Lp.coeFn_smul (Real.sqrt (a - b ^ 2)) S.1]
    with ω hpair hadd hsm hroot
  change (lpWeightedTransform P a b S : Ω → WithLp 2 (E × E)) ω = _
  rw [show (lpWeightedTransform P a b S : Ω → WithLp 2 (E × E)) ω =
    WithLp.toLp 2 ((S.2 + b • S.1 : Lp E 2 P) ω,(Real.sqrt (a - b ^ 2) • S.1 : Lp E 2 P) ω) from hpair]
  simp only [Pi.add_apply,Pi.smul_apply] at hadd hsm hroot
  rw [hadd,hsm,hroot]
  rfl

theorem lpWeightedTransform_norm (a b : ℝ) (S : Lp E 2 P × Lp E 2 P) :
    ‖lpWeightedTransform P a b S‖ = weightedPhaseNorm a b S := by
  have h1 := lpEuclideanPair_norm_sq P (S.2 + b • S.1) (Real.sqrt (a - b ^ 2) • S.1)
  have h2 : weightedPhaseNorm a b S ^ 2 =
      ‖S.2 + b • S.1‖ ^ 2 + ‖Real.sqrt (a - b ^ 2) • S.1‖ ^ 2 := by
    exact WithLp.prod_norm_sq_eq_of_L2 _
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  exact h1.trans h2.symm

theorem eLpNorm_weightedPhaseCoe (a b : ℝ) (S : Lp E 2 P × Lp E 2 P) :
    eLpNorm (fun ω ↦ weightedPhaseTransform a b (lpPhaseCoe P S ω)) 2 P =
      ENNReal.ofReal (weightedPhaseNorm a b S) := by
  rw [← eLpNorm_congr_ae (lpWeightedTransform_coe P a b S)]
  rw [← lpWeightedTransform_norm P a b S, Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (lpWeightedTransform P a b S))]

theorem lpPhaseCoe_sub (S T : Lp E 2 P × Lp E 2 P) :
    lpPhaseCoe P (S - T) =ᵐ[P] fun ω ↦ lpPhaseCoe P S ω - lpPhaseCoe P T ω := by
  filter_upwards [Lp.coeFn_sub S.1 T.1,Lp.coeFn_sub S.2 T.2] with ω h1 h2
  exact Prod.ext h1 h2

variable [IsFiniteMeasure P]

theorem lp_obaboStep_coe (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (h δ σ : ℝ) (S : Lp E 2 P × Lp E 2 P) (Ξ Ξ' : Lp E 2 P) :
    lpPhaseCoe P (obaboStep (ULA.lpDrift P g hg) h δ σ S Ξ Ξ') =ᵐ[P]
      fun ω ↦ obaboStep g h δ σ (lpPhaseCoe P S ω) (Ξ ω) (Ξ' ω) := by
  let G := ULA.lpDrift P g hg
  filter_upwards [lp_ornsteinStep_coe P δ σ Ξ S,
    lp_verletStep_coe P g M hg h (ornsteinStep δ σ Ξ S),
    lp_ornsteinStep_coe P δ σ Ξ' (verletStep G h (ornsteinStep δ σ Ξ S))]
    with ω hfirst hH hlast
  change lpPhaseCoe P (ornsteinStep δ σ Ξ' (verletStep G h (ornsteinStep δ σ Ξ S))) ω = _
  rw [hlast,hH,hfirst]
  rfl

end KineticLangevin
