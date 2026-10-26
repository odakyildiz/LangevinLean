import PBGSO.QuadraticMartingale
import UnadjustedLangevin.MarkovLaw
import UnadjustedLangevin.GaussianMoments
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Random-coefficient Gaussian step isometry

The coefficients may depend on the entire past. Independence is imposed
between the current innovation vector and that past, not between the
coefficient columns. Weighted second moments are calculated from Gaussian
coordinate laws and primitive independence.
-/
noncomputable section
set_option linter.unusedSectionVars false
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology RealInnerProductSpace InnerProductSpace
namespace PBGSO.PredictableIsometry

variable {Ω Z I : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

theorem pairing_integrable (W : Z →L[ℝ] Z) (A B : Ω → Z)
    (hA : MemLp A 2 Q) (hB : MemLp B 2 Q) :
    Integrable (fun ω => ⟪A ω, W (B ω)⟫_ℝ) Q := by
  apply (lp_weighted_pairing_integrable Q W (hA.toLp A) (hB.toLp B)).congr
  filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with ω ha hb
  rw [ha, hb]

/-- Independence of a square-integrable scalar innovation and random
coefficient gives an actual square-integrable noise contribution. -/
theorem independent_smul_memLp (ξ : Ω → ℝ) (A : Ω → Z)
    (hξ : MemLp ξ 2 Q) (hA : MemLp A 2 Q) (hInd : IndepFun ξ A Q) :
    MemLp (fun ω => ξ ω • A ω) 2 Q := by
  apply (memLp_two_iff_integrable_sq_norm (hξ.aestronglyMeasurable.smul
    hA.aestronglyMeasurable)).mpr
  have hξsq := (memLp_two_iff_integrable_sq_norm hξ.aestronglyMeasurable).mp hξ
  have hAsq := (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA
  have hind := hInd.comp (continuous_norm.pow 2).measurable (continuous_norm.pow 2).measurable
  have hi := hind.integrable_mul hξsq hAsq
  apply hi.congr
  exact ae_of_all Q fun ω => by
    change ‖ξ ω‖ ^ 2 * ‖A ω‖ ^ 2 = ‖ξ ω • A ω‖ ^ 2
    rw [norm_smul, mul_pow]

section Vector
variable [Fintype I] [DecidableEq I]

/-- One actual innovation step with random coefficient columns. -/
def stepSum (ξ : I → Ω → ℝ) (A : I → Ω → Z) (ω : Ω) : Z :=
  ∑ i, ξ i ω • A i ω

theorem stepSum_memLp (ξ : I → Ω → ℝ) (A : I → Ω → Z)
    (hξ : ∀ i, MemLp (ξ i) 2 Q) (hA : ∀ i, MemLp (A i) 2 Q)
    (hInd : IndepFun (fun ω i => ξ i ω) (fun ω i => A i ω) Q) :
    MemLp (stepSum ξ A) 2 Q := by
  apply memLp_finsetSum Finset.univ
  intro i _
  apply independent_smul_memLp Q _ _ (hξ i) (hA i)
  exact hInd.comp (measurable_pi_apply i) (measurable_pi_apply i)

/-- Cross moments separate the current innovation vector from the random
past-dependent coefficients. Within-column Gaussian independence is a
separate primitive and will discharge the innovation covariance below. -/
theorem weighted_cross_moment (W : Z →L[ℝ] Z)
    (ξ : I → Ω → ℝ) (A : I → Ω → Z)
    (hξ : ∀ i, MemLp (ξ i) 2 Q) (hA : ∀ i, MemLp (A i) 2 Q)
    (hInd : IndepFun (fun ω i => ξ i ω) (fun ω i => A i ω) Q) (i j : I) :
    (∫ ω, ⟪ξ i ω • A i ω, W (ξ j ω • A j ω)⟫_ℝ ∂Q) =
      (∫ ω, ξ i ω * ξ j ω ∂Q) * (∫ ω, ⟪A i ω, W (A j ω)⟫_ℝ ∂Q) := by
  have hind := hInd.comp
    (show Measurable (fun x : I → ℝ => x i * x j) by fun_prop)
    (show Measurable (fun x : I → Z => ⟪x i, W (x j)⟫_ℝ) by fun_prop)
  have h1 : Integrable (fun ω => ξ i ω * ξ j ω) Q :=
    (hξ i).integrable_mul (hξ j)
  have h2 := pairing_integrable Q W (A i) (A j) (hA i) (hA j)
  have he := hind.integral_mul_eq_mul_integral h1.aestronglyMeasurable h2.aestronglyMeasurable
  simp only [Function.comp_apply, Pi.mul_apply] at he
  convert he using 1
  apply integral_congr_ae
  exact ae_of_all Q fun ω => by
    simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring

/-- A fresh independent standard Gaussian coordinate vector has its
actual identity covariance, derived from its primitive laws. -/
theorem gaussian_cross_moment (ξ : I → Ω → ℝ)
    (hLaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) Q) (hInd : iIndepFun ξ Q) (i j : I) :
    (∫ ω, ξ i ω * ξ j ω ∂Q) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    simpa only [pow_two, Function.comp_apply, NNReal.coe_one] using ((hLaw i).integral_comp
      (f := fun x : ℝ => x ^ 2) (by fun_prop)).trans (ULA.centered_gaussian_second_moment 1)
  · rw [ite_eq_right hij]
    have hi : (∫ ω, ξ i ω ∂Q) = 0 := by
      exact ((hLaw i).integral_comp (f := id) (by fun_prop)).trans integral_id_gaussianReal
    have hj : (∫ ω, ξ j ω ∂Q) = 0 := by
      exact ((hLaw j).integral_comp (f := id) (by fun_prop)).trans integral_id_gaussianReal
    have he := (hInd.indepFun hij).integral_mul_eq_mul_integral
      (hLaw i).aemeasurable.aestronglyMeasurable (hLaw j).aemeasurable.aestronglyMeasurable
    simpa only [Pi.mul_apply, hi, hj, zero_mul] using he

/-- Exact weighted isometry of an actual Gaussian step with arbitrary
random coefficient columns independent of the fresh innovation vector. -/
theorem gaussian_step_isometry (W : Z →L[ℝ] Z)
    (ξ : I → Ω → ℝ) (A : I → Ω → Z)
    (hLaw : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) Q)
    (hξInd : iIndepFun ξ Q) (hA : ∀ i, MemLp (A i) 2 Q)
    (hInd : IndepFun (fun ω i => ξ i ω) (fun ω i => A i ω) Q) :
    (∫ ω, ⟪stepSum ξ A ω, W (stepSum ξ A ω)⟫_ℝ ∂Q) =
      ∑ i, ∫ ω, ⟪A i ω, W (A i ω)⟫_ℝ ∂Q := by
  have hξ (i : I) : MemLp (ξ i) 2 Q :=
    (hLaw i).memLp (memLp_id_gaussianReal (2 : ℝ≥0))
  have hm (i : I) : MemLp (fun ω => ξ i ω • A i ω) 2 Q :=
    independent_smul_memLp (mΩ := mΩ) Q _ _ (hξ i) (hA i)
      (hInd.comp (measurable_pi_apply i) (measurable_pi_apply i))
  have hi (i j : I) : Integrable
      (fun ω => ⟪ξ i ω • A i ω, W (ξ j ω • A j ω)⟫_ℝ) Q :=
    pairing_integrable Q W _ _ (hm i) (hm j)
  have he : (fun ω => ⟪stepSum ξ A ω, W (stepSum ξ A ω)⟫_ℝ) =
      (fun ω => ∑ i, ∑ j, ⟪ξ i ω • A i ω, W (ξ j ω • A j ω)⟫_ℝ) := by
    funext ω
    simp only [stepSum, map_sum, sum_inner, inner_sum]
    exact Finset.sum_comm
  rw [he, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  simp_rw [weighted_cross_moment Q W ξ A hξ hA hInd,
    gaussian_cross_moment Q ξ hLaw hξInd]
  simp

/-- A predictable random-coefficient Gaussian step has zero conditional
mean. Independence from the past and adaptedness are primitive inputs;
the martingale increment property is derived by conditional pull-out. -/
theorem independent_step_condExp_zero
    (F : MeasurableSpace Ω) (hF : F ≤ mΩ)
    (ξ : I → Ω → ℝ) (A : I → Ω → Z)
    (hξmeas : ∀ i, @Measurable Ω ℝ mΩ inferInstance (ξ i))
    (hξ : ∀ i, MemLp (ξ i) 2 Q) (hA : ∀ i, MemLp (A i) 2 Q)
    (hAadapt : ∀ i, StronglyMeasurable[F] (A i))
    (hInd : IndepFun (fun ω i => ξ i ω) (fun ω i => A i ω) Q)
    (hPast : Indep (MeasurableSpace.comap (fun ω i => ξ i ω) inferInstance) F Q)
    (hmean : ∀ i, (∫ ω, ξ i ω ∂Q) = 0) :
    Q[stepSum ξ A | F] =ᵐ[Q] (0 : Ω → Z) := by
  let G := MeasurableSpace.comap (fun ω i => ξ i ω) inferInstance
  have hmwhole : @Measurable Ω (I → ℝ) mΩ inferInstance (fun ω i => ξ i ω) :=
    (@measurable_pi_iff Ω I (fun _ => ℝ) mΩ (fun _ => inferInstance)
      (fun ω i => ξ i ω)).mpr hξmeas
  have hG : G ≤ mΩ := hmwhole.comap_le
  have hprod (i : I) : MemLp (fun ω => ξ i ω • A i ω) 2 Q :=
    independent_smul_memLp (mΩ := mΩ) Q _ _ (hξ i) (hA i)
      (hInd.comp (measurable_pi_apply i) (measurable_pi_apply i))
  have hξcond (i : I) : Q[ξ i | F] =ᵐ[Q] (0 : Ω → ℝ) := by
    have hmblock : Measurable[G] (fun ω i => ξ i ω) :=
      measurable_iff_comap_le.mpr le_rfl
    have hmeas : Measurable[G] (ξ i) := by
      simpa only [Function.comp_def] using (measurable_pi_apply i).comp hmblock
    have he := condExp_indep_eq hG hF hmeas.stronglyMeasurable hPast
    change Q[ξ i | F] =ᵐ[Q] (fun _ => (0 : ℝ))
    simpa only [hmean i] using he
  have hcond (i : I) : Q[(fun ω => ξ i ω • A i ω) | F] =ᵐ[Q] (0 : Ω → Z) := by
    have hp := condExp_smul_of_aestronglyMeasurable_right
      ((hξ i).integrable (by norm_num)) ((hprod i).integrable (by norm_num))
      (hAadapt i).aestronglyMeasurable
    have heqfun : ξ i • A i = (fun ω => ξ i ω • A i ω) := rfl
    rw [heqfun] at hp
    filter_upwards [hp, hξcond i] with ω hp hξ0
    simpa only [Pi.smul_apply', hξ0, zero_smul, Pi.zero_apply] using hp
  have he := condExp_finsetSum (s := Finset.univ)
    (fun i _ => (hprod i).integrable (by norm_num)) F
  have hsum : (∑ i : I, Q[(fun ω => ξ i ω • A i ω) | F]) =ᵐ[Q] (0 : Ω → Z) := by
    filter_upwards [ae_all_iff.mpr hcond] with ω hω
    simp only [Finset.sum_apply, hω, Pi.zero_apply, Finset.sum_const_zero]
  have hfun : stepSum ξ A = ∑ i : I, (fun ω => ξ i ω • A i ω) := by
    funext ω
    simp only [stepSum, Finset.sum_apply]
  rw [hfun]
  exact he.trans hsum

/-- Conditional centering makes a square-integrable increment orthogonal
to every adapted square-integrable past vector in the actual weighted
pairing. This is derived from conditional pull-out, not assumed. -/
theorem conditional_zero_pairing (W : Z →L[ℝ] Z)
    (F : MeasurableSpace Ω) (hF : F ≤ mΩ) (X Y : Ω → Z)
    (hX : MemLp X 2 Q) (hY : MemLp Y 2 Q)
    (hXadapt : AEStronglyMeasurable[F] X Q)
    (hYmean : Q[Y | F] =ᵐ[Q] (0 : Ω → Z)) :
    (∫ ω, ⟪X ω, W (Y ω)⟫_ℝ ∂Q) = 0 := by
  let B : Z →L[ℝ] Z →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ Z) W
  have hp := condExp_bilin_of_aestronglyMeasurable_left (mΩ := mΩ) (μ := Q) (m := F) B
    hXadapt (pairing_integrable (mΩ := mΩ) Q W X Y hX hY) (hY.integrable (by norm_num))
  have hzero : Q[(fun ω => ⟪X ω, W (Y ω)⟫_ℝ) | F] =ᵐ[Q] (fun _ => (0 : ℝ)) := by
    filter_upwards [hp, hYmean] with ω hp hy
    simpa only [B, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply, hy, Pi.zero_apply, map_zero, inner_zero_right] using hp
  have he := integral_congr_ae hzero
  rw [integral_condExp hF, integral_zero] at he
  exact he

end Vector
section Canonical
variable [Fintype I] [DecidableEq I]

abbrev NoiseVector (I : Type*) := I → ℝ
abbrev NoisePath (I : Type*) := ℕ → NoiseVector I

def vectorLaw : Measure (NoiseVector I) := Measure.pi (fun _ => gaussianReal 0 1)
def pathLaw : Measure (NoisePath I) := Measure.infinitePi (fun _ => vectorLaw (I := I))

instance vectorLaw_probability : IsProbabilityMeasure (vectorLaw (I := I)) := by
  dsimp [vectorLaw]
  infer_instance
instance pathLaw_probability : IsProbabilityMeasure (pathLaw (I := I)) := by
  dsimp [pathLaw]
  infer_instance

def pastPrefix (n : ℕ) (w : NoisePath I) : Fin n → NoiseVector I := fun k => w k

theorem fresh_hasLaw (n : ℕ) :
    HasLaw (fun w : NoisePath I => w n) (vectorLaw (I := I)) (pathLaw (I := I)) where
  aemeasurable := (measurable_pi_apply n).aemeasurable
  map_eq := Measure.infinitePi_map_eval _ n

theorem coordinate_hasLaw (n : ℕ) (i : I) :
    HasLaw (fun w : NoisePath I => w n i) (gaussianReal 0 1) (pathLaw (I := I)) := by
  have hc := (measurePreserving_eval (fun _ : I => gaussianReal 0 1) i).hasLaw
  simpa only [Function.comp_def] using hc.comp (fresh_hasLaw (I := I) n)

theorem coordinate_independent (n : ℕ) :
    iIndepFun (fun i => fun w : NoisePath I => w n i) (pathLaw (I := I)) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (coordinate_hasLaw n i).aemeasurable)).mpr
  simp only [(coordinate_hasLaw n _).map_eq]
  exact (fresh_hasLaw (I := I) n).map_eq

/-- The complete current Gaussian vector is independent of every measurable
random coefficient formed from the strict finite past. -/
theorem fresh_independent_coefficient (n : ℕ)
    (A : (Fin n → NoiseVector I) → I → Z) (hA : Measurable A) :
    IndepFun (fun w : NoisePath I => fun i => w n i)
      (fun w i => A (pastPrefix n w) i) (pathLaw (I := I)) := by
  change IndepFun (fun w : NoisePath I => w n) (fun w => A (pastPrefix n w)) _
  unfold pastPrefix pathLaw
  exact (ULA.iid_prefix_independent_fresh (vectorLaw (I := I)) n).symm.comp measurable_id hA

/-- An actual canonical iid Gaussian path and arbitrary square-integrable
past-dependent coefficient columns satisfy the weighted one-step isometry.
All Gaussian laws and current/past independence are constructed. -/
theorem canonical_step_isometry (W : Z →L[ℝ] Z) (n : ℕ)
    (A : (Fin n → NoiseVector I) → I → Z) (hA : Measurable A)
    (hA2 : ∀ i, MemLp (fun w : NoisePath I => A (pastPrefix n w) i) 2 (pathLaw (I := I))) :
    (∫ w, ⟪(∑ i, w n i • A (pastPrefix n w) i),
      W (∑ i, w n i • A (pastPrefix n w) i)⟫_ℝ ∂pathLaw (I := I)) =
      ∑ i, ∫ w, ⟪A (pastPrefix n w) i, W (A (pastPrefix n w) i)⟫_ℝ ∂pathLaw (I := I) :=
  gaussian_step_isometry (pathLaw (I := I)) W _ _
    (coordinate_hasLaw n) (coordinate_independent n) hA2 (fresh_independent_coefficient n A hA)

/-- The actual strict-past filtration of the canonical Gaussian path. -/
def pastFiltration : Filtration ℕ (inferInstance : MeasurableSpace (NoisePath I)) where
  seq n := MeasurableSpace.comap (pastPrefix (I := I) n) inferInstance
  mono' := by
    intro n m hnm
    let restrict : (Fin m → NoiseVector I) → (Fin n → NoiseVector I) :=
      fun v i => v ⟨i.val, lt_of_lt_of_le i.isLt hnm⟩
    have hr : Measurable restrict := by fun_prop
    have hm : Measurable[MeasurableSpace.comap (pastPrefix (I := I) m) inferInstance]
        (pastPrefix m) := measurable_iff_comap_le.mpr le_rfl
    have hn : Measurable[MeasurableSpace.comap (pastPrefix (I := I) m) inferInstance]
        (pastPrefix n) := by
      change Measurable[MeasurableSpace.comap (pastPrefix (I := I) m) inferInstance]
        (fun w => fun i : Fin n => w i.val)
      exact hr.comp hm
    exact hn.comap_le
  le' n := (show Measurable (pastPrefix (I := I) n) from
    measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)).comap_le

theorem pastPrefix_measurable (n : ℕ) :
    Measurable[pastFiltration (I := I) n] (pastPrefix n) :=
  measurable_iff_comap_le.mpr le_rfl

theorem coefficient_adapted (n : ℕ) (A : (Fin n → NoiseVector I) → I → Z)
    (hA : Measurable A) (i : I) :
    StronglyMeasurable[pastFiltration (I := I) n] (fun w => A (pastPrefix n w) i) :=
  ((measurable_pi_apply i).comp (hA.comp (pastPrefix_measurable n))).stronglyMeasurable

theorem fresh_past_independent (n : ℕ) :
    Indep (MeasurableSpace.comap (fun w : NoisePath I => w n) inferInstance)
      (pastFiltration (I := I) n) (pathLaw (I := I)) := by
  exact (ULA.iid_prefix_independent_fresh (vectorLaw (I := I)) n).symm

/-- The predictable step is a genuine centered martingale increment on
the constructed Gaussian path and its strict-past filtration. -/
theorem canonical_step_condExp_zero (n : ℕ)
    (A : (Fin n → NoiseVector I) → I → Z) (hA : Measurable A)
    (hA2 : ∀ i, MemLp (fun w : NoisePath I => A (pastPrefix n w) i) 2 (pathLaw (I := I))) :
    (pathLaw (I := I))[(fun w => ∑ i, w n i • A (pastPrefix n w) i) |
      pastFiltration (I := I) n] =ᵐ[pathLaw (I := I)] (0 : NoisePath I → Z) := by
  apply independent_step_condExp_zero (pathLaw (I := I)) (pastFiltration n)
    ((pastFiltration (I := I)).le n) (fun i w => w n i)
    (fun i w => A (pastPrefix n w) i) (fun i => by fun_prop)
    (fun i => (coordinate_hasLaw n i).memLp (memLp_id_gaussianReal (2 : ℝ≥0))) hA2
    (coefficient_adapted n A hA) (fresh_independent_coefficient n A hA)
    (fresh_past_independent n)
  intro i
  exact ((coordinate_hasLaw n i).integral_comp (f := id) (by fun_prop)).trans integral_id_gaussianReal

/-- Every finite input prefix has exactly the finite product Gaussian law. -/
theorem pastPrefix_hasLaw (n : ℕ) :
    HasLaw (pastPrefix (I := I) n) (Measure.pi (fun _ : Fin n => vectorLaw (I := I)))
      (pathLaw (I := I)) where
  aemeasurable := (show Measurable (pastPrefix (I := I) n) from
    measurable_pi_iff.mpr (fun i => measurable_pi_apply i.val)).aemeasurable
  map_eq := by
    change (Measure.infinitePi (fun _ : ℕ => vectorLaw (I := I))).map
      (fun (w : NoisePath I) (i : Fin n) => w i.val) = _
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]

/-- Actual step with a coefficient determined solely by past innovations. -/
def predictableStep (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (n : ℕ) (w : NoisePath I) : Z := ∑ i, w n i • A n (pastPrefix n w) i

def predictableSum (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (n : ℕ) (w : NoisePath I) : Z := ∑ k : Fin n, predictableStep A k w

@[simp] theorem predictableSum_zero (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (w : NoisePath I) : predictableSum A 0 w = 0 := by simp [predictableSum]

theorem predictableSum_succ (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (n : ℕ) (w : NoisePath I) :
    predictableSum A (n + 1) w = predictableSum A n w + predictableStep A n w := by
  simp only [predictableSum, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem predictableStep_memLp (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (hA : ∀ n, Measurable (A n))
    (hA2 : ∀ n i, MemLp (fun w : NoisePath I => A n (pastPrefix n w) i) 2 (pathLaw (I := I)))
    (n : ℕ) : MemLp (predictableStep A n) 2 (pathLaw (I := I)) :=
  stepSum_memLp (pathLaw (I := I)) _ _
    (fun i => (coordinate_hasLaw n i).memLp (memLp_id_gaussianReal (2 : ℝ≥0)))
    (hA2 n) (fresh_independent_coefficient n (A n) (hA n))

theorem predictableSum_memLp (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (hA : ∀ n, Measurable (A n))
    (hA2 : ∀ n i, MemLp (fun w : NoisePath I => A n (pastPrefix n w) i) 2 (pathLaw (I := I)))
    (n : ℕ) : MemLp (predictableSum A n) 2 (pathLaw (I := I)) :=
  memLp_finsetSum Finset.univ (fun k _ => predictableStep_memLp A hA hA2 k)

theorem predictableStep_adapted (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (hA : ∀ n, Measurable (A n)) (n : ℕ) :
    StronglyMeasurable[pastFiltration (I := I) (n + 1)] (predictableStep A n) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have hξ : Measurable[pastFiltration (I := I) (n + 1)] (fun w : NoisePath I => w n i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply (Fin.last n)).comp
      (pastPrefix_measurable (n + 1)))
  exact hξ.stronglyMeasurable.smul ((coefficient_adapted n (A n) (hA n) i).mono
    ((pastFiltration (I := I)).mono (Nat.le_succ n)))

theorem predictableSum_adapted (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (hA : ∀ n, Measurable (A n)) :
    StronglyAdapted (pastFiltration (I := I)) (predictableSum A) := by
  intro n
  apply Finset.stronglyMeasurable_fun_sum
  intro k _
  exact (predictableStep_adapted A hA k).mono
    ((pastFiltration (I := I)).mono (Nat.succ_le_of_lt k.isLt))

/-- The finite sums of the actual predictable Gaussian increments form
an actual martingale, derived from independent future innovations. -/
theorem predictableSum_martingale (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (hA : ∀ n, Measurable (A n))
    (hA2 : ∀ n i, MemLp (fun w : NoisePath I => A n (pastPrefix n w) i) 2 (pathLaw (I := I))) :
    Martingale (predictableSum A) (pastFiltration (I := I)) (pathLaw (I := I)) := by
  apply martingale_of_condExp_sub_eq_zero_nat (predictableSum_adapted A hA)
    (fun n => (predictableSum_memLp A hA hA2 n).integrable (by norm_num))
  intro n
  have heq : predictableSum A (n + 1) - predictableSum A n = predictableStep A n := by
    funext w
    simp only [Pi.sub_apply, predictableSum_succ, add_sub_cancel_left]
  rw [heq]
  exact canonical_step_condExp_zero n (A n) (hA n) (hA2 n)

/-- The accumulated actual predictable Gaussian martingale satisfies its
exact weighted finite-sum Itô isometry. The coefficient maps may be
nonlinear functions of every past innovation. -/
theorem predictableSum_isometry (W : Z →L[ℝ] Z)
    (hW : ∀ z w, ⟪z, W w⟫_ℝ = ⟪W z, w⟫_ℝ)
    (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (hA : ∀ n, Measurable (A n))
    (hA2 : ∀ n i, MemLp (fun w : NoisePath I => A n (pastPrefix n w) i) 2 (pathLaw (I := I)))
    (n : ℕ) :
    (∫ w, ⟪predictableSum A n w, W (predictableSum A n w)⟫_ℝ ∂pathLaw (I := I)) =
      ∑ k : Fin n, ∑ i, ∫ w, ⟪A k (pastPrefix k w) i,
        W (A k (pastPrefix k w) i)⟫_ℝ ∂pathLaw (I := I) := by
  induction n with
  | zero => simp only [predictableSum_zero, inner_zero_left, integral_zero, Finset.univ_eq_empty,
      Finset.sum_empty]
  | succ n ih =>
    have hSn := predictableSum_memLp A hA hA2 n
    have hYn := predictableStep_memLp A hA hA2 n
    have hcross := conditional_zero_pairing (pathLaw (I := I)) W (pastFiltration n)
      ((pastFiltration (I := I)).le n) (predictableSum A n) (predictableStep A n)
      hSn hYn (predictableSum_adapted A hA n).aestronglyMeasurable
      (canonical_step_condExp_zero n (A n) (hA n) (hA2 n))
    have hstep := canonical_step_isometry W n (A n) (hA n) (hA2 n)
    have hpoint : (fun w => ⟪predictableSum A (n + 1) w, W (predictableSum A (n + 1) w)⟫_ℝ) =
        (fun w => ⟪predictableSum A n w, W (predictableSum A n w)⟫_ℝ +
          2 * ⟪predictableSum A n w, W (predictableStep A n w)⟫_ℝ +
          ⟪predictableStep A n w, W (predictableStep A n w)⟫_ℝ) := by
      funext w
      rw [predictableSum_succ]
      simp only [map_add, inner_add_left, inner_add_right]
      have hsym : ⟪predictableStep A n w, W (predictableSum A n w)⟫_ℝ =
          ⟪predictableSum A n w, W (predictableStep A n w)⟫_ℝ :=
        (real_inner_comm _ _).trans (hW _ _).symm
      rw [hsym]
      ring
    have h00 := pairing_integrable (pathLaw (I := I)) W _ _ hSn hSn
    have h01 := (pairing_integrable (pathLaw (I := I)) W _ _ hSn hYn).const_mul 2
    have h11 := pairing_integrable (pathLaw (I := I)) W _ _ hYn hYn
    have hint1 := integral_add (h00.add h01) h11
    have hint2 := integral_add h00 h01
    simp only [Pi.add_apply] at hint1 hint2
    rw [hpoint, hint1, hint2, integral_const_mul, hcross, mul_zero, add_zero, ih]
    change _ + (∫ w, ⟪(∑ i, w n i • A n (pastPrefix n w) i),
      W (∑ i, w n i • A n (pastPrefix n w) i)⟫_ℝ ∂pathLaw (I := I)) = _
    rw [hstep, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]

/-- Exact L² norm of the constructed predictable sum. -/
theorem predictableSum_norm_sq
    (A : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (hA : ∀ n, Measurable (A n))
    (hA2 : ∀ n i, MemLp (fun w : NoisePath I => A n (pastPrefix n w) i) 2 (pathLaw (I := I)))
    (n : ℕ) :
    ‖(predictableSum_memLp A hA hA2 n).toLp (predictableSum A n)‖ ^ 2 =
      ∑ k : Fin n, ∑ i, ∫ w, ‖A k (pastPrefix k w) i‖ ^ 2 ∂pathLaw (I := I) := by
  let hS := predictableSum_memLp A hA hA2 n
  rw [ProximalLangevin.lp_norm_sq_eq_integral]
  have he : (∫ w, ‖hS.toLp (predictableSum A n) w‖ ^ 2 ∂pathLaw (I := I)) =
      ∫ w, ‖predictableSum A n w‖ ^ 2 ∂pathLaw (I := I) :=
    integral_congr_ae (hS.coeFn_toLp.fun_comp (fun z : Z => ‖z‖ ^ 2))
  rw [he]
  simpa only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
    predictableSum_isometry (ContinuousLinearMap.id ℝ Z) (fun _ _ => rfl) A hA hA2 n

theorem predictableSum_sub
    (A B : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z) (n : ℕ) (w : NoisePath I) :
    predictableSum (fun k p i => A k p i - B k p i) n w =
      predictableSum A n w - predictableSum B n w := by
  simp only [predictableSum, predictableStep, smul_sub, Finset.sum_sub_distrib]

/-- The L² distance of two predictable integrals is exactly the coefficient
L² distance. This gives the Cauchy estimate needed for completion. -/
theorem predictableSum_distance_sq
    (A B : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z)
    (hA : ∀ n, Measurable (A n)) (hB : ∀ n, Measurable (B n))
    (hA2 : ∀ n i, MemLp (fun w : NoisePath I => A n (pastPrefix n w) i) 2 (pathLaw (I := I)))
    (hB2 : ∀ n i, MemLp (fun w : NoisePath I => B n (pastPrefix n w) i) 2 (pathLaw (I := I)))
    (n : ℕ) :
    ‖(predictableSum_memLp A hA hA2 n).toLp (predictableSum A n) -
      (predictableSum_memLp B hB hB2 n).toLp (predictableSum B n)‖ ^ 2 =
      ∑ k : Fin n, ∑ i, ∫ w, ‖A k (pastPrefix k w) i - B k (pastPrefix k w) i‖ ^ 2
        ∂pathLaw (I := I) := by
  let C : ∀ n : ℕ, (Fin n → NoiseVector I) → I → Z := fun k p i => A k p i - B k p i
  have hC (k : ℕ) : Measurable (C k) := (hA k).sub (hB k)
  have hC2 (k : ℕ) (i : I) : MemLp
      (fun w : NoisePath I => C k (pastPrefix k w) i) 2 (pathLaw (I := I)) :=
    (hA2 k i).sub (hB2 k i)
  let hSA := predictableSum_memLp A hA hA2 n
  let hSB := predictableSum_memLp B hB hB2 n
  let hSC := predictableSum_memLp C hC hC2 n
  have hLp : hSC.toLp (predictableSum C n) =
      hSA.toLp (predictableSum A n) - hSB.toLp (predictableSum B n) := by
    apply Lp.ext
    filter_upwards [hSC.coeFn_toLp, hSA.coeFn_toLp, hSB.coeFn_toLp,
      Lp.coeFn_sub (hSA.toLp (predictableSum A n)) (hSB.toLp (predictableSum B n))]
      with w hc ha hb hs
    rw [hs, Pi.sub_apply, hc, ha, hb]
    exact predictableSum_sub A B n w
  rw [← hLp]
  exact predictableSum_norm_sq C hC hC2 n

end Canonical
end PBGSO.PredictableIsometry
