import ProximalLangevin.MeanFieldDrift
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false

/-! # Exact empirical variance for independent mean-field copies

Exchangeability alone does not cancel the off-diagonal covariances. This
module constructs the iid copies on the actual finite product probability
space and proves the exact `1/N` centered second-moment identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators RealInnerProductSpace
namespace ProximalLangevin

section HilbertVariance
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  (P : Measure Ω) [IsProbabilityMeasure P]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] in
/-- Every inner product of two L² random variables is integrable. -/
theorem integrable_inner_of_memLp {X Y : Ω → E}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    Integrable (fun ω => ⟪X ω,Y ω⟫) P := by
  have h := L2.integrable_inner (𝕜 := ℝ) (hX.toLp X) (hY.toLp Y)
  apply h.congr
  filter_upwards [hX.coeFn_toLp,hY.coeFn_toLp] with ω hx hy
  rw [hx,hy]

/-- Centered independent Hilbert-valued samples have exactly additive
second moments. Independence is used for each mixed term. -/
theorem integral_norm_sum_sq_centered_independent
    {ι : Type*} [Fintype ι] (X : ι → Ω → E)
    (hX : ∀ i, MemLp (X i) 2 P) (hind : iIndepFun X P)
    (hmean : ∀ i, (∫ ω,X i ω ∂P)=0) :
    (∫ ω, ‖∑ i, X i ω‖^2 ∂P) = ∑ i, ∫ ω, ‖X i ω‖^2 ∂P := by
  classical
  have hint (i j : ι) := integrable_inner_of_memLp P (hX i) (hX j)
  have hcross (i j : ι) :
      (∫ ω,⟪X i ω,X j ω⟫ ∂P) = if i=j then ∫ ω,‖X i ω‖^2 ∂P else 0 := by
    by_cases hij : i=j
    · subst j
      simp only [ite_true, real_inner_self_eq_norm_sq]
    · have h := (hind.indepFun hij).integral_bilin
        ((hX i).integrable (by norm_num : (1 : ENNReal) ≤ 2))
        ((hX j).integrable (by norm_num : (1 : ENNReal) ≤ 2)) (innerSL ℝ)
      change (∫ ω,⟪X i ω,X j ω⟫ ∂P)=⟪∫ ω,X i ω ∂P,∫ ω,X j ω ∂P⟫ at h
      simpa only [hmean, inner_zero_left, ite_eq_right hij] using h
  have hexpand (ω : Ω) : ‖∑ i,X i ω‖^2 = ∑ i,∑ j,⟪X i ω,X j ω⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum]
    exact Finset.sum_comm
  simp_rw [hexpand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j),hcross]
  simp

end HilbertVariance

/-- The empirical mean on the explicitly specified finite sample space. -/
def empiricalAverage {N : ℕ} {A E : Type*} [AddCommMonoid E] [Module ℝ E]
    (φ : A → E) (x : Fin N → A) : E := (N : ℝ)⁻¹ • ∑ i,φ (x i)

section ProductVariance
variable {A E : Type*} [MeasurableSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure A) [IsProbabilityMeasure μ] (φ : A → E) (hφ : MemLp φ 2 μ)

include hφ

/-- The actual iid finite product gives the exact centered empirical variance.
All moments are Bochner integrals, including the mean used for centering. -/
theorem iid_empirical_variance {N : ℕ} (hN : 0<N) :
    (∫ x : Fin N → A, ‖empiricalAverage φ x-(∫ a,φ a ∂μ)‖^2
      ∂Measure.pi (fun _ : Fin N => μ)) =
      (∫ a,‖φ a-(∫ b,φ b ∂μ)‖^2 ∂μ)/(N : ℝ) := by
  classical
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  let C := fun a => φ a-(∫ b,φ b ∂μ)
  have hC : MemLp C 2 μ := hφ.sub (memLp_const _)
  have hCm : (∫ a,C a ∂μ)=0 := by
    dsimp [C]
    rw [integral_sub (hφ.integrable (by norm_num)) (integrable_const _),
      integral_const,probReal_univ,one_smul,sub_self]
  let P := Measure.pi (fun _ : Fin N => μ)
  let X := fun (i : Fin N) (x : Fin N → A) => C (x i)
  have hXi (i : Fin N) : MemLp (X i) 2 P :=
    hC.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hind : iIndepFun X P := iIndepFun_pi (fun _ => hC.aemeasurable)
  have hmean (i : Fin N) : (∫ x,X i x ∂P)=0 := by
    have hh := integral_map (μ := P) (φ := fun x : Fin N → A => x i)
      (measurable_pi_apply i).aemeasurable
      (show AEStronglyMeasurable C (P.map (fun x => x i)) from by
        rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq]
        exact hC.aestronglyMeasurable)
    rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq,hCm] at hh
    exact hh.symm
  have hvar (i : Fin N) : (∫ x,‖X i x‖^2 ∂P)=∫ a,‖C a‖^2 ∂μ := by
    have hh := integral_map (μ := P) (φ := fun x : Fin N → A => x i)
      (measurable_pi_apply i).aemeasurable
      (show AEStronglyMeasurable (fun a => ‖C a‖^2) (P.map (fun x => x i)) from by
        rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq]
        exact hC.aestronglyMeasurable.norm.pow 2)
    rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq] at hh
    exact hh.symm
  have hsum := integral_norm_sum_sq_centered_independent P X hXi hind hmean
  have hid (x : Fin N → A) : empiricalAverage φ x-(∫ a,φ a ∂μ) =
      (N : ℝ)⁻¹ • ∑ i,X i x := by
    dsimp [empiricalAverage,X,C]
    rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ,smul_sub,smul_smul,inv_mul_cancel₀ hn,one_smul]
  simp_rw [hid,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [integral_const_mul,hsum]
  simp_rw [hvar]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change (N : ℝ)⁻¹^2*((N : ℝ)*(∫ a,‖C a‖^2 ∂μ))=(∫ a,‖C a‖^2 ∂μ)/(N : ℝ)
  field_simp

/-- The same exact identity written as an RMS sampling error. -/
theorem iid_empirical_rms {N : ℕ} (hN : 0<N) :
    Real.sqrt (∫ x : Fin N → A,‖empiricalAverage φ x-(∫ a,φ a ∂μ)‖^2
      ∂Measure.pi (fun _ : Fin N => μ)) =
    Real.sqrt (∫ a,‖φ a-(∫ b,φ b ∂μ)‖^2 ∂μ)/Real.sqrt (N : ℝ) := by
  rw [iid_empirical_variance μ φ hφ hN,Real.sqrt_div (integral_nonneg fun _ => sq_nonneg _)]

end ProductVariance

/-- Exact iid empirical parameter-gradient variance for the actual joint
potential. The copies are independent under the displayed finite product. -/
theorem iid_parameterGradient_variance {N dθ dx : ℕ} (hN : 0<N)
    {U : IPLA.Joint dθ dx → ℝ} {L : ℝ≥0} (hLip : LipschitzWith L (gradient U))
    (θ : EuclideanSpace ℝ (Fin dθ))
    (μ : Measure (EuclideanSpace ℝ (Fin dx))) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x => x) 2 μ) :
    (∫ x : Fin N → EuclideanSpace ℝ (Fin dx),
      ‖empiricalAverage (parameterGradient U θ) x-meanFieldDrift U θ μ‖^2
      ∂Measure.pi (fun _ : Fin N => μ)) =
      (∫ x,‖parameterGradient U θ x-meanFieldDrift U θ μ‖^2 ∂μ)/(N : ℝ) := by
  exact iid_empirical_variance μ (parameterGradient U θ)
    (memLp_lipschitz_observable μ (parameterGradient_latent_lipschitz hLip θ) hμ) hN

end ProximalLangevin
