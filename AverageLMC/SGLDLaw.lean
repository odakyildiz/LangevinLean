import AverageLMC.SGLDEstimator
import AverageLMC.CenteredPerturbation
import UnadjustedLangevin.LSI.GaussianDrift

set_option linter.style.header false
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace AverageLMC

/-- The exact fixed-point-control-variate SGLD update. -/
def sgldProposal {p n : ℕ} (f : Fin n → State p → ℝ) (anchor : State p)
    (h : ℝ) (x z : State p) (i : Fin n) : State p :=
  x - h • controlVariateEstimator f anchor x i + Real.sqrt (2 * h) • z

/-- Its transition law uses independent initialization, standard Gaussian
innovation and uniform component index. -/
def sgldLawStep {p n : ℕ} (f : Fin n → State p → ℝ) (anchor : State p)
    (h : ℝ) (μ : Measure (State p)) : Measure (State p) :=
  ((μ.prod (stdGaussian (State p))).prod (uniformIndexLaw n)).map
    (fun q ↦ sgldProposal f anchor h q.1.1 q.1.2 q.2)

/-- The actual SGLD chain's marginal laws. Fresh independent Gaussian and
index innovations are used at each transition. -/
def sgldLaws {p n : ℕ} (f : Fin n → State p → ℝ) (anchor : State p)
    (h : ℝ) (μ : Measure (State p)) : ℕ → Measure (State p)
  | 0 => μ
  | k + 1 => sgldLawStep f anchor h (sgldLaws f anchor h μ k)

theorem sgldProposal_eq_full_gradient {p n : ℕ} (f : Fin n → State p → ℝ)
    (anchor x z : State p) (h : ℝ) (i : Fin n) :
    sgldProposal f anchor h x z i = ULA.malaProposal (componentPotential f) h x z +
      (-h) • controlVariateError f anchor x i := by
  simp only [sgldProposal, ULA.malaProposal, controlVariateError, smul_sub, neg_smul]
  module

theorem sgldProposal_measurable {p n : ℕ} (f : Fin n → State p → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (L : Fin n → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (M : ℝ≥0) (hfull : LipschitzWith M (gradient (componentPotential f)))
    (anchor : State p) (h : ℝ) :
    Measurable (fun q : (State p × State p) × Fin n ↦
      sgldProposal f anchor h q.1.1 q.1.2 q.2) := by
  simp_rw [sgldProposal_eq_full_gradient]
  exact ((ULA.malaProposal_measurable (componentPotential f) h M hfull).comp measurable_fst).add
    ((controlVariateError_product_measurable f hf L hLip anchor Prod.fst measurable_fst).const_smul (-h))

theorem sgldLawStep_isProbability {p n : ℕ} (hn : 0 < n)
    (f : Fin n → State p → ℝ) (_hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (_hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (M : ℝ≥0) (_hfull : LipschitzWith M (gradient (componentPotential f)))
    (anchor : State p) (h : ℝ) (μ : Measure (State p)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (sgldLawStep f anchor h μ) := by
  have := uniformIndexLaw_probability n hn
  unfold sgldLawStep
  infer_instance

instance sgldLawStep_probability {p n : ℕ} [NeZero n]
    (f : Fin n → State p → ℝ) (anchor : State p) (h : ℝ)
    (μ : Measure (State p)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (sgldLawStep f anchor h μ) := by
  have := uniformIndexLaw_probability n (Nat.pos_of_ne_zero (NeZero.ne n))
  unfold sgldLawStep
  infer_instance

instance sgldLaws_probability {p n : ℕ} [NeZero n]
    (f : Fin n → State p → ℝ) (anchor : State p) (h : ℝ)
    (μ : Measure (State p)) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (sgldLaws f anchor h μ k) := by
  induction k with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ k ih => exact sgldLawStep_probability f anchor h _

/-- A full-gradient proposal has a derived second moment on the actual
independent Gaussian input space. -/
theorem full_gradient_proposal_memLp {p : ℕ} (F : State p → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient F)) (h : ℝ)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : State p ↦ x) 2 μ) :
    MemLp (fun q : State p × State p ↦ ULA.malaProposal F h q.1 q.2)
      2 (μ.prod (stdGaussian (State p))) := by
  have hX : MemLp (fun q : State p × State p ↦ q.1) 2 (μ.prod (stdGaussian (State p))) :=
    hμ.comp_fst _
  have hg := ULA.lpDrift_memLp (μ.prod (stdGaussian (State p))) (gradient F) hLip (hX.toLp _)
  have hg' : MemLp (fun q : State p × State p ↦ gradient F q.1) 2
      (μ.prod (stdGaussian (State p))) := by
    apply hg.ae_eq
    filter_upwards [hX.coeFn_toLp] with q hq
    rw [hq]
  have hZ := (IsGaussian.memLp_id (stdGaussian (State p)) 2 (by norm_num)).comp_snd μ
  exact (hX.sub (hg'.const_smul h)).add (hZ.const_smul (Real.sqrt (2 * h)))

/-- Exact variance-addition estimate for the genuine SGLD transition.
The coupling lift is constructed by disintegration, and its cross term is
zero by the proved unbiasedness of the finite-index estimator. -/
theorem sgld_variance_addition {p n : ℕ} (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (M : ℝ≥0) (hfull : LipschitzWith M (gradient (componentPotential f)))
    (anchor : State p) (hstar : gradient (componentPotential f) anchor = 0)
    (h : ℝ) (μ π : Measure (State p)) [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hμ : MemLp (fun x : State p ↦ x) 2 μ) (hπ : MemLp (fun x : State p ↦ x) 2 π) :
    ULA.wasserstein2Real (sgldLawStep f anchor h μ) π ^ 2 ≤
      ULA.wasserstein2Real (ULA.ulaLawStep (componentPotential f) h μ) π ^ 2 +
        h ^ 2 * ∫ q : (State p × State p) × Fin n,
          ‖controlVariateError f anchor q.1.1 q.2‖ ^ 2
            ∂(μ.prod (stdGaussian (State p))).prod (uniformIndexLaw n) := by
  have := uniformIndexLaw_probability n hn
  let P := μ.prod (stdGaussian (State p))
  let X : State p × State p → State p := Prod.fst
  have hX : MemLp X 2 P := hμ.comp_fst _
  let D := fun q : State p × State p ↦ fun i : Fin n ↦
    (-h) • controlVariateError f anchor q.1 i
  have hD : Measurable (Function.uncurry D) :=
    (controlVariateError_product_measurable f hf L hLip anchor X measurable_fst).const_smul (-h)
  have hD2 : MemLp (Function.uncurry D) 2 (P.prod (uniformIndexLaw n)) :=
    (controlVariateError_product_memLp P f hf L hLip anchor X hX).const_smul (-h)
  have hmean (q : State p × State p) : (∫ i, D q i ∂uniformIndexLaw n) = 0 := by
    dsimp [D]
    rw [integral_smul, controlVariateError_centered hn f hf anchor hstar, smul_zero]
  have hw := wasserstein2_sq_centered_perturbation P (uniformIndexLaw n)
    (fun q ↦ ULA.malaProposal (componentPotential f) h q.1 q.2)
    (ULA.malaProposal_measurable _ h M hfull)
    (full_gradient_proposal_memLp _ M hfull h μ hμ)
    D hD hD2 (fun _ ↦ Integrable.of_finite) hmean π hπ
  have hmap : (P.prod (uniformIndexLaw n)).map
      (fun q ↦ ULA.malaProposal (componentPotential f) h q.1.1 q.1.2 + D q.1 q.2) =
      sgldLawStep f anchor h μ := by
    apply congrArg (Measure.map · (P.prod (uniformIndexLaw n)))
    funext q
    exact (sgldProposal_eq_full_gradient f anchor q.1.1 q.1.2 h q.2).symm
  rw [hmap] at hw
  have hvariance : (∫ q : (State p × State p) × Fin n, ‖D q.1 q.2‖ ^ 2
      ∂P.prod (uniformIndexLaw n)) = h ^ 2 *
      ∫ q : (State p × State p) × Fin n, ‖controlVariateError f anchor q.1.1 q.2‖ ^ 2
        ∂P.prod (uniformIndexLaw n) := by
    simp only [D, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
    exact integral_const_mul _ _
  simpa only [hvariance, P, ULA.ulaLawStep] using hw

/-- Lipschitz scores preserve the second moment of any input law. -/
theorem gradient_memLp {p : ℕ} (F : State p → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient F))
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : State p ↦ x) 2 μ) : MemLp (gradient F) 2 μ := by
  have hg := ULA.lpDrift_memLp μ (gradient F) hLip (hμ.toLp _)
  apply hg.ae_eq
  filter_upwards [hμ.coeFn_toLp] with x hx
  rw [hx]

/-- The actual SGLD law has a finite second moment, derived from its input. -/
theorem sgldLawStep_memLp {p n : ℕ}
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (M : ℝ≥0) (hfull : LipschitzWith M (gradient (componentPotential f)))
    (anchor : State p) (h : ℝ) (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : State p ↦ x) 2 μ) :
    MemLp (fun x : State p ↦ x) 2 (sgldLawStep f anchor h μ) := by
  let P := μ.prod (stdGaussian (State p))
  have hX : MemLp (fun q : State p × State p ↦ q.1) 2 P := hμ.comp_fst _
  have hd := (controlVariateError_product_memLp P f hf L hLip anchor Prod.fst hX).const_smul (-h)
  have hg := (full_gradient_proposal_memLp _ M hfull h μ hμ).comp_fst (uniformIndexLaw n)
  apply (memLp_map_measure_iff (by fun_prop)
    (sgldProposal_measurable f hf L hLip M hfull anchor h).aemeasurable).mpr
  simpa only [Function.comp_def, sgldProposal_eq_full_gradient, Pi.add_def, Pi.smul_def]
    using hg.add hd

/-- Fubini's theorem removes the unused Gaussian innovation from the exact
stochastic-gradient variance. -/
theorem sgld_error_variance_identity {p n : ℕ} (hn : 0 < n)
    (f : Fin n → State p → ℝ) (hf : ∀ i, Differentiable ℝ (f i))
    (L : Fin n → ℝ≥0) (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (M : ℝ≥0) (hfull : LipschitzWith M (gradient (componentPotential f)))
    (anchor : State p) (hstar : gradient (componentPotential f) anchor = 0)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : State p ↦ x) 2 μ) :
    (∫ q : (State p × State p) × Fin n,
      ‖controlVariateError f anchor q.1.1 q.2‖ ^ 2
        ∂(μ.prod (stdGaussian (State p))).prod (uniformIndexLaw n)) =
    (∫ q : State p × Fin n, ‖controlVariateEstimator f anchor q.1 q.2‖ ^ 2
      ∂μ.prod (uniformIndexLaw n)) - ∫ x, ‖gradient (componentPotential f) x‖ ^ 2 ∂μ := by
  have := uniformIndexLaw_probability n hn
  let P := μ.prod (stdGaussian (State p))
  have hX : MemLp (fun q : State p × State p ↦ q.1) 2 P := hμ.comp_fst _
  have he := (controlVariateError_product_memLp P f hf L hLip anchor Prod.fst hX).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have hs := (controlVariateEstimator_product_memLp μ f L hLip anchor id hμ).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  simp only [id_eq] at hs
  have hg := (gradient_memLp _ M hfull μ hμ).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [integral_prod _ he]
  simp_rw [controlVariateError_second_moment hn f hf anchor hstar]
  have hi : Integrable (fun x ↦
      (∫ i, ‖controlVariateEstimator f anchor x i‖ ^ 2 ∂uniformIndexLaw n) -
        ‖gradient (componentPotential f) x‖ ^ 2) μ := hs.integral_prod_left.sub hg
  rw [integral_prod _ (hi.comp_fst (stdGaussian (State p)))]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_sub hs.integral_prod_left hg, ← integral_prod _ hs]

/-- The integrated estimator energy is exactly the n-weighted sum of the
component gradient increments in Proposition 3's first claim. -/
theorem integral_controlVariateEstimator_sq {p n : ℕ} (hn : 0 < n)
    (f : Fin n → State p → ℝ) (L : Fin n → ℝ≥0)
    (hLip : ∀ i, LipschitzWith (L i) (gradient (f i)))
    (anchor : State p) (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hμ : MemLp (fun x : State p ↦ x) 2 μ) :
    (∫ q : State p × Fin n, ‖controlVariateEstimator f anchor q.1 q.2‖ ^ 2
      ∂μ.prod (uniformIndexLaw n)) =
      (n : ℝ) * ∑ i, ∫ x, ‖gradient (f i) x - gradient (f i) anchor‖ ^ 2 ∂μ := by
  have he := (controlVariateEstimator_product_memLp μ f L hLip anchor id hμ).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  simp only [id_eq] at he
  have hi (i : Fin n) : Integrable (fun x ↦ ‖gradient (f i) x - gradient (f i) anchor‖ ^ 2) μ :=
    ((gradient_memLp (f i) (L i) (hLip i) μ hμ).sub (memLp_const _)).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)
  rw [integral_prod _ he]
  simp_rw [controlVariateEstimator_second_moment hn]
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ ↦ hi i)]

end AverageLMC
