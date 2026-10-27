import LatentDiffusion.RegularVariational
import LatentDiffusion.Marginal

set_option linter.style.header false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace LatentDiffusion.RegularModel

variable {dθ dz M : ℕ}

def latentInsert : EuclideanSpace ℝ (Fin dz) →L[ℝ] IPLA.Joint dθ dz :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ IPLA.pair 0 z
      map_add' := by intro x y; ext j; cases j <;> simp [IPLA.pair]
      map_smul' := by intro c x; ext j; cases j <;> simp [IPLA.pair] }

theorem slice_differentiable (U : IPLA.Joint dθ dz → ℝ)
    (hU : Differentiable ℝ U) (a : EuclideanSpace ℝ (Fin dθ)) :
    Differentiable ℝ (fun z ↦ U (IPLA.pair a z)) := by
  have hp : (fun z : EuclideanSpace ℝ (Fin dz) ↦ IPLA.pair a z) =
      fun z ↦ IPLA.pair a 0 + latentInsert z := by
    funext z
    ext j
    cases j <;> simp [IPLA.pair, latentInsert]
  rw [show (fun z ↦ U (IPLA.pair a z)) = U ∘ (fun z ↦ IPLA.pair a z) from rfl, hp]
  exact hU.comp (latentInsert.differentiable.const_add (IPLA.pair a 0))

theorem slice_strongConvex (U : IPLA.Joint dθ dz → ℝ) (m : ℝ)
    (hU : StrongConvexOn univ m U) (a : EuclideanSpace ℝ (Fin dθ)) :
    StrongConvexOn univ m (fun z ↦ U (IPLA.pair a z)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy r s hr hs hrs
  have h := hU.2 (mem_univ (IPLA.pair a x)) (mem_univ (IPLA.pair a y)) hr hs hrs
  have ha : r • a + s • a = a := by rw [← add_smul, hrs, one_smul]
  rw [← IPLA.pair_affine, ha, IPLA.pair_sub] at h
  dsimp only at h
  rw [IPLA.norm_pair_sq] at h
  simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using h

/-- The source density model is constructed from the original potentials.
Normalization and existence of the posterior are consequences of A3. -/
def densityModel (U : Fin M → IPLA.Joint dθ dz → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ m (U i)) :
    RegularVariational.DensityModel (EuclideanSpace ℝ (Fin dθ))
      (EuclideanSpace ℝ (Fin dz)) M volume where
  density a i z := Real.exp (-U i (IPLA.pair a z))
  measurable a i := (Real.continuous_exp.comp
    ((slice_differentiable (U i) (hdiff i) a).continuous.neg)).measurable
  positive _ _ _ := Real.exp_pos _
  integrable a i := IPLA.integrable_marginal_weight (U i) m hm (hdiff i) (hsc i) a
  mass_positive a i := IPLA.marginalIntegral_pos (U i) m hm (hdiff i) (hsc i) a

theorem densityModel_logEvidence (U : Fin M → IPLA.Joint dθ dz → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ m (U i)) (a : EuclideanSpace ℝ (Fin dθ)) :
    (densityModel U m hm hdiff hsc).family.logEvidence a = -averageMarginalPotential U a := by
  simp only [RegularVariational.DensityModel.family, densityModel,
    RegularVariational.DensityModel.mass, averageMarginalPotential,
    IPLA.marginalPotential, IPLA.marginalIntegral, Finset.sum_neg_distrib, mul_neg, neg_neg]

/-- Actual heterogeneous posterior normalization and evidence identification
are constructed, rather than supplied as an abstract family interpretation. -/
theorem existsUnique_variationalOptimizer (U : Fin M → IPLA.Joint dθ dz → ℝ)
    (hM : 0 < M) (m : ℝ) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ m (U i)) :
    ∃! p : EuclideanSpace ℝ (Fin dθ) ×
        (Fin M → ProbabilityMeasure (EuclideanSpace ℝ (Fin dz))),
      (densityModel U m hm hdiff hsc).family.IsGlobalMin p.1 p.2 :=
  LatentDiffusion.existsUnique_variationalOptimizer U hM m hm hdiff hsc
    (densityModel U m hm hdiff hsc).family (densityModel_logEvidence U m hm hdiff hsc)

/-- Every posterior lies in the source P₂ domain, derived from joint strong
convexity and not added as an independent moment hypothesis. -/
theorem posterior_memLp (U : Fin M → IPLA.Joint dθ dz → ℝ) (m : ℝ) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ m (U i)) (a : EuclideanSpace ℝ (Fin dθ)) (i : Fin M) :
    MemLp (fun z : EuclideanSpace ℝ (Fin dz) ↦ z) 2
      ((densityModel U m hm hdiff hsc).posterior a i : Measure _) := by
  let V : EuclideanSpace ℝ (Fin dz) → ℝ := fun z ↦ U i (IPLA.pair a z)
  have hdiffV := slice_differentiable (U i) (hdiff i) a
  have hscV := slice_strongConvex (U i) m (hsc i) a
  have hid : ((densityModel U m hm hdiff hsc).posterior a i : Measure _) = ULA.gibbsMeasure V := by
    simp only [RegularVariational.DensityModel.posterior, densityModel,
      RegularVariational.DensityModel.mass, Density.posteriorMeasure, Density.densityMeasure,
      ULA.gibbsMeasure, ULA.gibbsPartition, ULA.gibbsWeight]
    rw [← withDensity_smul _ (show Measurable (ULA.gibbsWeight V) from
      (Real.continuous_exp.comp hdiffV.continuous.neg).measurable.ennreal_ofReal)]
    apply withDensity_congr_ae
    refine ae_of_all _ fun z ↦ ?_
    have hZ : 0 < ∫ z, Real.exp (-U i (IPLA.pair a z)) :=
      IPLA.marginalIntegral_pos (U i) m hm (hdiff i) (hsc i) a
    change ENNReal.ofReal (Real.exp (-U i (IPLA.pair a z)) / ∫ z, Real.exp (-U i (IPLA.pair a z))) = _
    rw [ENNReal.ofReal_div_of_pos hZ]
    have hmass := ofReal_integral_eq_lintegral_ofReal
      (IPLA.integrable_marginal_weight (U i) m hm (hdiff i) (hsc i) a)
      (ae_of_all _ fun z ↦ (Real.exp_pos _).le)
    rw [hmass]
    simp only [V, ULA.gibbsWeight, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [hid]
  exact ULA.memLp_id_gibbsMeasure V m hm hdiffV hscV

/-- The source optimizer theorem on its actual P₂ and finite-KL domain, using
the literal density integral and posteriors constructed from the potentials. -/
theorem existsUnique_p2_literalOptimizer (U : Fin M → IPLA.Joint dθ dz → ℝ)
    (hM : 0 < M) (m : ℝ) (hm : 0 < m)
    (hdiff : ∀ i, Differentiable ℝ (U i))
    (hsc : ∀ i, StrongConvexOn univ m (U i)) :
    let D := densityModel U m hm hdiff hsc
    ∃! p : EuclideanSpace ℝ (Fin dθ) ×
        (Fin M → ProbabilityMeasure (EuclideanSpace ℝ (Fin dz))),
      D.family.Admissible p.1 p.2 ∧
      (∀ i, MemLp (fun z : EuclideanSpace ℝ (Fin dz) ↦ z) 2 (p.2 i : Measure _)) ∧
      ∀ b q, D.family.Admissible b q →
        (∀ i, MemLp (fun z : EuclideanSpace ℝ (Fin dz) ↦ z) 2 (q i : Measure _)) →
        D.literalEnergy p.1 p.2 ≤ D.literalEnergy b q := by
  let D := densityModel U m hm hdiff hsc
  let domain := fun q : Fin M → ProbabilityMeasure (EuclideanSpace ℝ (Fin dz)) ↦
    ∀ i, MemLp (fun z : EuclideanSpace ℝ (Fin dz) ↦ z) 2 (q i : Measure _)
  have hpost : ∀ a, domain (D.posterior a) := fun a i ↦ posterior_memLp U m hm hdiff hsc a i
  have heq (p : EuclideanSpace ℝ (Fin dθ) ×
      (Fin M → ProbabilityMeasure (EuclideanSpace ℝ (Fin dz)))) :
      (D.family.Admissible p.1 p.2 ∧ domain p.2 ∧
        ∀ b q, D.family.Admissible b q → domain q →
          D.literalEnergy p.1 p.2 ≤ D.literalEnergy b q) ↔
      D.family.IsGlobalMin p.1 p.2 :=
    (D.literal_minimizers_on_iff hM domain hpost p.1 p.2).trans
      (D.family.global_minimizers_iff hM p.1 p.2).symm
  obtain ⟨p, hp, hu⟩ := existsUnique_variationalOptimizer U hM m hm hdiff hsc
  exact ⟨p, (heq p).mpr hp, fun q hq ↦ hu q ((heq q).mp hq)⟩

end LatentDiffusion.RegularModel
