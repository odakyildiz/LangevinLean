import PBGSO.LawContraction
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! # The actual deterministic-optimiser product transport law

The state has the Euclidean product norm (`WithLp 2`), not the default
maximum norm on a Lean product. Couplings are lifted from sampler laws and
projected back to them. The deterministic optimiser coordinate contributes
exactly its squared distance to the quadratic transport cost.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Set
open scoped ENNReal NNReal
namespace PBGSO
namespace ProductTransport

variable {S Z : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]

abbrev Joint (S Z : Type*) := WithLp 2 (S × Z)

/-- Insert a deterministic complete optimiser state into the full Hilbert
state. Auxiliary optimiser and sampler variables are retained. -/
def embed (s : S) (z : Z) : Joint S Z := WithLp.toLp 2 (s, z)

@[fun_prop] theorem embed_measurable (s : S) : Measurable (embed (Z := Z) s) :=
  (WithLp.measurable_toLp 2 (S × Z)).comp (measurable_const.prodMk measurable_id)

theorem embed_lipschitz (s : S) : LipschitzWith 1 (embed (Z := Z) s) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  change dist (WithLp.toLp 2 (s, z)) (WithLp.toLp 2 (s, w)) ≤ _
  simp only [dist_eq_norm, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self]
  rw [WithLp.norm_toLp_snd]
  simp [dist_eq_norm]

/-- The actual product law δ_s tensor ν on the Euclidean full state. -/
def law (s : S) (ν : Measure Z) : Measure (Joint S Z) := ν.map (embed s)

/-- The embedding law is literally δ_s tensor ν, transported to the
Euclidean product type. -/
theorem law_eq_dirac_prod (s : S) (ν : Measure Z) [SFinite ν] :
    law s ν = ((Measure.dirac s).prod ν).map (WithLp.toLp 2) := by
  rw [Measure.dirac_prod, Measure.map_map (WithLp.measurable_toLp 2 (S × Z))
    measurable_prodMk_left]
  rfl

instance law_probability (s : S) (ν : Measure Z) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (law s ν) :=
  (Measure.isProbabilityMeasure_map_iff (embed_measurable s).aemeasurable).mpr inferInstance

theorem law_second_moment (s : S) (ν : Measure Z) [IsProbabilityMeasure ν]
    (hν : MemLp (fun z : Z => z) 2 ν) :
    MemLp (fun p : Joint S Z => p) 2 (law s ν) := by
  have hm := ProximalLangevin.memLp_lipschitz_observable ν (embed_lipschitz s) hν
  exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable
    (embed_measurable s).aemeasurable).mpr hm

theorem law_sampler_marginal (s : S) (ν : Measure Z) :
    (law s ν).map WithLp.snd = ν := by
  rw [law, Measure.map_map (WithLp.continuous_snd 2 S Z).measurable (embed_measurable s)]
  exact Measure.map_id

/-- Every optimiser coordinate under the actual product law is s. -/
theorem law_optimizer_ae (s : S) (ν : Measure Z) :
    ∀ᵐ p ∂law s ν, p.fst = s := by
  apply (ae_map_iff (embed_measurable s).aemeasurable
    (isClosed_eq (WithLp.continuous_fst 2 S Z) continuous_const).measurableSet).mpr
  exact ae_of_all ν fun _ => rfl

/-- Lift a genuine sampler coupling to the full two product laws. -/
def liftCoupling (s s' : S) {ν ν' : Measure Z} (c : ULA.Coupling ν ν') :
    ULA.Coupling (law s ν) (law s' ν') where
  joint := c.joint.map (fun p => (embed s p.1, embed s' p.2))
  fst := by
    rw [Measure.map_map (f := fun p : Z × Z => (embed s p.1, embed s' p.2))
      measurable_fst (by fun_prop)]
    change c.joint.map (embed s ∘ Prod.fst) = _
    rw [← Measure.map_map (embed_measurable s) measurable_fst, c.fst]
    rfl
  snd := by
    rw [Measure.map_map (f := fun p : Z × Z => (embed s p.1, embed s' p.2))
      measurable_snd (by fun_prop)]
    change c.joint.map (embed s' ∘ Prod.snd) = _
    rw [← Measure.map_map (embed_measurable s') measurable_snd, c.snd]
    rfl

/-- Project any genuine full-state coupling to its sampler marginals. -/
def projectCoupling (s s' : S) {ν ν' : Measure Z}
    (c : ULA.Coupling (law s ν) (law s' ν')) : ULA.Coupling ν ν' where
  joint := c.joint.map (fun p => (p.1.snd, p.2.snd))
  fst := by
    rw [Measure.map_map (f := fun p : Joint S Z × Joint S Z => (p.1.snd, p.2.snd))
      measurable_fst (by fun_prop)]
    change c.joint.map (WithLp.snd ∘ Prod.fst) = _
    rw [← Measure.map_map (WithLp.continuous_snd 2 S Z).measurable measurable_fst, c.fst]
    exact law_sampler_marginal s ν
  snd := by
    rw [Measure.map_map (f := fun p : Joint S Z × Joint S Z => (p.1.snd, p.2.snd))
      measurable_snd (by fun_prop)]
    change c.joint.map (WithLp.snd ∘ Prod.snd) = _
    rw [← Measure.map_map (WithLp.continuous_snd 2 S Z).measurable measurable_snd, c.snd]
    exact law_sampler_marginal s' ν'

/-- The full quadratic cost decomposes into deterministic optimiser cost
and projected sampler cost on any actual coupling of the two product laws. -/
theorem coupling_cost_decomposition (s s' : S) (ν ν' : Measure Z)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : MemLp (fun z : Z => z) 2 ν) (hν' : MemLp (fun z : Z => z) 2 ν')
    (c : ULA.Coupling (law s ν) (law s' ν')) :
    (ULA.couplingCost c.joint).toReal ^ 2 = ‖s - s'‖ ^ 2 +
      (ULA.couplingCost (projectCoupling s s' c).joint).toReal ^ 2 := by
  letI := c.isProbabilityMeasure
  have hm := coupling_difference_memLp (law s ν) (law s' ν')
    (law_second_moment s ν hν) (law_second_moment s' ν' hν') c
  have hp := coupling_difference_memLp ν ν' hν hν' (projectCoupling s s' c)
  rw [couplingCost_sq_eq_integral c.joint hm,
    couplingCost_sq_eq_integral (projectCoupling s s' c).joint hp]
  have hleft : ∀ᵐ p ∂c.joint, p.1.fst = s := by
    have hi := law_optimizer_ae s ν
    rw [← c.fst] at hi
    exact (ae_map_iff measurable_fst.aemeasurable
      ((isClosed_eq (WithLp.continuous_fst 2 S Z) continuous_const).measurableSet)).mp hi
  have hright : ∀ᵐ p ∂c.joint, p.2.fst = s' := by
    have hi := law_optimizer_ae s' ν'
    rw [← c.snd] at hi
    exact (ae_map_iff measurable_snd.aemeasurable
      ((isClosed_eq (WithLp.continuous_fst 2 S Z) continuous_const).measurableSet)).mp hi
  have hmap := integral_map
    (((WithLp.continuous_snd 2 S Z).measurable.comp measurable_fst).prodMk
      ((WithLp.continuous_snd 2 S Z).measurable.comp measurable_snd)).aemeasurable
    (show AEStronglyMeasurable (fun p : Z × Z => ‖p.1 - p.2‖ ^ 2)
      ((projectCoupling s s' c).joint) from hp.aestronglyMeasurable.norm.pow 2)
  change (∫ p, ‖p.1 - p.2‖ ^ 2 ∂c.joint) =
    ‖s - s'‖ ^ 2 + ∫ p, ‖p.1 - p.2‖ ^ 2 ∂(projectCoupling s s' c).joint
  change (∫ p : Z × Z, ‖p.1 - p.2‖ ^ 2 ∂(projectCoupling s s' c).joint) =
    ∫ p : Joint S Z × Joint S Z, ‖p.1.snd - p.2.snd‖ ^ 2 ∂c.joint at hmap
  rw [hmap]
  have hi : Integrable (fun p : Joint S Z × Joint S Z => ‖p.1.snd - p.2.snd‖ ^ 2) c.joint :=
    ((hp.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).comp_measurable
      (((WithLp.continuous_snd 2 S Z).measurable.comp measurable_fst).prodMk
        ((WithLp.continuous_snd 2 S Z).measurable.comp measurable_snd)))
  have hsum : (∫ p : Joint S Z × Joint S Z,
      ‖s - s'‖ ^ 2 + ‖p.1.snd - p.2.snd‖ ^ 2 ∂c.joint) =
      ‖s - s'‖ ^ 2 + ∫ p : Joint S Z × Joint S Z, ‖p.1.snd - p.2.snd‖ ^ 2 ∂c.joint := by
    rw [integral_add (integrable_const _) hi]
    simp
  rw [← hsum]
  apply integral_congr_ae
  filter_upwards [hleft, hright] with p hs hs'
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.sub_fst, WithLp.sub_snd, hs, hs']

theorem project_lift_joint (s s' : S) {ν ν' : Measure Z} (c : ULA.Coupling ν ν') :
    (projectCoupling s s' (liftCoupling s s' c)).joint = c.joint := by
  change (c.joint.map (fun p => (embed s p.1, embed s' p.2))).map
    (fun p => (p.1.snd, p.2.snd)) = c.joint
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

theorem lifted_cost_decomposition (s s' : S) (ν ν' : Measure Z)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : MemLp (fun z : Z => z) 2 ν) (hν' : MemLp (fun z : Z => z) 2 ν')
    (c : ULA.Coupling ν ν') :
    (ULA.couplingCost (liftCoupling s s' c).joint).toReal ^ 2 =
      ‖s - s'‖ ^ 2 + (ULA.couplingCost c.joint).toReal ^ 2 := by
  rw [coupling_cost_decomposition s s' ν ν' hν hν', project_lift_joint]

/-- Exact Wasserstein identity for the actual deterministic-optimiser
product laws, with the Euclidean product norm and finite second moments.
No optimal-coupling existence or supplied product-transport identity is used. -/
theorem wasserstein_product_eq (s s' : S) (ν ν' : Measure Z)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hν : MemLp (fun z : Z => z) 2 ν) (hν' : MemLp (fun z : Z => z) 2 ν') :
    ULA.wasserstein2Real (law s ν) (law s' ν') =
      Real.sqrt (‖s - s'‖ ^ 2 + ULA.wasserstein2Real ν ν' ^ 2) := by
  have hFull := ULA.wasserstein2_ne_top_of_memLp (law s ν) (law s' ν')
    (law_second_moment s ν hν) (law_second_moment s' ν' hν')
  have hSam := ULA.wasserstein2_ne_top_of_memLp ν ν' hν hν'
  apply le_antisymm
  · apply bound_of_all_finite_couplings ν ν' hSam
      (fun x => Real.sqrt (‖s - s'‖ ^ 2 + x ^ 2)) (by fun_prop)
    intro c _
    have hc := (coupling_difference_memLp (law s ν) (law s' ν')
      (law_second_moment s ν hν) (law_second_moment s' ν' hν')
      (liftCoupling s s' c)).eLpNorm_ne_top
    apply (wasserstein_le_finite_coupling (law s ν) (law s' ν')
      (liftCoupling s s' c) hc).trans_eq
    rw [← lifted_cost_decomposition s s' ν ν' hν hν' c,
      Real.sqrt_sq ENNReal.toReal_nonneg]
  · apply bound_of_all_finite_couplings (law s ν) (law s' ν') hFull
      (fun x => x) continuousAt_id
    intro c _
    have hp := (coupling_difference_memLp ν ν' hν hν' (projectCoupling s s' c)).eLpNorm_ne_top
    have hw := wasserstein_le_finite_coupling ν ν' (projectCoupling s s' c) hp
    have hs : ULA.wasserstein2Real ν ν' ^ 2 ≤
        (ULA.couplingCost (projectCoupling s s' c).joint).toReal ^ 2 :=
      (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hw
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) ENNReal.toReal_nonneg).mp
    rw [Real.sq_sqrt (by positivity), coupling_cost_decomposition s s' ν ν' hν hν' c]
    linarith

end ProductTransport

section ProductLawContraction
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
  [MeasurableSpace S] [BorelSpace S] [SecondCountableTopology S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z] [Fintype I]

/-- Contraction for the actual δ-optimiser tensor sampler laws in the full
Euclidean state space, with the source's exact condition-number factor. -/
theorem weak_product_law_contraction
    (M : Model S Θ Z X I) (D : TwistedGeometry S Z)
    (tests : Set (Z → ℝ)) (pairTests : Set (Z × Z → ℝ))
    (s s' : ℝ → S) (ν ν' : ℝ → Measure Z)
    [IsProbabilityMeasure (ν 0)] [IsProbabilityMeasure (ν' 0)]
    (hν : MemLp (fun z : Z => z) 2 (ν 0))
    (hν' : MemLp (fun z : Z => z) 2 (ν' 0))
    (hquad : couplingQuadratic D ∈ pairTests)
    (ρ T : ℝ) (hmono : TwistedJointMonotonicity M D ρ)
    (realize : ∀ c : ULA.Coupling (ν 0) (ν' 0),
      ∃ Λ : ℝ → Measure (Z × Z),
        IsCoupledWeakSolution M tests pairTests s s' ν ν' Λ ∧ Λ 0 = c.joint)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    ULA.wasserstein2Real (ProductTransport.law (s t) (ν t))
      (ProductTransport.law (s' t) (ν' t)) ≤
      Real.sqrt D.conditionNumber * Real.exp (-ρ * t) *
        ULA.wasserstein2Real (ProductTransport.law (s 0) (ν 0))
          (ProductTransport.law (s' 0) (ν' 0)) := by
  have hfinite := ULA.wasserstein2_ne_top_of_memLp (ν 0) (ν' 0) hν hν'
  obtain ⟨c, _⟩ := ULA.exists_finiteCost_coupling (ν 0) (ν' 0) hfinite
  obtain ⟨Λ, hsol, _⟩ := realize c
  letI := hsol.left.probability t ht.1
  letI := hsol.right.probability t ht.1
  have hνt : MemLp (fun z : Z => z) 2 (ν t) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).2
      (hsol.left.second_moment t ht.1)
  have hνt' : MemLp (fun z : Z => z) 2 (ν' t) :=
    (memLp_two_iff_integrable_sq_norm measurable_id.aestronglyMeasurable).2
      (hsol.right.second_moment t ht.1)
  rw [ProductTransport.wasserstein_product_eq _ _ _ _ hνt hνt',
    ProductTransport.wasserstein_product_eq _ _ _ _ hν hν']
  exact weak_law_contraction M D tests pairTests s s' ν ν' hν hν' hquad ρ T hmono realize t ht

end ProductLawContraction
end PBGSO
