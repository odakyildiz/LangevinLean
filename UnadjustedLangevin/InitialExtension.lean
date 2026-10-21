import UnadjustedLangevin.ChainLaw
import UnadjustedLangevin.TransportMoments

/-!
# A concrete independent-noise extension of every initial coupling

For an arbitrary coupling `c` of the algorithm's initialization `μ` and the
reference law `π`, take the product `c.joint.prod Q` with a noise space `Q`.
The two initial states retain exactly their coupled law and cost. The noise
is independent of both states. The output law depends only on `μ` and `Q`.
No optimal coupling, coupling-family axiom, or supplied equality of output
laws is used.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ULA

variable {H S Z : Type*} [MeasurableSpace H] [MeasurableSpace S] [MeasurableSpace Z]

/-- A coupling of probability measures is a probability measure. -/
theorem Coupling.isProbabilityMeasure {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) : IsProbabilityMeasure c.joint := by
  have : IsProbabilityMeasure (c.joint.map Prod.fst) := by
    rw [c.fst]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map measurable_fst.aemeasurable

/-- The probability space carrying an arbitrary initial coupling and fresh noise. -/
def initialExtension {μ π : Measure H} (c : Coupling μ π) (Q : Measure S) :
    Measure ((H × H) × S) := c.joint.prod Q

/-- Every probability noise space gives a probability extension. -/
theorem initialExtension_isProbabilityMeasure {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (Q : Measure S) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (initialExtension c Q) := by
  have := c.isProbabilityMeasure
  exact inferInstanceAs (IsProbabilityMeasure (c.joint.prod Q))

/-- The extension preserves the full initial joint distribution. -/
theorem initialExtension_joint {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q] :
    (initialExtension c Q).map Prod.fst = c.joint := by
  simp [initialExtension]

/-- The algorithm starts with exactly its specified initial law. -/
theorem initialExtension_initial {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q] :
    (initialExtension c Q).map (fun p ↦ p.1.1) = μ := by
  rw [← Function.comp_def, ← Measure.map_map measurable_fst measurable_fst,
    initialExtension_joint, c.fst]

/-- The reference starts with exactly its specified law. -/
theorem initialExtension_reference {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q] :
    (initialExtension c Q).map (fun p ↦ p.1.2) = π := by
  rw [← Function.comp_def, ← Measure.map_map measurable_snd measurable_fst,
    initialExtension_joint, c.snd]

/-- The noise marginal is unchanged. -/
theorem initialExtension_noise {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (Q : Measure S) [SFinite Q] :
    (initialExtension c Q).map Prod.snd = Q := by
  have := c.isProbabilityMeasure
  simp [initialExtension]

/-- The fresh noise is independent of the full coupled initial state. -/
theorem initialExtension_independent {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (Q : Measure S) [IsProbabilityMeasure Q] :
    IndepFun Prod.fst Prod.snd (initialExtension c Q) := by
  have := c.isProbabilityMeasure
  exact indepFun_prod measurable_id measurable_id

/-- Projecting out the reference gives precisely the product of the algorithm's
initial law and the noise-space law. -/
theorem initialExtension_initial_noise {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (Q : Measure S) [SFinite Q] :
    (initialExtension c Q).map (fun p ↦ (p.1.1, p.2)) = μ.prod Q := by
  have := c.isProbabilityMeasure
  change (c.joint.prod Q).map (Prod.map Prod.fst id) = _
  simpa only [c.fst, Measure.map_id] using
    (Measure.map_prod_map c.joint Q measurable_fst measurable_id).symm

/-- Every measurable function of the algorithm's initial state and noise has a
law independent of which initial coupling was used. -/
theorem initialExtension_map {T : Type*} [MeasurableSpace T]
    {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (Q : Measure S) [SFinite Q]
    (f : H × S → T) (hf : Measurable f) :
    (initialExtension c Q).map (fun p ↦ f (p.1.1, p.2)) = (μ.prod Q).map f := by
  rw [← initialExtension_initial_noise c Q,
    Measure.map_map hf (measurable_fst.fst.prodMk measurable_snd)]
  rfl

/-- In particular, the output law of the recursive algorithm is the canonical
law for every initial coupling. The noise space may carry Brownian paths,
iid Gaussian sequences, or another explicitly specified noise source. -/
theorem initialExtension_chainLaw {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (Q : Measure (ℕ → Z)) [SFinite Q]
    (F : H → Z → H) (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    (initialExtension c Q).map
      (fun p ↦ noiseDrivenChain F p.1.1 p.2 n) = chainLaw F μ Q n :=
  initialExtension_map c Q _ (noiseDrivenChain_measurable F hF n)

/-- The iid extension has exactly the requested noise marginal at every step. -/
theorem initialExtension_iid_noiseLaw {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (η : Measure Z) [IsProbabilityMeasure η] (n : ℕ) :
    (initialExtension c (Measure.infinitePi (fun _ : ℕ ↦ η))).map
      (fun p ↦ p.2 n) = η := by
  change (initialExtension c (Measure.infinitePi (fun _ : ℕ ↦ η))).map
    ((fun w : ℕ → Z ↦ w n) ∘ Prod.snd) = η
  rw [← Measure.map_map (measurable_pi_apply n) measurable_snd,
    initialExtension_noise, Measure.infinitePi_map_eval]

/-- The iid noise vectors on the extension are mutually independent. -/
theorem initialExtension_iid_independent {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (η : Measure Z) [IsProbabilityMeasure η] :
    iIndepFun (fun n (p : (H × H) × (ℕ → Z)) ↦ p.2 n)
      (initialExtension c (Measure.infinitePi (fun _ : ℕ ↦ η))) := by
  have := initialExtension_isProbabilityMeasure c (Measure.infinitePi (fun _ : ℕ ↦ η))
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).mpr
  simp only [initialExtension_iid_noiseLaw, initialExtension_noise]

/-- The initial state is independent of the complete iid noise sequence. -/
theorem initialExtension_initial_independent {μ π : Measure H} [IsProbabilityMeasure μ]
    (c : Coupling μ π) (Q : Measure S) [IsProbabilityMeasure Q] :
    IndepFun (fun p : (H × H) × S ↦ p.1.1) Prod.snd (initialExtension c Q) :=
  (initialExtension_independent c Q).comp measurable_fst measurable_id

section Cost

variable [NormedAddCommGroup H] [BorelSpace H] [SecondCountableTopology H]

/-- The extension retains exactly the quadratic cost of the given coupling. -/
theorem initialExtension_cost {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q] :
    eLpNorm (fun p : (H × H) × S ↦ p.1.1 - p.1.2) 2 (initialExtension c Q) =
      couplingCost c.joint := by
  exact eLpNorm_comp_measurePreserving
    (g := fun p : H × H ↦ p.1 - p.2) (p := 2) (by fun_prop)
    (measurePreserving_fst (μ := c.joint) (ν := Q))

/-- Finite cost gives an actual square-integrable difference on the extension. -/
theorem initialExtension_memLp_difference {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q] (hc : couplingCost c.joint ≠ ⊤) :
    MemLp (fun p : (H × H) × S ↦ p.1.1 - p.1.2) 2 (initialExtension c Q) := by
  change eLpNorm _ 2 _ < ⊤
  rw [initialExtension_cost]
  exact lt_top_iff_ne_top.mpr hc

omit [BorelSpace H] [SecondCountableTopology H] in
/-- Square integrability of the reference law lifts to its coordinate. -/
theorem initialExtension_memLp_reference {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q]
    (hπ : MemLp (fun x : H ↦ x) 2 π) :
    MemLp (fun p : (H × H) × S ↦ p.1.2) 2 (initialExtension c Q) := by
  have hmap : MemLp (fun x : H ↦ x) 2
      ((initialExtension c Q).map (fun p ↦ p.1.2)) := by
    rw [initialExtension_reference]
    exact hπ
  exact hmap.comp_of_map (by fun_prop)

/-- Finite coupling cost and the reference's second moment give a square
integrable initialization on every extension; no extra moment assumption is
introduced for the initial law. -/
theorem initialExtension_memLp_initial {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q] (hc : couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : H ↦ x) 2 π) :
    MemLp (fun p : (H × H) × S ↦ p.1.1) 2 (initialExtension c Q) := by
  simpa only [Pi.add_def, sub_add_cancel] using
    (initialExtension_memLp_difference c Q hc).add
      (initialExtension_memLp_reference c Q hπ)

/-- An actual `L²` initialization realizing the first coupling coordinate. -/
def initialExtension_lpInitial {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q] (hc : couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : H ↦ x) 2 π) : Lp H 2 (initialExtension c Q) :=
  (initialExtension_memLp_initial c Q hc hπ).toLp (fun p ↦ p.1.1)

/-- An actual `L²` reference initialization realizing the second coordinate. -/
def initialExtension_lpReference {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q]
    (hπ : MemLp (fun x : H ↦ x) 2 π) : Lp H 2 (initialExtension c Q) :=
  (initialExtension_memLp_reference c Q hπ).toLp (fun p ↦ p.1.2)

/-- Taking an `L²` representative does not change the initial law. -/
theorem initialExtension_lpInitial_law {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q] (hc : couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : H ↦ x) 2 π) :
    (initialExtension c Q).map (initialExtension_lpInitial c Q hc hπ) = μ := by
  unfold initialExtension_lpInitial
  rw [Measure.map_congr (initialExtension_memLp_initial c Q hc hπ).coeFn_toLp]
  exact initialExtension_initial c Q

omit [BorelSpace H] [SecondCountableTopology H] in
/-- Taking an `L²` representative does not change the reference's initial law. -/
theorem initialExtension_lpReference_law {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q]
    (hπ : MemLp (fun x : H ↦ x) 2 π) :
    (initialExtension c Q).map (initialExtension_lpReference c Q hπ) = π := by
  unfold initialExtension_lpReference
  rw [Measure.map_congr (initialExtension_memLp_reference c Q hπ).coeFn_toLp]
  exact initialExtension_reference c Q

/-- The `L²` distance of the constructed initializations equals the exact
initial coupling cost. This discharges, rather than assumes, initialCost. -/
theorem initialExtension_lp_cost {μ π : Measure H} (c : Coupling μ π)
    (Q : Measure S) [IsProbabilityMeasure Q] (hc : couplingCost c.joint ≠ ⊤)
    (hπ : MemLp (fun x : H ↦ x) 2 π) :
    ‖initialExtension_lpInitial c Q hc hπ - initialExtension_lpReference c Q hπ‖ =
      (couplingCost c.joint).toReal := by
  rw [Lp.norm_def]
  have hae : initialExtension_lpInitial c Q hc hπ - initialExtension_lpReference c Q hπ
      =ᵐ[initialExtension c Q] fun p ↦ p.1.1 - p.1.2 :=
    (Lp.coeFn_sub _ _).trans
      ((initialExtension_memLp_initial c Q hc hπ).coeFn_toLp.sub
        (initialExtension_memLp_reference c Q hπ).coeFn_toLp)
  rw [eLpNorm_congr_ae hae, initialExtension_cost]

end Cost
end ULA
