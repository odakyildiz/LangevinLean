import UnadjustedLangevin.ProductBrownian
import UnadjustedLangevin.CanonicalBrownian
import Mathlib.Probability.Independence.InfinitePi

set_option linter.style.header false

/-! # Independent Brownian coordinates on the actual particle-copy space

The common parameter Brownian motion is taken from the first copy, while each
particle uses the latent Brownian coordinates of its own copy. Flattening the
independent rows and selecting distinct coordinates proves independence of the
entire coordinate paths, including the first particle and common parameter.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace ProximalLangevin

/-- Select a distinct base-copy/coordinate pair for every particle-noise coordinate. -/
def particleBrownianIndex {N dθ dx : ℕ} (hN : 0 < N) :
    Fin dθ ⊕ (Fin N × Fin dx) → Fin N × (Fin dθ ⊕ Fin dx)
  | .inl j => (⟨0, hN⟩, .inl j)
  | .inr p => (p.1, .inr p.2)

/-- The common parameter uses copy zero; latent blocks use their respective copies. -/
theorem particleBrownianIndex_injective {N dθ dx : ℕ} (hN : 0 < N) :
    Function.Injective (@particleBrownianIndex N dθ dx hN) := by
  intro a b hab
  rcases a with a | ⟨i, a⟩ <;> rcases b with b | ⟨j, b⟩
  · simpa [particleBrownianIndex] using hab
  · simp [particleBrownianIndex] at hab
  · simp [particleBrownianIndex] at hab
  · simpa [particleBrownianIndex] using hab

/-- The actual joint Brownian source for the interacting particle coordinates. -/
def particleBrownianFamily {Ω : Type*} {N dθ dx : ℕ} (hN : 0 < N)
    (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (a : Fin dθ ⊕ (Fin N × Fin dx)) (t : ℝ≥0) (ω : Fin N → Ω) : ℝ :=
  W (particleBrownianIndex hN a).2 t (ω (particleBrownianIndex hN a).1)

@[simp] theorem particleBrownianFamily_parameter {Ω : Type*} {N dθ dx : ℕ}
    (hN : 0 < N) (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (j : Fin dθ) (t : ℝ≥0) (ω : Fin N → Ω) :
    particleBrownianFamily hN W (.inl j) t ω = W (.inl j) t (ω ⟨0, hN⟩) := rfl

@[simp] theorem particleBrownianFamily_latent {Ω : Type*} {N dθ dx : ℕ}
    (hN : 0 < N) (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (i : Fin N) (j : Fin dx) (t : ℝ≥0) (ω : Fin N → Ω) :
    particleBrownianFamily hN W (.inr (i, j)) t ω = W (.inr j) t (ω i) := rfl

section Source
variable {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {N dθ dx : ℕ} (hN : 0 < N)
    (W : (Fin dθ ⊕ Fin dx) → ℝ≥0 → Ω → ℝ)
    (hW : ∀ j, IsPreBrownianReal (W j) Q)

include hW

/-- Every selected coordinate is an actual standard pre-Brownian motion. -/
theorem particleBrownianFamily_preBrownian (a : Fin dθ ⊕ (Fin N × Fin dx)) :
    IsPreBrownianReal (particleBrownianFamily hN W a) (Measure.pi (fun _ : Fin N => Q)) :=
  ULA.Hilbert.preBrownian_comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin N => Q) (particleBrownianIndex hN a).1)
    (W (particleBrownianIndex hN a).2) (hW _)

omit hW in
/-- Measurable source evaluations remain measurable after selecting a copy. -/
theorem particleBrownianFamily_measurable (hm : ∀ j t, Measurable (W j t))
    (a : Fin dθ ⊕ (Fin N × Fin dx)) (t : ℝ≥0) :
    Measurable (particleBrownianFamily hN W a t) :=
  (hm _ _).comp (measurable_pi_apply _)

omit hW in
/-- Full coordinate-path independence is derived on the actual finite product.
There is no assumption of independent particles after interaction. -/
theorem particleBrownianFamily_paths_independent
    (hm : ∀ j t, Measurable (W j t))
    (hind : iIndepFun (fun j ω t => W j t ω) Q) :
    iIndepFun (fun a (ω : Fin N → Ω) t => particleBrownianFamily hN W a t ω)
      (Measure.pi (fun _ : Fin N => Q)) := by
  let P := Measure.pi (fun _ : Fin N => Q)
  let X := fun (i : Fin N) (j : Fin dθ ⊕ Fin dx) (ω : Fin N → Ω) (t : ℝ≥0) =>
    W j t (ω i)
  have hfull : Measurable (fun ω (j : Fin dθ ⊕ Fin dx) (t : ℝ≥0) => W j t ω) :=
    measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun t => hm j t
  have hXm (i : Fin N) (j : Fin dθ ⊕ Fin dx) : Measurable (X i j) :=
    measurable_pi_iff.mpr fun t => (hm j t).comp (measurable_pi_apply i)
  have hrows : iIndepFun (fun i ω j => X i j ω) P :=
    iIndepFun_pi (fun _ => hfull.aemeasurable)
  have hrow (i : Fin N) : iIndepFun (X i) P := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hXm i j).aemeasurable)).mpr
    have hmap : P.map (fun ω j => X i j ω) = Q.map (fun ω j t => W j t ω) := by
      change P.map ((fun ω j t => W j t ω) ∘ (fun ω : Fin N → Ω => ω i)) = _
      rw [← Measure.map_map hfull (measurable_pi_apply i),
        (measurePreserving_eval (fun _ : Fin N => Q) i).map_eq]
    rw [hmap, hind.map_fun_eq_pi_map
      (fun j => (measurable_pi_iff.mpr fun t => hm j t).aemeasurable)]
    congr 1
    funext j
    change Q.map (fun ω t => W j t ω) =
      P.map ((fun ω t => W j t ω) ∘ (fun ω : Fin N → Ω => ω i))
    rw [← Measure.map_map (measurable_pi_iff.mpr fun t => hm j t) (measurable_pi_apply i),
      (measurePreserving_eval (fun _ : Fin N => Q) i).map_eq]
  have hflat : iIndepFun (fun p : Fin N × (Fin dθ ⊕ Fin dx) => X p.1 p.2) P :=
    iIndepFun_uncurry' hXm hrows hrow
  exact hflat.precomp (particleBrownianIndex_injective hN)

end Source

/-- The concrete canonical Gaussian time-indicator construction supplies all
selected scalar Brownian laws and their full-path independence. -/
theorem canonical_particleBrownianFamily (N dθ dx : ℕ) (hN : 0 < N) :
    (∀ a : Fin dθ ⊕ (Fin N × Fin dx),
      IsPreBrownianReal (particleBrownianFamily hN ULA.CanonicalBrownian.coordinate a)
        (Measure.pi (fun _ : Fin N =>
          ULA.CanonicalBrownian.vectorProbability (Fin dθ ⊕ Fin dx)))) ∧
    iIndepFun (fun a (ω : Fin N → ULA.CanonicalBrownian.VectorSample (Fin dθ ⊕ Fin dx)) t =>
      particleBrownianFamily hN ULA.CanonicalBrownian.coordinate a t ω)
      (Measure.pi (fun _ : Fin N =>
        ULA.CanonicalBrownian.vectorProbability (Fin dθ ⊕ Fin dx))) := by
  refine ⟨particleBrownianFamily_preBrownian _ hN _
    ULA.CanonicalBrownian.coordinate_isPreBrownian, ?_⟩
  apply particleBrownianFamily_paths_independent _ hN _
  · intro j t
    exact (ULA.CanonicalBrownian.process_measurable t).comp (measurable_pi_apply j)
  · exact ULA.CanonicalBrownian.coordinate_paths_independent _

end ProximalLangevin
