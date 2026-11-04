import WassersteinMixing.Semigroup
import WassersteinMixing.SemigroupContinuity

/-! # Passing reversible Markov operator identities through actual strong limits

These lemmas are used after a concrete discrete Markov approximation has been
proved to converge. Self-adjointness and composition are conclusions of the
strong convergence; no limiting semigroup identity is supplied as an input.
-/

noncomputable section
open Filter
open scoped Topology

namespace WassersteinMixing

/-- Adding independent auxiliary randomness cannot change a compressed
transition: the common source pullback is an isometry on both evaluations. -/
theorem compression_isometricLift {𝕜 A B C : Type*} [RCLike 𝕜]
    [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] [CompleteSpace B]
    [NormedAddCommGroup C] [InnerProductSpace 𝕜 C] [CompleteSpace C]
    (initial current : A →ₗᵢ[𝕜] B) (lift : B →ₗᵢ[𝕜] C) :
    ObservableTransition.compression (lift.comp initial) (lift.comp current) =
      ObservableTransition.compression initial current := by
  ext f
  apply ext_inner_right 𝕜
  intro g
  rw [ObservableTransition.compression_inner, ObservableTransition.compression_inner]
  exact lift.inner_map_map _ _

variable {𝕜 H I : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] [CompleteSpace H] {l : Filter I}

/-- Strong convergence preserves self-adjointness. -/
theorem strongLimit_isSelfAdjoint [l.NeBot]
    (A : I → H →L[𝕜] H) (T : H →L[𝕜] H)
    (hA : ∀ i, IsSelfAdjoint (A i))
    (hlim : ∀ f, Tendsto (fun i ↦ A i f) l (𝓝 (T f))) : IsSelfAdjoint T := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hleft : Tendsto (fun i ↦ inner 𝕜 (A i f) g) l (𝓝 (inner 𝕜 (T f) g)) :=
    (hlim f).inner tendsto_const_nhds
  have hright : Tendsto (fun i ↦ inner 𝕜 f (A i g)) l (𝓝 (inner 𝕜 f (T g))) :=
    tendsto_const_nhds.inner (hlim g)
  have heq : (fun i ↦ inner 𝕜 (A i f) g) =ᶠ[l] fun i ↦ inner 𝕜 f (A i g) :=
    Eventually.of_forall fun i ↦
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA i)) f g
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

omit [CompleteSpace H] in
/-- Two strongly convergent families compose strongly when the first family
is contractive, as is the case for every actual Markov approximation here. -/
theorem strongLimit_comp
    (A B : I → H →L[𝕜] H) (T S : H →L[𝕜] H)
    (hcontract : ∀ i f, ‖A i f‖ ≤ ‖f‖)
    (hA : ∀ f, Tendsto (fun i ↦ A i f) l (𝓝 (T f)))
    (hB : ∀ f, Tendsto (fun i ↦ B i f) l (𝓝 (S f))) (f : H) :
    Tendsto (fun i ↦ A i (B i f)) l (𝓝 (T (S f))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hfirst := tendsto_iff_norm_sub_tendsto_zero.mp (hB f)
  have hsecond := tendsto_iff_norm_sub_tendsto_zero.mp (hA (S f))
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    (by simpa only [add_zero] using hfirst.add hsecond)
  calc
    _ ≤ ‖A i (B i f) - A i (S f)‖ + ‖A i (S f) - T (S f)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖A i (B i f - S f)‖ + ‖A i (S f) - T (S f)‖ := by rw [map_sub]
    _ ≤ _ := add_le_add (hcontract i _) le_rfl

omit [CompleteSpace H] in
/-- A discrete composition identity passes to the limiting actual operators.
For MALA, the three approximants are powers with two step counts and their sum. -/
theorem strongLimit_comp_eq [l.NeBot]
    (A B C : I → H →L[𝕜] H) (T S R : H →L[𝕜] H)
    (hcontract : ∀ i f, ‖A i f‖ ≤ ‖f‖)
    (hcomp : ∀ i, C i = A i ∘L B i)
    (hA : ∀ f, Tendsto (fun i ↦ A i f) l (𝓝 (T f)))
    (hB : ∀ f, Tendsto (fun i ↦ B i f) l (𝓝 (S f)))
    (hC : ∀ f, Tendsto (fun i ↦ C i f) l (𝓝 (R f))) : R = T ∘L S := by
  ext f
  have hc := hC f
  have hab := strongLimit_comp A B T S hcontract hA hB f
  simp only [hcomp, ContinuousLinearMap.comp_apply] at hc
  exact tendsto_nhds_unique hc hab

end WassersteinMixing
