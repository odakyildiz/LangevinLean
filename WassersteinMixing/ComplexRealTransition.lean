import WassersteinMixing.ComplexRealCorrector
import WassersteinMixing.Semigroup

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Real observables are preserved by actual complex transition compression

Pointwise real-to-complex embeddings commute with actual evaluation and its
adjoint. Thus compression of two measure-preserving observations preserves the
real image; the corrector construction needs no extra preservation hypothesis.
-/

noncomputable section
open MeasureTheory

namespace WassersteinMixing.RealComplexEmbedding

section Restrict
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
local instance : InnerProductSpace ℝ K := InnerProductSpace.rclikeToReal ℂ K

/-- Complex adjunction agrees with real adjunction after scalar restriction. -/
theorem adjoint_restrictScalars (T : H →L[ℂ] K) :
    (T.restrictScalars ℝ).adjoint = T.adjoint.restrictScalars ℝ := by
  ext y
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left]
  change (inner ℂ y (T x)).re = (inner ℂ (T.adjoint y) x).re
  rw [ContinuousLinearMap.adjoint_inner_left]

end Restrict

section Pointwise
variable {A B R H : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

omit [CompleteSpace H] in
/-- The real inner product on complex `L²` has its genuine pointwise integral. -/
theorem real_inner_Lp (μ : Measure A) (f g : Lp H 2 μ) :
    inner ℝ f g = ∫ a, inner ℝ (f a) (g a) ∂μ := by
  rfl

omit [CompleteSpace H] in
/-- The pointwise and scalar-restricted real inner products on complex `L²` agree. -/
theorem real_inner_Lp_eq_re (μ : Measure A) (f g : Lp H 2 μ) :
    inner ℝ f g = (inner ℂ f g).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner f g)

/-- The adjoint of pointwise embedding is actual pointwise adjoint extraction. -/
theorem mapLp_adjoint (i : R →ₗᵢ[ℝ] H) (μ : Measure A) :
    (mapLp i μ).toContinuousLinearMap.adjoint =
      i.toContinuousLinearMap.adjoint.compLpL 2 μ := by
  ext z : 1
  apply ext_inner_right ℝ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  change (inner ℂ z (mapLp i μ f)).re = _
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ a, (inner ℂ (z a) (mapLp i μ f a)).re ∂μ :=
      (integral_re (L2.integrable_inner (𝕜 := ℂ) z (mapLp i μ f))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [mapLp_coeFn i μ f,
        i.toContinuousLinearMap.adjoint.coeFn_compLp z] with a hf hz
      change (inner ℂ (z a) (mapLp i μ f a)).re =
        inner ℝ ((i.toContinuousLinearMap.adjoint.compLp z) a) (f a)
      rw [hf, hz]
      exact (i.toContinuousLinearMap.adjoint_inner_left (f a) (z a)).symm

/-- Every actual evaluation commutes with pointwise adjoint extraction. -/
theorem extraction_compMeasurePreserving (i : R →ₗᵢ[ℝ] H)
    (μ : Measure A) (ν : Measure B) (φ : B → A) (hφ : MeasurePreserving φ ν μ)
    (f : Lp H 2 μ) :
    i.toContinuousLinearMap.adjoint.compLpL 2 ν (Lp.compMeasurePreserving φ hφ f) =
      Lp.compMeasurePreserving φ hφ (i.toContinuousLinearMap.adjoint.compLpL 2 μ f) := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving f hφ
  have h2 := i.toContinuousLinearMap.adjoint.coeFn_compLp
    (Lp.compMeasurePreserving φ hφ f)
  have h3 := Lp.coeFn_compMeasurePreserving
    (i.toContinuousLinearMap.adjoint.compLpL 2 μ f) hφ
  have h4 := hφ.quasiMeasurePreserving.ae_eq_comp
    (i.toContinuousLinearMap.adjoint.coeFn_compLp f)
  filter_upwards [h1, h2, h3, h4] with b h1 h2 h3 h4
  exact h2.trans ((congrArg i.toContinuousLinearMap.adjoint h1).trans (h4.symm.trans h3.symm))

omit [CompleteSpace R] [CompleteSpace H] in
/-- Pointwise real embedding commutes with evaluation of actual observations. -/
theorem mapLp_compMeasurePreserving (i : R →ₗᵢ[ℝ] H)
    (μ : Measure A) (ν : Measure B) (φ : B → A) (hφ : MeasurePreserving φ ν μ)
    (f : Lp R 2 μ) :
    mapLp i ν (Lp.compMeasurePreserving φ hφ f) =
      Lp.compMeasurePreserving φ hφ (mapLp i μ f) := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving f hφ
  have h2 := mapLp_coeFn i ν (Lp.compMeasurePreserving φ hφ f)
  have h3 := Lp.coeFn_compMeasurePreserving (mapLp i μ f) hφ
  have h4 := hφ.quasiMeasurePreserving.ae_eq_comp (mapLp_coeFn i μ f)
  filter_upwards [h1, h2, h3, h4] with b h1 h2 h3 h4
  exact h2.trans ((congrArg i h1).trans (h4.symm.trans h3.symm))

/-- Adjoint evaluation also commutes with actual real-observable embedding. -/
theorem evaluation_adjoint_mapLp (i : R →ₗᵢ[ℝ] H)
    (μ : Measure A) (ν : Measure B) (φ : B → A) (hφ : MeasurePreserving φ ν μ)
    (f : Lp R 2 ν) :
    (Lp.compMeasurePreservingₗᵢ ℂ φ hφ).toContinuousLinearMap.adjoint (mapLp i ν f) =
      mapLp i μ ((Lp.compMeasurePreservingₗᵢ ℝ φ hφ).toContinuousLinearMap.adjoint f) := by
  let C : Lp H 2 μ →L[ℂ] Lp H 2 ν :=
    (Lp.compMeasurePreservingₗᵢ ℂ φ hφ).toContinuousLinearMap
  let A : Lp R 2 μ →L[ℝ] Lp R 2 ν :=
    (Lp.compMeasurePreservingₗᵢ ℝ φ hφ).toContinuousLinearMap
  have he : (mapLp i ν).toContinuousLinearMap.adjoint ∘L C.restrictScalars ℝ =
      A ∘L (mapLp i μ).toContinuousLinearMap.adjoint := by
    ext z : 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [mapLp_adjoint, mapLp_adjoint]
    exact extraction_compMeasurePreserving i μ ν φ hφ z
  have ha := congrArg (fun T ↦ T.adjoint) he
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_adjoint,
    adjoint_restrictScalars] at ha
  exact congrArg (fun T ↦ T f) ha

/-- Compression of two actual observations sends embedded real observables to
the embedding of their genuine real transition. -/
theorem compression_mapLp (i : R →ₗᵢ[ℝ] H)
    (μ : Measure A) (ν : Measure B) (φ ψ : B → A)
    (hφ : MeasurePreserving φ ν μ) (hψ : MeasurePreserving ψ ν μ)
    (f : Lp R 2 μ) :
    ObservableTransition.compression (Lp.compMeasurePreservingₗᵢ ℂ φ hφ)
      (Lp.compMeasurePreservingₗᵢ ℂ ψ hψ) (mapLp i μ f) =
      mapLp i μ (ObservableTransition.compression (Lp.compMeasurePreservingₗᵢ ℝ φ hφ)
        (Lp.compMeasurePreservingₗᵢ ℝ ψ hψ) f) := by
  change (Lp.compMeasurePreservingₗᵢ ℂ φ hφ).toContinuousLinearMap.adjoint
      (Lp.compMeasurePreserving ψ hψ (mapLp i μ f)) = _
  rw [← mapLp_compMeasurePreserving i μ ν ψ hψ f, evaluation_adjoint_mapLp]
  rfl

/-- Real-range preservation follows from actual evaluation compression. -/
theorem compression_mem_range (i : R →ₗᵢ[ℝ] H)
    (μ : Measure A) (ν : Measure B) (φ ψ : B → A)
    (hφ : MeasurePreserving φ ν μ) (hψ : MeasurePreserving ψ ν μ)
    (f : Lp R 2 μ) :
    ObservableTransition.compression (Lp.compMeasurePreservingₗᵢ ℂ φ hφ)
      (Lp.compMeasurePreservingₗᵢ ℂ ψ hψ) (mapLp i μ f) ∈ Set.range (mapLp i μ) :=
  ⟨_, (compression_mapLp i μ ν φ ψ hφ hψ f).symm⟩

end Pointwise
end WassersteinMixing.RealComplexEmbedding
