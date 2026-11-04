import WassersteinMixing.SemigroupPoisson
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.style.header false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Passing the constructed complex corrector to a genuine real subspace

An isometric real embedding gives an orthogonal projection. Preservation by
the actual semigroup implies preservation by the integrated defect, every
partial corrector, and its proved strong limit. Adjoint extraction therefore
transfers the exact Poisson equation and both corrector estimates to the real
space, without assuming any property of a chosen real corrector.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace WassersteinMixing.ComplexRealCorrector

variable {R H : Type*} [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H

/-- The actual orthogonal projection onto the embedded real space. -/
def projection (i : R →ₗᵢ[ℝ] H) : H →L[ℝ] H :=
  i.toContinuousLinearMap ∘L i.toContinuousLinearMap.adjoint

/-- Adjoint extraction is exactly the identity on the isometric real image. -/
theorem adjoint_embed (i : R →ₗᵢ[ℝ] H) (x : R) :
    i.toContinuousLinearMap.adjoint (i x) = x := by
  have he := congrArg (fun T : R →L[ℝ] R ↦ T x) i.adjoint_comp_self
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self,
    LinearIsometry.coe_toContinuousLinearMap] using he

@[simp] theorem projection_embed (i : R →ₗᵢ[ℝ] H) (x : R) :
    projection i (i x) = i x := by
  simp only [projection, ContinuousLinearMap.comp_apply, adjoint_embed,
    LinearIsometry.coe_toContinuousLinearMap]

/-- Fixed vectors of the projection are exactly vectors in the embedded real range. -/
theorem projection_fixed_iff (i : R →ₗᵢ[ℝ] H) (y : H) :
    projection i y = y ↔ y ∈ Set.range i := by
  constructor
  · intro hy
    exact ⟨i.toContinuousLinearMap.adjoint y, hy⟩
  · rintro ⟨x, rfl⟩
    exact projection_embed i x

/-- The embedded real range is closed, proved through its continuous projection. -/
theorem isClosed_range (i : R →ₗᵢ[ℝ] H) : IsClosed (Set.range i) := by
  have heq : Set.range i = {y | projection i y = y} := by
    ext y
    exact (projection_fixed_iff i y).symm
  rw [heq]
  exact isClosed_eq (projection i).continuous continuous_id

/-- Real-subspace preservation is a property of the semigroup, not an assumption
about the corrector. Actual coordinate transition operators prove this property. -/
def PreservesReal (S : ReversibleSemigroup H) (i : R →ₗᵢ[ℝ] H) : Prop :=
  ∀ t, 0 ≤ t → ∀ x, projection i (S.op t (i x)) = S.op t (i x)

variable (S : ReversibleSemigroup H) (i : R →ₗᵢ[ℝ] H)

theorem op_fixed (hreal : PreservesReal S i) {t : ℝ} (ht : 0 ≤ t)
    (y : H) (hy : projection i y = y) :
    projection i (S.op t y) = S.op t y := by
  have he : i (i.toContinuousLinearMap.adjoint y) = y := hy
  have h := hreal t ht (i.toContinuousLinearMap.adjoint y)
  rw [he] at h
  exact h

/-- The genuine Bochner defect preserves the embedded real subspace. -/
theorem defect_fixed (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h) (x : R) :
    projection i (S.defect h (i x)) = S.defect h (i x) := by
  unfold ReversibleSemigroup.defect
  rw [← (projection i).intervalIntegral_comp_comm (S.defect_integrable (i x) hh)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht0 : 0 ≤ t := (show t ∈ Set.Icc 0 h by simpa only [Set.uIcc_of_le hh] using ht).1
  change projection i (i x - S.op t (i x)) = i x - S.op t (i x)
  rw [map_sub, projection_embed, hreal t ht0 x]

/-- Every constructed partial corrector preserves the real range. -/
theorem partialCorrector_fixed (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h)
    (N : ℕ) (x : R) :
    projection i (S.partialCorrector h hh N (i x)) = S.partialCorrector h hh N (i x) := by
  induction N with
  | zero => simp [ReversibleSemigroup.partialCorrector]
  | succ N ih =>
    rw [S.partialCorrector_succ h hh N, add_apply, map_add, ih]
    congr 1
    exact op_fixed S i hreal (by positivity) (S.defect h (i x))
      (defect_fixed S i hreal h hh x)

/-- Closed-range preservation passes to the actual strong corrector limit. -/
theorem corrector_fixed (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h) (x : R) :
    projection i (S.corrector h hh (i x)) = S.corrector h hh (i x) := by
  have hl := S.partialCorrector_tendsto h hh (i x)
  have hp := (projection i).continuous.tendsto (S.corrector h hh (i x)) |>.comp hl
  have hr : Tendsto (fun N ↦ projection i (S.partialCorrector h hh N (i x)))
      atTop (𝓝 (S.corrector h hh (i x))) := by
    convert hl using 1
    ext N
    exact partialCorrector_fixed S i hreal h hh N x
  exact tendsto_nhds_unique hp hr

/-- Extraction of the actual semigroup as real bounded operators. -/
def realOp (t : ℝ) : R →L[ℝ] R :=
  i.toContinuousLinearMap.adjoint ∘L (S.op t).restrictScalars ℝ ∘L i.toContinuousLinearMap

/-- Extraction of the already constructed complex corrector. -/
def realCorrector (h : ℝ) (hh : 0 ≤ h) : R →L[ℝ] R :=
  i.toContinuousLinearMap.adjoint ∘L (S.corrector h hh).restrictScalars ℝ ∘L
    i.toContinuousLinearMap

/-- The real transition embeds exactly into the complex transition. -/
theorem embed_realOp (hreal : PreservesReal S i) {t : ℝ} (ht : 0 ≤ t) (x : R) :
    i (realOp S i t x) = S.op t (i x) := hreal t ht x

/-- The real corrector embeds exactly into the constructed complex corrector. -/
theorem embed_realCorrector (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h) (x : R) :
    i (realCorrector S i h hh x) = S.corrector h hh (i x) :=
  corrector_fixed S i hreal h hh x

/-- The pointwise norm estimate transfers without a dimension factor. -/
theorem realCorrector_norm_le (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h) (x : R) :
    ‖realCorrector S i h hh x‖ ≤ h * ‖x‖ := by
  calc
    _ = ‖i (realCorrector S i h hh x)‖ := (i.norm_map _).symm
    _ = ‖S.corrector h hh (i x)‖ := congrArg norm (embed_realCorrector S i hreal h hh x)
    _ ≤ h * ‖i x‖ := (S.corrector h hh).le_of_opNorm_le (S.corrector_norm_le h hh) (i x)
    _ = _ := by rw [i.norm_map]

/-- The real corrector is bounded by the same step in operator norm. -/
theorem realCorrector_opNorm_le (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h) :
    ‖realCorrector S i h hh‖ ≤ h := by
  apply ContinuousLinearMap.opNorm_le_bound _ hh
  exact realCorrector_norm_le S i hreal h hh

/-- The actual real defect, extracted from the complex Bochner defect. -/
def realDefect (h : ℝ) (x : R) : R :=
  i.toContinuousLinearMap.adjoint (S.defect h (i x))

/-- The extracted defect is the genuine integral of the real semigroup increments. -/
theorem realDefect_eq_integral (h : ℝ) (hh : 0 ≤ h) (x : R) :
    realDefect S i h x = ∫ t in 0..h, x - realOp S i t x := by
  unfold realDefect ReversibleSemigroup.defect
  rw [← i.toContinuousLinearMap.adjoint.intervalIntegral_comp_comm
    (S.defect_integrable (i x) hh)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [map_sub, adjoint_embed, realOp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', LinearIsometry.coe_toContinuousLinearMap]

/-- The real defect embeds exactly into the actual complex defect. -/
theorem embed_realDefect (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h) (x : R) :
    i (realDefect S i h x) = S.defect h (i x) := defect_fixed S i hreal h hh x

/-- The exact Poisson equation holds on the real space, with its true time integral. -/
theorem realCorrector_poisson (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h) (x : R) :
    realCorrector S i h hh x - realOp S i h (realCorrector S i h hh x) =
      ∫ t in 0..h, x - realOp S i t x := by
  rw [← realDefect_eq_integral S i h hh x]
  apply i.injective
  rw [map_sub, embed_realCorrector S i hreal h hh,
    embed_realOp S i hreal hh, embed_realCorrector S i hreal h hh,
    embed_realDefect S i hreal h hh]
  exact S.corrector_poisson h hh (i x)

/-- The Dirichlet-energy estimate transfers isometrically to real observables. -/
theorem realCorrector_energy_le (hreal : PreservesReal S i) (h : ℝ) (hh : 0 ≤ h)
    {s : ℝ} (hs : 0 ≤ s) (x : R) :
    inner ℝ (realCorrector S i h hh x)
      (realCorrector S i h hh x - realOp S i s (realCorrector S i h hh x)) ≤
      h ^ 2 * inner ℝ x (x - realOp S i s x) := by
  have he := S.corrector_energy_le h hh hs (i x)
  rw [← embed_realCorrector S i hreal h hh x,
    ← embed_realOp S i hreal hs (realCorrector S i h hh x),
    ← map_sub, i.inner_map_map,
    ← embed_realOp S i hreal hs x, ← map_sub, i.inner_map_map] at he
  exact he

end WassersteinMixing.ComplexRealCorrector

namespace WassersteinMixing.RealComplexEmbedding

variable {A E F : Type*} [MeasurableSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual pointwise linear isometry induces a genuine isometry of `L²`
classes; no second-moment or measurability condition is assumed on the image. -/
def mapLp (i : E →ₗᵢ[ℝ] F) (μ : Measure A) : Lp E 2 μ →ₗᵢ[ℝ] Lp F 2 μ where
  toLinearMap := i.toContinuousLinearMap.compLpₗ 2 μ
  norm_map' f := by
    change ‖i.toContinuousLinearMap.compLp f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    filter_upwards [i.toContinuousLinearMap.coeFn_compLp f] with a ha
    rw [ha, LinearIsometry.coe_toContinuousLinearMap, i.norm_map]

/-- The lifted map has exactly the expected pointwise representative. -/
theorem mapLp_coeFn (i : E →ₗᵢ[ℝ] F) (μ : Measure A) (f : Lp E 2 μ) :
    mapLp i μ f =ᵐ[μ] fun a ↦ i (f a) := by
  change i.toContinuousLinearMap.compLp f =ᵐ[μ] fun a ↦ i (f a)
  simpa only [Filter.EventuallyEq, LinearIsometry.coe_toContinuousLinearMap] using
    i.toContinuousLinearMap.coeFn_compLp f

/-- Coordinatewise real-to-complex inclusion is an actual real linear isometry. -/
def euclideanOfReal (ι : Type*) [Fintype ι] :
    EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℂ ι where
  toFun x := WithLp.toLp 2 (fun j ↦ (x j : ℂ))
  map_add' x y := by
    ext j
    simp
  map_smul' c x := by
    ext j
    simp
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp

/-- A concrete finite-dimensional real Hilbert space embeds isometrically in
complex coordinate space using its proved orthonormal-basis representation. -/
def coordinate (R : Type*) [NormedAddCommGroup R] [InnerProductSpace ℝ R]
    [FiniteDimensional ℝ R] :
    R →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (Module.finrank ℝ R)) :=
  (euclideanOfReal (Fin (Module.finrank ℝ R))).comp
    (stdOrthonormalBasis ℝ R).repr.toLinearIsometry

/-- The actual coordinatewise complex embedding of real-valued `L²` observables. -/
def coordinateLp (R : Type*) [NormedAddCommGroup R] [InnerProductSpace ℝ R]
    [FiniteDimensional ℝ R] (μ : Measure A) :
    Lp R 2 μ →ₗᵢ[ℝ] Lp (EuclideanSpace ℂ (Fin (Module.finrank ℝ R))) 2 μ :=
  mapLp (coordinate R) μ

/-- The coordinate embedding preserves every observable norm without a
cardinality or dimension loss. -/
theorem coordinateLp_norm (R : Type*) [NormedAddCommGroup R] [InnerProductSpace ℝ R]
    [FiniteDimensional ℝ R] (μ : Measure A) (f : Lp R 2 μ) :
    ‖coordinateLp R μ f‖ = ‖f‖ := (coordinateLp R μ).norm_map f

end WassersteinMixing.RealComplexEmbedding
