import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # Concrete `L²` transition operators of stationary two-time laws

For an actual stationary joint law, composition with its two coordinate
projections gives two isometries. Their adjoint compression constructs the
transition operator. Contractivity and the reversible self-adjoint identity
are proved from those measures, rather than supplied as operator fields.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ENNReal InnerProduct

namespace WassersteinMixing.StationaryPair

variable {𝕜 E F : Type*} [RCLike 𝕜] [MeasurableSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  (μ : Measure E) (J : Measure (E × E))
  (hfst : J.map Prod.fst = μ) (hsnd : J.map Prod.snd = μ)

/-- Evaluation at the actual first state of a stationary two-time law. -/
def evalFst : Lp F 2 μ →ₗᵢ[𝕜] Lp F 2 J :=
  Lp.compMeasurePreservingₗᵢ 𝕜 Prod.fst ⟨measurable_fst, hfst⟩

/-- Evaluation at the actual second state of that same two-time law. -/
def evalSnd : Lp F 2 μ →ₗᵢ[𝕜] Lp F 2 J :=
  Lp.compMeasurePreservingₗᵢ 𝕜 Prod.snd ⟨measurable_snd, hsnd⟩

/-- The actual transition operator is an adjoint compression of the second
evaluation against the first evaluation. -/
def transition : Lp F 2 μ →L[𝕜] Lp F 2 μ :=
  (evalFst (𝕜 := 𝕜) μ J hfst).toContinuousLinearMap.adjoint ∘L
    (evalSnd (𝕜 := 𝕜) μ J hsnd).toContinuousLinearMap

/-- Its defining two-time correlation identity. -/
theorem transition_inner (f g : Lp F 2 μ) :
    inner 𝕜 (transition (𝕜 := 𝕜) μ J hfst hsnd f) g =
      inner 𝕜 (evalSnd (𝕜 := 𝕜) μ J hsnd f) (evalFst (𝕜 := 𝕜) μ J hfst g) := by
  dsimp only [transition, ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- Every actual stationary transition is a contraction on `L²`. -/
theorem transition_norm_le (f : Lp F 2 μ) :
    ‖transition (𝕜 := 𝕜) μ J hfst hsnd f‖ ≤ ‖f‖ := by
  have hnorm : ‖(evalFst (𝕜 := 𝕜) (F := F) μ J hfst).toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    change ‖evalFst (𝕜 := 𝕜) (F := F) μ J hfst g‖ ≤ 1 * ‖g‖
    rw [(evalFst (𝕜 := 𝕜) (F := F) μ J hfst).norm_map, one_mul]
  have hb := ((evalFst (𝕜 := 𝕜) (F := F) μ J hfst).toContinuousLinearMap.adjoint).le_opNorm
    (evalSnd (𝕜 := 𝕜) μ J hsnd f)
  rw [ContinuousLinearMap.adjoint.norm_map, (evalSnd (𝕜 := 𝕜) μ J hsnd).norm_map] at hb
  exact hb.trans (mul_le_of_le_one_left (norm_nonneg _) hnorm)

/-- The norm bound holds for the constructed bounded operator itself. -/
theorem transition_opNorm_le : ‖transition (𝕜 := 𝕜) (F := F) μ J hfst hsnd‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using transition_norm_le (𝕜 := 𝕜) μ J hfst hsnd f

variable (hswap : J.map Prod.swap = J)

/-- Time reversal acts isometrically on the actual joint sample space. -/
def reverse : Lp F 2 J →ₗᵢ[𝕜] Lp F 2 J :=
  Lp.compMeasurePreservingₗᵢ 𝕜 Prod.swap ⟨measurable_swap, hswap⟩

omit [CompleteSpace F] in
theorem reverse_evalFst (f : Lp F 2 μ) :
    reverse (𝕜 := 𝕜) J hswap (evalFst (𝕜 := 𝕜) μ J hfst f) = evalSnd (𝕜 := 𝕜) μ J hsnd f := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving (evalFst (𝕜 := 𝕜) μ J hfst f)
    (show MeasurePreserving Prod.swap J J from ⟨measurable_swap, hswap⟩)
  have h2 := Lp.coeFn_compMeasurePreserving f
    (show MeasurePreserving Prod.fst J μ from ⟨measurable_fst, hfst⟩)
  have h3 := Lp.coeFn_compMeasurePreserving f
    (show MeasurePreserving Prod.snd J μ from ⟨measurable_snd, hsnd⟩)
  have h2swap := (show MeasurePreserving Prod.swap J J from
    ⟨measurable_swap, hswap⟩).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h2swap, h3] with p hp1 hp2 hp3
  exact hp1.trans (hp2.trans hp3.symm)

omit [CompleteSpace F] in
theorem reverse_evalSnd (f : Lp F 2 μ) :
    reverse (𝕜 := 𝕜) J hswap (evalSnd (𝕜 := 𝕜) μ J hsnd f) = evalFst (𝕜 := 𝕜) μ J hfst f := by
  apply Lp.ext
  have h1 := Lp.coeFn_compMeasurePreserving (evalSnd (𝕜 := 𝕜) μ J hsnd f)
    (show MeasurePreserving Prod.swap J J from ⟨measurable_swap, hswap⟩)
  have h2 := Lp.coeFn_compMeasurePreserving f
    (show MeasurePreserving Prod.snd J μ from ⟨measurable_snd, hsnd⟩)
  have h3 := Lp.coeFn_compMeasurePreserving f
    (show MeasurePreserving Prod.fst J μ from ⟨measurable_fst, hfst⟩)
  have h2swap := (show MeasurePreserving Prod.swap J J from
    ⟨measurable_swap, hswap⟩).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h2swap, h3] with p hp1 hp2 hp3
  exact hp1.trans (hp2.trans hp3.symm)

include hswap in
/-- Actual detailed balance implies the self-adjoint correlation identity. -/
theorem transition_symmetric (f g : Lp F 2 μ) :
    inner 𝕜 (transition (𝕜 := 𝕜) μ J hfst hsnd f) g =
      inner 𝕜 f (transition (𝕜 := 𝕜) μ J hfst hsnd g) := by
  rw [transition_inner]
  have hr := (reverse (𝕜 := 𝕜) (F := F) J hswap).inner_map_map
    (evalSnd (𝕜 := 𝕜) μ J hsnd f) (evalFst (𝕜 := 𝕜) μ J hfst g)
  rw [reverse_evalSnd (𝕜 := 𝕜) μ J hfst hsnd hswap f,
    reverse_evalFst (𝕜 := 𝕜) μ J hfst hsnd hswap g] at hr
  rw [← hr]
  exact (ContinuousLinearMap.adjoint_inner_right
    (evalFst (𝕜 := 𝕜) (F := F) μ J hfst).toContinuousLinearMap f (evalSnd (𝕜 := 𝕜) μ J hsnd g)).symm

include hswap in
/-- Reversibility proves, rather than postulates, self-adjointness. -/
theorem transition_isSelfAdjoint : IsSelfAdjoint (transition (𝕜 := 𝕜) (F := F) μ J hfst hsnd) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact transition_symmetric (𝕜 := 𝕜) μ J hfst hsnd hswap

end WassersteinMixing.StationaryPair

namespace WassersteinMixing.ObservableTransition

variable {𝕜 A B : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [InnerProductSpace 𝕜 A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] [CompleteSpace B]

/-- Compress one actual isometric evaluation against another on their common
probability space. This is the `L²` conditional transition between observations. -/
def compression (initial current : A →ₗᵢ[𝕜] B) : A →L[𝕜] A :=
  initial.toContinuousLinearMap.adjoint ∘L current.toContinuousLinearMap

theorem compression_inner (initial current : A →ₗᵢ[𝕜] B) (f g : A) :
    inner 𝕜 (compression initial current f) g = inner 𝕜 (current f) (initial g) := by
  dsimp only [compression, ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- Stationarity of both evaluations proves contraction of the compressed transition. -/
theorem compression_norm_le (initial current : A →ₗᵢ[𝕜] B) (f : A) :
    ‖compression initial current f‖ ≤ ‖f‖ := by
  have hi : ‖initial.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro g
    change ‖initial g‖ ≤ 1 * ‖g‖
    rw [initial.norm_map, one_mul]
  have hb := initial.toContinuousLinearMap.adjoint.le_opNorm (current f)
  rw [ContinuousLinearMap.adjoint.norm_map, current.norm_map] at hb
  exact hb.trans (mul_le_of_le_one_left (norm_nonneg _) hi)

/-- At equal times the constructed transition is exactly the identity. -/
theorem compression_self (initial : A →ₗᵢ[𝕜] B) :
    compression initial initial = ContinuousLinearMap.id 𝕜 A := by
  exact initial.adjoint_comp_self

end WassersteinMixing.ObservableTransition
