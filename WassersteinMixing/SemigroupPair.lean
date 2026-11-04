import WassersteinMixing.SemigroupContinuity

/-! # Reversible pair laws give self-adjoint observable compression -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory Filter

namespace WassersteinMixing.StationaryObservables

variable {𝕜 E F Ω : Type*} [RCLike 𝕜] [MeasurableSpace Ω]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  (μ : Measure E) (Q : Measure Ω)

omit [SecondCountableTopology E] [CompleteSpace F] in
/-- Observable correlations depend only on the genuine joint state law. -/
theorem evaluation_inner_pair (X Y : Lp E 2 Q) (hX : Q.map X = μ) (hY : Q.map Y = μ)
    (f g : Lp F 2 μ) :
    inner 𝕜 (evaluation (𝕜 := 𝕜) μ Q Y hY f) (evaluation (𝕜 := 𝕜) μ Q X hX g) =
      ∫ p, inner 𝕜 (f p.2) (g p.1) ∂Q.map (fun ω ↦ (X ω, Y ω)) := by
  rw [L2.inner_def, integral_map (by fun_prop) (by fun_prop)]
  apply integral_congr_ae
  have hx : MeasurePreserving X Q μ := ⟨(Lp.stronglyMeasurable X).measurable, hX⟩
  have hy : MeasurePreserving Y Q μ := ⟨(Lp.stronglyMeasurable Y).measurable, hY⟩
  filter_upwards [Lp.coeFn_compMeasurePreserving f hy,
    Lp.coeFn_compMeasurePreserving g hx] with ω hf hg
  exact congrArg₂ (inner 𝕜) hf hg

omit [SecondCountableTopology E] in
/-- Two actual realizations with the same anchored state law define the same
compressed observable transition. -/
theorem compression_eq_of_pair_law {Ω' : Type*} [MeasurableSpace Ω'] (Q' : Measure Ω')
    (X Y : Lp E 2 Q) (X' Y' : Lp E 2 Q')
    (hX : Q.map X = μ) (hY : Q.map Y = μ)
    (hX' : Q'.map X' = μ) (hY' : Q'.map Y' = μ)
    (hpair : Q.map (fun ω ↦ (X ω, Y ω)) = Q'.map (fun ω ↦ (X' ω, Y' ω))) :
    ObservableTransition.compression (evaluation (𝕜 := 𝕜) (F := F) μ Q X hX)
      (evaluation μ Q Y hY) =
    ObservableTransition.compression (evaluation μ Q' X' hX') (evaluation μ Q' Y' hY') := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right 𝕜
  intro g
  rw [ObservableTransition.compression_inner, ObservableTransition.compression_inner,
    evaluation_inner_pair, evaluation_inner_pair, hpair]

omit [SecondCountableTopology E] in
/-- A reversible actual joint law proves self-adjointness of the compressed
transition without assuming an abstract transition-kernel representation. -/
theorem compression_isSelfAdjoint_of_pair_swap (X Y : Lp E 2 Q)
    (hX : Q.map X = μ) (hY : Q.map Y = μ)
    (hswap : (Q.map (fun ω ↦ (X ω, Y ω))).map Prod.swap =
      Q.map (fun ω ↦ (X ω, Y ω))) :
    IsSelfAdjoint (ObservableTransition.compression
      (evaluation (𝕜 := 𝕜) (F := F) μ Q X hX) (evaluation μ Q Y hY)) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner 𝕜 (ObservableTransition.compression
    (evaluation (𝕜 := 𝕜) μ Q X hX) (evaluation μ Q Y hY) f) g = _
  rw [ObservableTransition.compression_inner (𝕜 := 𝕜)
    (evaluation μ Q X hX) (evaluation μ Q Y hY) f g, evaluation_inner_pair]
  have hrev : Q.map (fun ω ↦ (Y ω, X ω)) = Q.map (fun ω ↦ (X ω, Y ω)) := by
    rw [← hswap, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hr := evaluation_inner_pair (𝕜 := 𝕜) μ Q Y X hY hX f g
  rw [hrev] at hr
  rw [← hr]
  dsimp only [ObservableTransition.compression, ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.adjoint_inner_right
    (evaluation (𝕜 := 𝕜) (F := F) μ Q X hX).toContinuousLinearMap f
    (evaluation (𝕜 := 𝕜) μ Q Y hY g)).symm

end WassersteinMixing.StationaryObservables
