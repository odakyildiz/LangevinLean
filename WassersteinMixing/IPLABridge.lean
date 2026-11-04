import WassersteinMixing.IsometryTransport
import WassersteinMixing.IPLACurvature
import WassersteinMixing.IPLARates
import IPLA.ULAAdapter

set_option linter.style.header false

/-! # The sharp actual-law Wasserstein estimate in IPLA coordinates

The theorem for standard finite Euclidean coordinates is transferred by a
proved isometry. The lifted potential, invariant law, transition, transport
metric, and dimension scaling are the actual objects of the IPLA algorithm.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace WassersteinMixing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The constructed Gaussian ULA invariant law in the original coordinate type. -/
def coordinateInvariantLaw (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V) : Measure H :=
  (invariantLaw P (V ∘ e.symm) (potentialAssumptions_reindex P e V hV)).map e.symm

omit [FiniteDimensional ℝ H] in
/-- Changing back to Euclidean coordinates recovers exactly the constructed
invariant probability measure. -/
theorem coordinateInvariantLaw_map (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V) :
    (coordinateInvariantLaw P e V hV).map e =
      invariantLaw P (V ∘ e.symm) (potentialAssumptions_reindex P e V hV) := by
  simp [coordinateInvariantLaw, Measure.map_map e.continuous.measurable
    e.symm.continuous.measurable, Function.comp_def]

omit [FiniteDimensional ℝ H] [BorelSpace H] in
/-- The pulled-back invariant law is a genuine probability measure. -/
theorem coordinateInvariantLaw_isProbability (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V) :
    IsProbabilityMeasure (coordinateInvariantLaw P e V hV) := by
  unfold coordinateInvariantLaw
  infer_instance

/-- Its second moment is proved by the coordinate isometry. -/
theorem coordinateInvariantLaw_memLp (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V) :
    MemLp (id : H → H) 2 (coordinateInvariantLaw P e V hV) := by
  exact memLp_id_map_isometry e.symm _
    (invariantLaw_memLp P (V ∘ e.symm) (potentialAssumptions_reindex P e V hV))

/-- The pulled-back law is invariant for the actual Gaussian ULA transition. -/
theorem coordinateInvariantLaw_invariant (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V) :
    ULA.ulaLawStep V P.step (coordinateInvariantLaw P e V hV) =
      coordinateInvariantLaw P e V hV := by
  let := coordinateInvariantLaw_isProbability P e V hV
  apply e.toMeasurableEquiv.measurableEmbedding.map_injective
  change (ULA.ulaLawStep V P.step (coordinateInvariantLaw P e V hV)).map e =
    (coordinateInvariantLaw P e V hV).map e
  rw [ulaLawStep_map_isometry e V (hV.regularity.differentiable (by norm_num))
    ⟨P.beta, P.beta_pos.le⟩ hV.gradientLipschitz, coordinateInvariantLaw_map,
    invariantLaw_invariant]

/-- The original theorem's bias conclusion in any isometric coordinate type. -/
theorem coordinate_bias_bound (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V) :
    ULA.wasserstein2Real (ULA.gibbsMeasure V) (coordinateInvariantLaw P e V hV) ≤ P.bias := by
  rw [← wasserstein2Real_map_isometry e, gibbsMeasure_map_isometry,
    coordinateInvariantLaw_map]
  exact bias_from_comparison (potentialAssumptions_reindex P e V hV)
    (actualULAComparison P (V ∘ e.symm) (potentialAssumptions_reindex P e V hV))

/-- The finite-time theorem acts on the original, independent-Gaussian laws. -/
theorem coordinate_convergence_bound (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V)
    (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ) (n : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≤
      P.contraction ^ n * ULA.wasserstein2Real μ (coordinateInvariantLaw P e V hV) + P.bias := by
  rw [← wasserstein2Real_map_isometry e ((ULA.ulaLawStep V P.step)^[n] μ),
    ula_iterate_map_isometry P e V hV, gibbsMeasure_map_isometry,
    ← wasserstein2Real_map_isometry e μ, coordinateInvariantLaw_map]
  exact convergence_from_comparison (potentialAssumptions_reindex P e V hV)
    (actualULAComparison P (V ∘ e.symm) (potentialAssumptions_reindex P e V hV))
    (μ.map e) (memLp_id_map_isometry e μ hμ) n

/-- Finite output transport is established before using its real value. -/
theorem coordinate_convergence_finite (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V)
    (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ) (n : ℕ) :
    ULA.wasserstein2 ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≠ ⊤ := by
  let W := V ∘ e.symm
  have hW := potentialAssumptions_reindex P e V hV
  let := actualTarget_isProbability P W hW
  have hfinite := ULA.wasserstein2_ne_top_of_memLp (μ.map e) (ULA.gibbsMeasure W)
    (memLp_id_map_isometry e μ hμ) (actualTarget_memLp P W hW)
  have hout := ULA.Hilbert.dalalyan_output_finite W P.alpha P.step
    ⟨P.beta, P.beta_pos.le⟩ P.alpha_pos (hW.regularity.differentiable (by norm_num))
    hW.strongConvexity hW.gradientLipschitz P.step_pos (μ.map e) hfinite n
  rw [← ula_iterate_map_isometry P e V hV, ← gibbsMeasure_map_isometry e V,
    wasserstein2_map_isometry] at hout
  exact hout

/-- Starting at the Gibbs law, the actual finite-time displacement is bounded
by the same corrector budget as the invariant bias. -/
theorem coordinate_stationary_start_bound (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V) (n : ℕ) :
    ULA.wasserstein2Real (ULA.gibbsMeasure V)
      ((ULA.ulaLawStep V P.step)^[n] (ULA.gibbsMeasure V)) ≤ P.bias := by
  let := ULA.isProbabilityMeasure_gibbsMeasure V P.alpha P.alpha_pos
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity
  rw [← wasserstein2Real_map_isometry e,
    ula_iterate_map_isometry P e V hV, gibbsMeasure_map_isometry]
  exact (actualULAComparison P (V ∘ e.symm)
    (potentialAssumptions_reindex P e V hV)).stationary_start_bound n

/-- The stationary-start comparison supplies finite transport before the
real-valued cost is used. -/
theorem coordinate_stationary_start_finite (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V) (n : ℕ) :
    ULA.wasserstein2 (ULA.gibbsMeasure V)
      ((ULA.ulaLawStep V P.step)^[n] (ULA.gibbsMeasure V)) ≠ ⊤ := by
  let := ULA.isProbabilityMeasure_gibbsMeasure V P.alpha P.alpha_pos
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity
  rw [← wasserstein2_map_isometry e,
    ula_iterate_map_isometry P e V hV, gibbsMeasure_map_isometry]
  exact (actualULAComparison P (V ∘ e.symm)
    (potentialAssumptions_reindex P e V hV)).stationary_start_finite n

/-- Measuring the initial distance to the Gibbs target retains the sharp
coefficient: compare the two actual iterates before using the stationary-start
Poisson bound, so no extra copy of the bias is introduced. -/
theorem coordinate_convergence_target_bound_sharp (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V)
    (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ) (n : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≤
      P.contraction ^ n * ULA.wasserstein2Real μ (ULA.gibbsMeasure V) +
        P.bias := by
  let := ULA.isProbabilityMeasure_gibbsMeasure V P.alpha P.alpha_pos
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity
  have hπ := ULA.memLp_id_gibbsMeasure V P.alpha P.alpha_pos
    (hV.regularity.differentiable (by norm_num)) hV.strongConvexity
  have hfinite := ULA.wasserstein2_ne_top_of_memLp μ (ULA.gibbsMeasure V) hμ hπ
  let := ula_iterate_isProbability P V hV μ n
  let := ula_iterate_isProbability P V hV (ULA.gibbsMeasure V) n
  have hstationary := coordinate_stationary_start_finite P e V hV n
  rw [wasserstein2_symm] at hstationary
  have ht := wasserstein2Real_triangle ((ULA.ulaLawStep V P.step)^[n] μ)
    ((ULA.ulaLawStep V P.step)^[n] (ULA.gibbsMeasure V)) (ULA.gibbsMeasure V)
    (ula_iterate_transport_finite P V hV μ _ hfinite n) hstationary
  have hb : ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] (ULA.gibbsMeasure V))
      (ULA.gibbsMeasure V) ≤ P.bias := by
    rw [wasserstein2Real_symm]
    exact coordinate_stationary_start_bound P e V hV n
  exact ht.trans (add_le_add
    (ula_iterate_wasserstein2Real_le P V hV μ _ hfinite n) hb)

/-- The weaker invariant-triangle form also follows from the sharper
stationary-start estimate. -/
theorem coordinate_convergence_target_bound (P : Parameters)
    (e : H ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin P.dimension))
    (V : H → ℝ) (hV : PotentialAssumptions P V)
    (μ : Measure H) [IsProbabilityMeasure μ] (hμ : MemLp (id : H → H) 2 μ) (n : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep V P.step)^[n] μ) (ULA.gibbsMeasure V) ≤
      P.contraction ^ n * ULA.wasserstein2Real μ (ULA.gibbsMeasure V) +
        (1 + P.contraction ^ n) * P.bias := by
  have hs := coordinate_convergence_target_bound_sharp P e V hV μ hμ n
  have hp := mul_nonneg (pow_nonneg P.contraction_nonneg n) P.bias_nonneg
  nlinarith

/-- The coordinate type of the actual IPLA state has precisely the claimed
finite Euclidean dimension. -/
def iplaCoordinates (N dθ dx : ℕ) :
    IPLA.State N dθ dx ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (dθ + N * dx)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Fintype.equivFinOfCardEq (by simp))

/-- The sharp Wasserstein rate of the scaled particle chain, with every
construction derived from the original joint potential and the explicit
twice-continuous-differentiability premise. -/
theorem ipla_wasserstein_bound
    {N dθ dx : ℕ} {U : IPLA.Joint dθ dx → ℝ} {m γ : ℝ} {L : ℝ≥0}
    (hN : 0 < N) (hm : 0 < m) (hmL : m ≤ L) (hγ : 0 < γ) (hγL : γ * L ≤ 1)
    (hU : ContDiff ℝ 2 U) (hsc : StrongConvexOn univ m U)
    (hLip : LipschitzWith L (gradient U))
    (μ : Measure (IPLA.State N dθ dx)) [IsProbabilityMeasure μ]
    (hμ : MemLp (id : IPLA.State N dθ dx → IPLA.State N dθ dx) 2 μ) (k : ℕ) :
    ULA.wasserstein2Real ((ULA.ulaLawStep (@IPLA.potential N dθ dx U) (γ / N))^[k] μ)
      (ULA.gibbsMeasure (@IPLA.potential N dθ dx U)) ≤
      (1 - m * γ) ^ k * ULA.wasserstein2Real μ
        (coordinateInvariantLaw (iplaParameters N dθ dx m L γ hN hm hmL hγ hγL)
          (iplaCoordinates N dθ dx) (IPLA.potential U)
          (ipla_potentialAssumptions hN hm hmL hγ hγL hU hsc hLip)) +
        iplaLinearBias m L γ (iplaEffectiveDimension N dθ dx) := by
  have hb := coordinate_convergence_bound
    (iplaParameters N dθ dx m L γ hN hm hmL hγ hγL)
    (iplaCoordinates N dθ dx) (IPLA.potential U)
    (ipla_potentialAssumptions hN hm hmL hγ hγL hU hsc hLip) μ hμ k
  have hn : (N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hN)
  have hq : (N : ℝ) * m * (γ / N) = m * γ := by field_simp
  simpa only [Parameters.contraction, Parameters.bias, Parameters.condition,
    iplaParameters, hq, ipla_lifted_bias_eq N dθ dx hN] using hb

end WassersteinMixing
