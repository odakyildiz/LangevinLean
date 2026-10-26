import PBGSO.MethodBrownianMatching

/-! # Exact segment equations for actual global method trajectories
Subtracting two original integral equations and shifting the integration
variable gives the actual step equation. The physical Brownian input over a
step is identified with the implementation's coupled Gaussian innovation.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace PBGSO.MethodSegments
open Methods

section ExactShift
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The exact step equation follows from the actual global integral equation. -/
theorem integral_shift (Y F B : ℝ → E) (hF : Continuous F)
    (heq : ∀ t, 0 ≤ t → Y t - Y 0 = (∫ r in 0..t, F r) + B t)
    (a h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) :
    Y (a + h) - Y a = (∫ r in 0..h, F (a + r)) + (B (a + h) - B a) := by
  have hi : (∫ r in 0..a + h, F r) - (∫ r in 0..a, F r) = ∫ r in a..a + h, F r := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hF.intervalIntegrable 0 a) (hF.intervalIntegrable a (a + h))]
    abel
  have hy : Y (a + h) - Y a = (∫ r in a..a + h, F r) + (B (a + h) - B a) := by
    calc
      _ = (Y (a + h) - Y 0) - (Y a - Y 0) := by abel
      _ = _ := by rw [heq (a + h) (add_nonneg ha hh), heq a ha, ← hi]; abel
  rw [hy]
  have hshift : (∫ r in a..a + h, F r) = ∫ r in 0..h, F (a + r) := by
    simpa only [add_zero] using (intervalIntegral.integral_comp_add_left
      (f := F) (a := 0) (b := h) a).symm
  rw [hshift]

end ExactShift

section Inputs
variable {Ω A I : Type*} [MeasurableSpace Ω] [Fintype I]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

/-- The complete physical kinetic input, with zero optimiser forcing and
zero position forcing. -/
def momentumInput (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (γ t : ℝ) : ((Lp A 2 Q × Lp (EuclideanSpace ℝ I) 2 Q) ×
      (Lp A 2 Q × Lp (EuclideanSpace ℝ I) 2 Q)) :=
  ((0, Real.sqrt γ • ULA.brownianLangevinNoise Q W hW 0 t), (0, 0))

theorem brownianNoise_increment (W : I → ℝ≥0 → Ω → ℝ)
    (hW : ∀ i, IsPreBrownianReal (W i) Q) (a h : ℝ) :
    ULA.brownianLangevinNoise Q W hW 0 (a + h) - ULA.brownianLangevinNoise Q W hW 0 a =
      ULA.brownianLangevinNoise Q W hW a h := by
  simp only [ULA.brownianLangevinNoise, zero_add]
  module

/-- The global physical input over a kinetic step is precisely the actual
Gaussian comparison innovation used in the method error proof. -/
theorem momentumInput_increment
    (W : I → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) Q)
    (γ h : ℝ) (hγ : 0 ≤ γ) (hh : 0 < h) (k : ℕ) :
    momentumInput (A := A) Q W hW γ ((k : ℝ) * h + h) - momentumInput Q W hW γ ((k : ℝ) * h) =
      (momentumGaussianIncrement (Θ := Lp A 2 Q) Q W hW γ h k, (0, 0)) := by
  rw [momentumGaussianIncrement_brownian Q W hW γ h hγ hh k]
  change ((0 - 0, Real.sqrt γ • ULA.brownianLangevinNoise Q W hW 0 ((k : ℝ) * h + h) -
      Real.sqrt γ • ULA.brownianLangevinNoise Q W hW 0 ((k : ℝ) * h)), (0 - 0, 0 - 0)) = _
  rw [← smul_sub, brownianNoise_increment]
  simp

variable [DecidableEq I]
  {f : Ω → ULA.CanonicalBrownian.VectorSample I}
  (hf : MeasurePreserving f Q (ULA.CanonicalBrownian.vectorProbability I))

/-- Physical HOL input on the actual initial/noise source: only its final
sampler auxiliary receives Brownian forcing. -/
def higherOrderInput (α t : ℝ) : HOLState (Lp A 2 Q) (Lp (EuclideanSpace ℝ I) 2 Q) :=
  holBrownianIncrement (Real.sqrt α • ULA.brownianLangevinNoise Q
    (canonicalPullbackCoordinate I hf) (canonicalPullbackCoordinate_isPreBrownian I hf) 0 t)

/-- The physical HOL input over a step is the actual fourth innovation of
the same four-kernel Gaussian block as the implementation. -/
theorem higherOrderInput_increment (α γ : ℝ) (hα : 0 ≤ α) (h : ℝ≥0) (k : ℕ) :
    higherOrderInput (A := A) Q hf α ((k : ℝ) * (h : ℝ) + (h : ℝ)) -
      higherOrderInput Q hf α ((k : ℝ) * (h : ℝ)) =
        holBrownianIncrement (higherOrderPullbackGaussianIncrement I hf α γ h k) := by
  have hn : higherOrderPullbackGaussianIncrement I hf α γ h k =
      Real.sqrt α • ULA.brownianLangevinNoise Q
        (canonicalPullbackCoordinate I hf) (canonicalPullbackCoordinate_isPreBrownian I hf)
        ((k : ℝ) * (h : ℝ)) (h : ℝ) :=
    higherOrderPullbackGaussianIncrement_brownian Q hf α γ hα ((k : ℝ≥0) * h) h
  rw [hn]
  change (0 - 0, 0 - 0, 0 - 0,
    Real.sqrt α • ULA.brownianLangevinNoise Q (canonicalPullbackCoordinate I hf)
      (canonicalPullbackCoordinate_isPreBrownian I hf) 0 ((k : ℝ) * (h : ℝ) + (h : ℝ)) -
    Real.sqrt α • ULA.brownianLangevinNoise Q (canonicalPullbackCoordinate I hf)
      (canonicalPullbackCoordinate_isPreBrownian I hf) 0 ((k : ℝ) * (h : ℝ))) = _
  rw [← smul_sub, brownianNoise_increment]
  simp [holBrownianIncrement]

end Inputs
end PBGSO.MethodSegments
