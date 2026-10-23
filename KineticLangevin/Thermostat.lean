import KineticLangevin.OBABO
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! # The Gaussian thermostat preserves its thermal velocity law

This is an actual pushforward equality for independent Gaussian inputs, proved
by characteristic functions. It establishes invariance of the O substep, not
invariance of the full kinetic diffusion or of the full OBABO chain.
-/

noncomputable section
set_option linter.style.header false
open MeasureTheory ProbabilityTheory
namespace KineticLangevin
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- An independent linear combination of standard Gaussians is standard
Gaussian precisely when its two squared coefficients sum to one. -/
theorem stdGaussian_linear_combination (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((stdGaussian E).prod (stdGaussian E)).map (fun z ↦ a • z.1 + b • z.2) =
      stdGaussian E := by
  let A : E × E →L[ℝ] E := a • ContinuousLinearMap.fst ℝ E E +
    b • ContinuousLinearMap.snd ℝ E E
  change ((stdGaussian E).prod (stdGaussian E)).map A = stdGaussian E
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_prod]
  have hleft : (L.comp A).comp (ContinuousLinearMap.inl ℝ E E) = a • L := by
    ext x
    simp [A]
  have hright : (L.comp A).comp (ContinuousLinearMap.inr ℝ E E) = b • L := by
    ext x
    simp [A]
  rw [hleft, hright, charFunDual_stdGaussian, charFunDual_stdGaussian,
    charFunDual_stdGaussian, ← Complex.exp_add]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs]
  have heq : -(a ^ 2 * ‖L‖ ^ 2) / 2 + -(b ^ 2 * ‖L‖ ^ 2) / 2 =
      -‖L‖ ^ 2 / 2 := by nlinarith [hab]
  norm_cast
  simpa only [mul_pow, sq_abs] using heq

/-- The O half-step leaves its standard Gaussian velocity distribution
unchanged, using exactly the damping and variance in OBABO. -/
theorem obabo_thermostat_preserves_standardGaussian {γ h : ℝ}
    (hγ : 0 ≤ γ) (hh : 0 ≤ h) :
    ((stdGaussian E).prod (stdGaussian E)).map
      (fun z ↦ obaboDamping γ h • z.1 + Real.sqrt (obaboVariance γ h) • z.2) =
      stdGaussian E := by
  apply stdGaussian_linear_combination
  rw [Real.sq_sqrt (obaboVariance_nonneg hγ hh)]
  dsimp [obaboVariance]
  ring

end KineticLangevin
