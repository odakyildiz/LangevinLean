import PBGSO.HOLNoise

/-! # Identifying the printed HOL covariance with the Brownian Gram matrix

The scalar entries below transcribe the appendix covariance. Occurrences of
`exp(-2αh)` are written as `exp(-αh)^2`, an equivalent expression by the
exponential addition identity. The antiderivative proofs identify the
actual covariance of the constructed Brownian innovations.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace PBGSO.Methods
open KineticLangevin KineticLangevin.BrownianConvolution

def holSigma11 (α γ h : ℝ) : ℝ :=
  2 * γ ^ 2 / α ^ 3 * h - 2 * γ ^ 2 / α ^ 2 * h ^ 2 +
    2 * γ ^ 2 / (3 * α) * h ^ 3 - 4 * γ ^ 2 / α ^ 3 * h * Real.exp (-α * h) +
    γ ^ 2 / α ^ 4 * (1 - Real.exp (-α * h) ^ 2)

def holSigma12 (α γ h : ℝ) : ℝ :=
  γ ^ 2 / α ^ 3 * (α * h - 1 + Real.exp (-α * h)) ^ 2

def holSigma13 (α γ h : ℝ) : ℝ :=
  -(γ ^ 3 / α ^ 2) * h ^ 2 * (2 * Real.exp (-α * h) + 1) +
    (2 * γ ^ 3 / α ^ 3 - γ ^ 3 / α ^ 3 * Real.exp (-α * h) ^ 2 -
      4 * γ ^ 3 / α ^ 3 * Real.exp (-α * h) -
      2 * γ / α * Real.exp (-α * h)) * h +
    (3 * γ ^ 3 / (2 * α ^ 4) + γ / α ^ 2) * (1 - Real.exp (-α * h) ^ 2)

def holSigma22 (α γ h : ℝ) : ℝ :=
  2 * γ ^ 2 / α * h - 4 * γ ^ 2 / α ^ 2 * (1 - Real.exp (-α * h)) +
    γ ^ 2 / α ^ 2 * (1 - Real.exp (-α * h) ^ 2)

def holSigma23 (α γ h : ℝ) : ℝ :=
  γ ^ 3 / α ^ 2 * (Real.exp (-α * h) ^ 2 - 2 * Real.exp (-α * h) - 2) * h +
    3 * γ ^ 3 / (2 * α ^ 3) * (Real.exp (-α * h) ^ 2 - 4 * Real.exp (-α * h) + 3) +
    γ / α * (1 - Real.exp (-α * h)) ^ 2

def holSigma33 (α γ h : ℝ) : ℝ :=
  -(γ ^ 4 / α ^ 2) * h ^ 2 * Real.exp (-α * h) ^ 2 +
    (-(2 * γ ^ 2 / α) * Real.exp (-α * h) ^ 2 +
      γ ^ 4 / α ^ 3 * (-3 * Real.exp (-α * h) ^ 2 + 4 * Real.exp (-α * h) + 2)) * h +
    γ ^ 4 / (2 * α ^ 4) * (-5 * Real.exp (-α * h) ^ 2 + 16 * Real.exp (-α * h) - 11) +
    γ ^ 2 / α ^ 2 * (-3 * Real.exp (-α * h) ^ 2 + 4 * Real.exp (-α * h) - 1) +
    1 - Real.exp (-α * h) ^ 2

private theorem hol_exp_hasDeriv (α t : ℝ) :
    HasDerivAt (fun h : ℝ => Real.exp (-α * h))
      (-α * Real.exp (-α * t)) t := by
  have hl : HasDerivAt (fun h : ℝ => -α * h) (-α) t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (-α)
  convert hl.exp using 1 <;> ring

theorem holSigma22_hasDeriv (α γ t : ℝ) (hα : α ≠ 0) :
    HasDerivAt (holSigma22 α γ)
      (2 * α * (holCoefficients α γ t).μ23 ^ 2) t := by
  have he := hol_exp_hasDeriv α t
  have h1 := (hasDerivAt_const t (1 : ℝ)).sub he
  have h2 := (hasDerivAt_const t (1 : ℝ)).sub (he.pow 2)
  have hd := (((hasDerivAt_id t).const_mul (2 * γ ^ 2 / α)).sub
    (h1.const_mul (4 * γ ^ 2 / α ^ 2))).add (h2.const_mul (γ ^ 2 / α ^ 2))
  convert hd using 1
  · funext s
    dsimp [holSigma22]
  · dsimp [holCoefficients]
    field_simp
    <;> ring

theorem holSigma12_hasDeriv (α γ t : ℝ) (hα : α ≠ 0) :
    HasDerivAt (holSigma12 α γ)
      (2 * α * (holCoefficients α γ t).μ13 * (holCoefficients α γ t).μ23) t := by
  have he := hol_exp_hasDeriv α t
  have hd := (((hasDerivAt_id t).const_mul α).sub_const 1 |>.add he).pow 2
    |>.const_mul (γ ^ 2 / α ^ 3)
  convert hd using 1
  · funext s
    dsimp [holSigma12]
  · dsimp [holCoefficients]
    field_simp
    <;> ring

theorem holSigma11_hasDeriv (α γ t : ℝ) (hα : α ≠ 0) :
    HasDerivAt (holSigma11 α γ)
      (2 * α * (holCoefficients α γ t).μ13 ^ 2) t := by
  have he := hol_exp_hasDeriv α t
  have ht := hasDerivAt_id t
  have hd := (((((ht.const_mul (2 * γ ^ 2 / α ^ 3)).sub
    ((ht.pow 2).const_mul (2 * γ ^ 2 / α ^ 2))).add
    ((ht.pow 3).const_mul (2 * γ ^ 2 / (3 * α)))).sub
    ((ht.mul he).const_mul (4 * γ ^ 2 / α ^ 3))).add
    (((hasDerivAt_const t (1 : ℝ)).sub (he.pow 2)).const_mul (γ ^ 2 / α ^ 4)))
  convert hd using 1
  · funext s
    dsimp [holSigma11]
    ring
  · dsimp [holCoefficients]
    field_simp
    <;> ring

theorem holSigma13_hasDeriv (α γ t : ℝ) (hα : α ≠ 0) :
    HasDerivAt (holSigma13 α γ)
      (2 * α * (holCoefficients α γ t).μ13 * (holCoefficients α γ t).μ33) t := by
  have he := hol_exp_hasDeriv α t
  have ht := hasDerivAt_id t
  have he2 := he.pow 2
  have hA := (((ht.pow 2).const_mul (-(γ ^ 3 / α ^ 2))).mul
    ((he.const_mul 2).add_const 1))
  have hB := ((((hasDerivAt_const t (2 * γ ^ 3 / α ^ 3)).sub
    (he2.const_mul (γ ^ 3 / α ^ 3))).sub
    (he.const_mul (4 * γ ^ 3 / α ^ 3))).sub (he.const_mul (2 * γ / α)))
  have hC := ((hasDerivAt_const t (1 : ℝ)).sub he2).const_mul
    (3 * γ ^ 3 / (2 * α ^ 4) + γ / α ^ 2)
  have hd := (hA.add (hB.mul ht)).add hC
  convert hd using 1
  · funext s
    dsimp [holSigma13]
  · dsimp [holCoefficients]
    field_simp
    <;> ring

theorem holSigma23_hasDeriv (α γ t : ℝ) (hα : α ≠ 0) :
    HasDerivAt (holSigma23 α γ)
      (2 * α * (holCoefficients α γ t).μ23 * (holCoefficients α γ t).μ33) t := by
  have he := hol_exp_hasDeriv α t
  have ht := hasDerivAt_id t
  have he2 := he.pow 2
  have hA := ((((he2.sub (he.const_mul 2)).sub_const 2).const_mul
    (γ ^ 3 / α ^ 2)).mul ht)
  have hB := ((he2.sub (he.const_mul 4)).add_const 3).const_mul (3 * γ ^ 3 / (2 * α ^ 3))
  have hC := (((hasDerivAt_const t (1 : ℝ)).sub he).pow 2).const_mul (γ / α)
  have hd := (hA.add hB).add hC
  convert hd using 1
  · funext s
    dsimp [holSigma23]
  · dsimp [holCoefficients]
    field_simp
    <;> ring

theorem holSigma33_hasDeriv (α γ t : ℝ) (hα : α ≠ 0) :
    HasDerivAt (holSigma33 α γ)
      (2 * α * (holCoefficients α γ t).μ33 ^ 2) t := by
  have he := hol_exp_hasDeriv α t
  have ht := hasDerivAt_id t
  have he2 := he.pow 2
  have hA := ((ht.pow 2).mul he2).const_mul (-(γ ^ 4 / α ^ 2))
  have hB := ((he2.const_mul (-(2 * γ ^ 2 / α))).add
    ((((he2.const_mul (-3)).add (he.const_mul 4)).add_const 2).const_mul
      (γ ^ 4 / α ^ 3))).mul ht
  have hC := (((he2.const_mul (-5)).add (he.const_mul 16)).sub_const 11).const_mul
    (γ ^ 4 / (2 * α ^ 4))
  have hD := (((he2.const_mul (-3)).add (he.const_mul 4)).sub_const 1).const_mul (γ ^ 2 / α ^ 2)
  have hE := (hasDerivAt_const t (1 : ℝ)).sub he2
  have hd := (((hA.add hB).add hC).add hD).add hE
  convert hd using 1
  · funext s
    dsimp [holSigma33]
    ring
  · dsimp [holCoefficients]
    field_simp
    <;> ring

/-- The symmetric 3×3 scalar covariance printed in the appendix. Spatial
blocks are this matrix tensored with the coordinate identity. -/
def holCovarianceMatrix (α γ h : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![holSigma11 α γ h, holSigma12 α γ h, holSigma13 α γ h],
    ![holSigma12 α γ h, holSigma22 α γ h, holSigma23 α γ h],
    ![holSigma13 α γ h, holSigma23 α γ h, holSigma33 α γ h]]

/-- Select the three algorithm innovations from the four-coordinate
Brownian coupling block. -/
def holTripleKernels (α γ : ℝ) (i : Fin 3) : ℝ → ℝ :=
  holNoiseKernels α γ (Fin.castLE (by decide : 3 ≤ 4) i)

theorem continuous_holTripleKernels (α γ : ℝ) (i : Fin 3) :
    Continuous (holTripleKernels α γ i) := continuous_holNoiseKernels α γ _

private theorem holTriple_product (α γ t : ℝ) (hα : 0 ≤ α) (i j : Fin 3) :
    holTripleKernels α γ i t * holTripleKernels α γ j t =
      2 * α * ![(holCoefficients α γ t).μ13,
        (holCoefficients α γ t).μ23, (holCoefficients α γ t).μ33] i *
        ![(holCoefficients α γ t).μ13,
          (holCoefficients α γ t).μ23, (holCoefficients α γ t).μ33] j := by
  have he (i : Fin 3) : holTripleKernels α γ i t = Real.sqrt (2 * α) *
      ![(holCoefficients α γ t).μ13,
        (holCoefficients α γ t).μ23, (holCoefficients α γ t).μ33] i := by
    fin_cases i <;> rfl
  rw [he i, he j]
  calc
    _ = Real.sqrt (2 * α) ^ 2 *
        (![(holCoefficients α γ t).μ13, (holCoefficients α γ t).μ23,
          (holCoefficients α γ t).μ33] i *
        ![(holCoefficients α γ t).μ13, (holCoefficients α γ t).μ23,
          (holCoefficients α γ t).μ33] j) := by ring
    _ = _ := by rw [Real.sq_sqrt (by positivity)]; ring

/-- Differentiating every printed covariance entry gives exactly the
product of the two corresponding Brownian response kernels. -/
theorem holCovarianceMatrix_hasDeriv (α γ t : ℝ) (hα : 0 < α) (i j : Fin 3) :
    HasDerivAt (fun s => holCovarianceMatrix α γ s i j)
      (holTripleKernels α γ i t * holTripleKernels α γ j t) t := by
  rw [holTriple_product α γ t hα.le i j]
  fin_cases i <;> fin_cases j
  · simpa [holCovarianceMatrix, pow_two, mul_assoc] using holSigma11_hasDeriv α γ t hα.ne'
  · simpa [holCovarianceMatrix] using holSigma12_hasDeriv α γ t hα.ne'
  · simpa [holCovarianceMatrix] using holSigma13_hasDeriv α γ t hα.ne'
  · simpa [holCovarianceMatrix, mul_comm, mul_left_comm, mul_assoc] using
      holSigma12_hasDeriv α γ t hα.ne'
  · simpa [holCovarianceMatrix, pow_two, mul_assoc] using holSigma22_hasDeriv α γ t hα.ne'
  · simpa [holCovarianceMatrix] using holSigma23_hasDeriv α γ t hα.ne'
  · simpa [holCovarianceMatrix, mul_comm, mul_left_comm, mul_assoc] using
      holSigma13_hasDeriv α γ t hα.ne'
  · simpa [holCovarianceMatrix, mul_comm, mul_left_comm, mul_assoc] using
      holSigma23_hasDeriv α γ t hα.ne'
  · simpa [holCovarianceMatrix, pow_two, mul_assoc] using holSigma33_hasDeriv α γ t hα.ne'

/-- All printed covariance entries start from zero. -/
theorem holCovarianceMatrix_zero (α γ : ℝ) : holCovarianceMatrix α γ 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holCovarianceMatrix, holSigma11, holSigma12, holSigma13,
      holSigma22, holSigma23, holSigma33]

/-- The printed covariance equals the actual integral Gram covariance of
the implementation response kernels. This establishes its validity rather
than assuming a positive-semidefinite matrix. -/
theorem holCovarianceMatrix_eq_gram (α γ h : ℝ) (hα : 0 < α) :
    holCovarianceMatrix α γ h = gramCovariance (holTripleKernels α γ) h := by
  ext i j
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => holCovarianceMatrix_hasDeriv α γ t hα i j)
    (((continuous_holTripleKernels α γ i).mul
      (continuous_holTripleKernels α γ j)).intervalIntegrable 0 h)
  have hz : holCovarianceMatrix α γ 0 i j = 0 := by rw [holCovarianceMatrix_zero]; rfl
  simpa only [hz, sub_zero, gramCovariance] using hi.symm

/-- The appendix's covariance is positive semidefinite at every physical
positive `α` and every nonnegative step, for any real `γ`. -/
theorem holCovarianceMatrix_posSemidef (α γ h : ℝ) (hα : 0 < α) (hh : 0 ≤ h) :
    (holCovarianceMatrix α γ h).PosSemidef := by
  rw [holCovarianceMatrix_eq_gram α γ h hα]
  exact gramCovariance_posSemidef _ (continuous_holTripleKernels α γ) hh

/-- The three actual Brownian-segment innovations have exactly the
Gaussian covariance prescribed by the implementation in the paper. -/
theorem holTripleNoise_jointLaw (α γ : ℝ) (hα : 0 < α) (a h : ℝ≥0) :
    ProbabilityTheory.HasLaw (fun ω => WithLp.toLp 2
      (fun i : Fin 3 => segmentConvolutionLp (holTripleKernels α γ i)
        (continuous_holTripleKernels α γ i) a h ω))
      (ProbabilityTheory.multivariateGaussian 0 (holCovarianceMatrix α γ (h : ℝ)))
      probability := by
  rw [holCovarianceMatrix_eq_gram α γ (h : ℝ) hα]
  exact segmentConvolutionLp_jointLaw _ (continuous_holTripleKernels α γ) a h

/-- The actual three-innovation array is independent over all iteration
and spatial-coordinate indices and has the paper's Gaussian block law. -/
theorem holTripleNoiseArray_law (ι : Type*) (α γ : ℝ) (hα : 0 < α) (h : ℝ≥0) :
    ProbabilityTheory.HasLaw (fun ω : ULA.CanonicalBrownian.VectorSample ι =>
      fun p : (n : ℕ) × ι =>
        vectorGridBlock ι (holTripleKernels α γ) (continuous_holTripleKernels α γ)
          h p.fst ω p.snd)
      (Measure.infinitePi (fun _ : (n : ℕ) × ι =>
        ProbabilityTheory.multivariateGaussian 0 (holCovarianceMatrix α γ (h : ℝ))))
      (ULA.CanonicalBrownian.vectorProbability ι) := by
  rw [holCovarianceMatrix_eq_gram α γ (h : ℝ) hα]
  exact vectorGridBlock_array_law ι _ (continuous_holTripleKernels α γ) h

/-- This identity relates the squared-exponential notation in this file to
the appendix's `exp(-2αh)` notation. -/
theorem hol_covariance_double_exp (α h : ℝ) :
    Real.exp (-α * h) ^ 2 = Real.exp (-2 * α * h) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

end PBGSO.Methods
