import KineticLangevin.Coefficients
import KineticLangevin.Integrator
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.InfinitePi

/-!
# Gaussian innovation laws for kinetic Langevin

The covariances in the algorithms are Gram matrices. This file constructs
actual Gaussian probability measures with precisely these covariances and
an independent stream of such Gaussian blocks. A block contains the two (or
four) correlated integrals for one spatial coordinate; blocks at distinct
iteration-coordinate pairs are independent.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace KineticLangevin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The centered Gaussian law associated with a finite family of kernels. -/
def kernelGaussian (kernels : ι → ℝ → ℝ) (h : ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  multivariateGaussian 0 (gramCovariance kernels h)

instance kernelGaussian_isGaussian (kernels : ι → ℝ → ℝ) (h : ℝ) :
    IsGaussian (kernelGaussian kernels h) := by
  unfold kernelGaussian
  infer_instance

instance kernelGaussian_isProbabilityMeasure (kernels : ι → ℝ → ℝ) (h : ℝ) :
    IsProbabilityMeasure (kernelGaussian kernels h) := by infer_instance

/-- The vector mean is zero, not an assumption on an unspecified noise source. -/
theorem kernelGaussian_mean (kernels : ι → ℝ → ℝ) (h : ℝ) :
    ∫ x, x ∂kernelGaussian kernels h = 0 :=
  integral_id_multivariateGaussian

/-- Every innovation block has a finite second moment. -/
theorem kernelGaussian_memLp (kernels : ι → ℝ → ℝ) (h : ℝ) :
    MemLp (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
      (kernelGaussian kernels h) :=
  IsGaussian.memLp_two_id

theorem kernelGaussian_coordinate_mean (kernels : ι → ℝ → ℝ) (h : ℝ) (i : ι) :
    ∫ x, x i ∂kernelGaussian kernels h = 0 := by
  change (∫ x, EuclideanSpace.proj i x ∂kernelGaussian kernels h) = 0
  rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
    kernelGaussian_mean]
  simp

theorem kernelGaussian_coordinate_memLp (kernels : ι → ℝ → ℝ) (h : ℝ) (i : ι) :
    MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 (kernelGaussian kernels h) := by
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (kernelGaussian_memLp kernels h)

/-- Each covariance is exactly the Brownian convolution covariance in the paper. -/
theorem kernelGaussian_covariance (kernels : ι → ℝ → ℝ)
    (hc : ∀ i, Continuous (kernels i)) {h : ℝ} (hh : 0 ≤ h) (i j : ι) :
    cov[fun x => x i, fun x => x j; kernelGaussian kernels h] =
      ∫ t in 0..h, kernels i t * kernels j t :=
  covariance_eval_multivariateGaussian (gramCovariance_posSemidef kernels hc hh) i j

theorem kernelGaussian_variance (kernels : ι → ℝ → ℝ)
    (hc : ∀ i, Continuous (kernels i)) {h : ℝ} (hh : 0 ≤ h) (i : ι) :
    Var[fun x => x i; kernelGaussian kernels h] =
      ∫ t in 0..h, kernels i t ^ 2 := by
  simpa only [kernelGaussian, gramCovariance, pow_two] using
    (variance_eval_multivariateGaussian (μ := 0)
      (gramCovariance_posSemidef kernels hc hh) i)

theorem kernelGaussian_secondMoment (kernels : ι → ℝ → ℝ)
    (hc : ∀ i, Continuous (kernels i)) {h : ℝ} (hh : 0 ≤ h) (i : ι) :
    (∫ x, (x i) ^ 2 ∂kernelGaussian kernels h) = ∫ t in 0..h, kernels i t ^ 2 := by
  have hv := kernelGaussian_variance kernels hc hh i
  rw [variance_eq_integral (by fun_prop), kernelGaussian_coordinate_mean] at hv
  simpa only [sub_zero] using hv

theorem kernelGaussian_crossMoment (kernels : ι → ℝ → ℝ)
    (hc : ∀ i, Continuous (kernels i)) {h : ℝ} (hh : 0 ≤ h) (i j : ι) :
    (∫ x, x i * x j ∂kernelGaussian kernels h) =
      ∫ t in 0..h, kernels i t * kernels j t := by
  have hv := kernelGaussian_covariance kernels hc hh i j
  simpa only [covariance, kernelGaussian_coordinate_mean, sub_zero] using hv

/-- The law of a first-order innovation block. -/
def klmcGaussian (γ h : ℝ) : Measure (EuclideanSpace ℝ (Fin 2)) :=
  kernelGaussian (klmcKernels γ) h

/-- The law of a second-order innovation block. -/
def klmc2Gaussian (γ h : ℝ) : Measure (EuclideanSpace ℝ (Fin 4)) :=
  kernelGaussian (klmc2Kernels γ) h

instance klmcGaussian_isProbabilityMeasure (γ h : ℝ) :
    IsProbabilityMeasure (klmcGaussian γ h) := by
  unfold klmcGaussian
  infer_instance

instance klmc2Gaussian_isProbabilityMeasure (γ h : ℝ) :
    IsProbabilityMeasure (klmc2Gaussian γ h) := by
  unfold klmc2Gaussian
  infer_instance

/-- One independent Gaussian block per iteration and spatial coordinate. -/
def kernelNoisePath (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ) :
    Measure (ℕ × Fin d → EuclideanSpace ℝ ι) :=
  Measure.infinitePi (fun _ => kernelGaussian kernels h)

instance kernelNoisePath_isProbabilityMeasure (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ) :
    IsProbabilityMeasure (kernelNoisePath d kernels h) := by
  unfold kernelNoisePath
  infer_instance

/-- Every block in the canonical stream has the prescribed correlated law. -/
theorem kernelNoisePath_block_law (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ)
    (n : ℕ) (i : Fin d) :
    HasLaw (fun ω : ℕ × Fin d → EuclideanSpace ℝ ι => ω (n, i))
      (kernelGaussian kernels h) (kernelNoisePath d kernels h) where
  aemeasurable := (measurable_pi_apply (n, i)).aemeasurable
  map_eq := Measure.infinitePi_map_eval _ _

/-- Correlation is retained inside each block; distinct blocks are independent. -/
theorem kernelNoisePath_independent (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ) :
    iIndepFun (fun p : ℕ × Fin d =>
      fun ω : ℕ × Fin d → EuclideanSpace ℝ ι => ω p)
      (kernelNoisePath d kernels h) :=
  iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

theorem kernelNoisePath_block_memLp (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ)
    (n : ℕ) (i : Fin d) :
    MemLp (fun ω : ℕ × Fin d → EuclideanSpace ℝ ι => ω (n, i)) 2
      (kernelNoisePath d kernels h) :=
  (kernelGaussian_memLp kernels h).comp_measurePreserving
    (measurePreserving_eval_infinitePi _ (n, i))

theorem kernelNoisePath_block_mean (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ)
    (n : ℕ) (i : Fin d) :
    ∫ ω, ω (n, i) ∂kernelNoisePath d kernels h = 0 := by
  rw [← kernelGaussian_mean kernels h]
  exact (kernelNoisePath_block_law d kernels h n i).integral_comp
    (f := id) measurable_id.aestronglyMeasurable

/-- Canonical extension carrying an arbitrary initial condition and an
independent stream of all future Gaussian blocks. -/
def kernelInitialExtension {S : Type*} [MeasurableSpace S]
    (initial : Measure S) (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ) :
    Measure (S × (ℕ × Fin d → EuclideanSpace ℝ ι)) :=
  initial.prod (kernelNoisePath d kernels h)

instance kernelInitialExtension_isProbabilityMeasure {S : Type*} [MeasurableSpace S]
    (initial : Measure S) [IsProbabilityMeasure initial]
    (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ) :
    IsProbabilityMeasure (kernelInitialExtension initial d kernels h) := by
  unfold kernelInitialExtension
  infer_instance

theorem kernelInitialExtension_initial_law {S : Type*} [MeasurableSpace S]
    (initial : Measure S) [IsProbabilityMeasure initial]
    (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ) :
    HasLaw Prod.fst initial (kernelInitialExtension initial d kernels h) :=
  measurePreserving_fst.hasLaw

theorem kernelInitialExtension_noise_law {S : Type*} [MeasurableSpace S]
    (initial : Measure S) [IsProbabilityMeasure initial]
    (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ) :
    HasLaw Prod.snd (kernelNoisePath d kernels h)
      (kernelInitialExtension initial d kernels h) :=
  measurePreserving_snd.hasLaw

theorem kernelInitialExtension_independent {S : Type*} [MeasurableSpace S]
    (initial : Measure S) [IsProbabilityMeasure initial]
    (d : ℕ) (kernels : ι → ℝ → ℝ) (h : ℝ) :
    IndepFun Prod.fst Prod.snd (kernelInitialExtension initial d kernels h) :=
  indepFun_prod measurable_id measurable_id

/-- Assemble correlated scalar blocks into a phase-space innovation. -/
def klmcInnovation (d : ℕ) (n : ℕ)
    (ω : ℕ × Fin d → EuclideanSpace ℝ (Fin 2)) :
    PhaseSpace (EuclideanSpace ℝ (Fin d)) :=
  (WithLp.toLp 2 (fun i => ω (n, i) 0),
   WithLp.toLp 2 (fun i => ω (n, i) 1))

/-- Assemble all four correlated scalar innovations for the second-order step. -/
def klmc2Innovation (d : ℕ) (n : ℕ)
    (ω : ℕ × Fin d → EuclideanSpace ℝ (Fin 4)) :
    Fin 4 → EuclideanSpace ℝ (Fin d) :=
  fun j => WithLp.toLp 2 (fun i => ω (n, i) j)

theorem measurable_klmcInnovation (d n : ℕ) : Measurable (klmcInnovation d n) := by
  unfold klmcInnovation
  fun_prop

theorem measurable_klmc2Innovation (d n : ℕ) : Measurable (klmc2Innovation d n) := by
  unfold klmc2Innovation
  fun_prop

/-- The exact one-dimensional KLMC transition probability measure. This is
the pushforward of the correlated two-dimensional Gaussian, not a declaration
of an unspecified transition with desired moments. -/
def klmcScalarTransition (force : ℝ → ℝ) (γ h : ℝ) (state : PhaseSpace ℝ) :
    Measure (PhaseSpace ℝ) :=
  (klmcGaussian γ h).map (fun ξ => klmcStep force γ h state (ξ 0, ξ 1))

instance klmcScalarTransition_isProbabilityMeasure (force : ℝ → ℝ) (γ h : ℝ)
    (state : PhaseSpace ℝ) : IsProbabilityMeasure (klmcScalarTransition force γ h state) := by
  unfold klmcScalarTransition
  apply Measure.isProbabilityMeasure_map_iff (by
    unfold klmcStep exponentialStep
    fun_prop) |>.mpr
  infer_instance

/-- Both scalar phase coordinates after one step have finite second moments. -/
theorem klmcScalarStep_memLp (force : ℝ → ℝ) (γ h : ℝ) (state : PhaseSpace ℝ) :
    MemLp (fun ξ : EuclideanSpace ℝ (Fin 2) =>
      (klmcStep force γ h state (ξ 0, ξ 1)).1) 2 (klmcGaussian γ h) ∧
    MemLp (fun ξ : EuclideanSpace ℝ (Fin 2) =>
      (klmcStep force γ h state (ξ 0, ξ 1)).2) 2 (klmcGaussian γ h) := by
  constructor
  · change MemLp (fun ξ : EuclideanSpace ℝ (Fin 2) =>
      frozenVelocity γ state.1 (force state.2) h + Real.sqrt (2 * γ) * ξ 0)
      2 (klmcGaussian γ h)
    have hc : MemLp (fun _ : EuclideanSpace ℝ (Fin 2) =>
        frozenVelocity γ state.1 (force state.2) h) 2 (klmcGaussian γ h) := memLp_const _
    exact hc.add
      ((kernelGaussian_coordinate_memLp (klmcKernels γ) h 0).const_mul (Real.sqrt (2 * γ)))
  · change MemLp (fun ξ : EuclideanSpace ℝ (Fin 2) =>
      frozenPosition γ state.2 state.1 (force state.2) h + Real.sqrt (2 * γ) * ξ 1)
      2 (klmcGaussian γ h)
    have hc : MemLp (fun _ : EuclideanSpace ℝ (Fin 2) =>
        frozenPosition γ state.2 state.1 (force state.2) h) 2 (klmcGaussian γ h) := memLp_const _
    exact hc.add
      ((kernelGaussian_coordinate_memLp (klmcKernels γ) h 1).const_mul (Real.sqrt (2 * γ)))

/-- The mean of the actual transition is exactly the frozen-force solution. -/
theorem klmcScalarTransition_mean (force : ℝ → ℝ) (γ h : ℝ) (state : PhaseSpace ℝ) :
    (∫ z, z ∂klmcScalarTransition force γ h state) =
      (frozenVelocity γ state.1 (force state.2) h,
       frozenPosition γ state.2 state.1 (force state.2) h) := by
  have hv (j : Fin 2) : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) =>
      Real.sqrt (2 * γ) * ξ j) (klmcGaussian γ h) :=
    ((kernelGaussian_coordinate_memLp (klmcKernels γ) h j).integrable (by norm_num)).const_mul _
  rw [klmcScalarTransition, integral_map (by
    unfold klmcStep exponentialStep
    fun_prop) (by fun_prop)]
  change (∫ ξ, (frozenVelocity γ state.1 (force state.2) h + Real.sqrt (2 * γ) * ξ 0,
      frozenPosition γ state.2 state.1 (force state.2) h + Real.sqrt (2 * γ) * ξ 1)
      ∂klmcGaussian γ h) = _
  have h1 : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) =>
      frozenVelocity γ state.1 (force state.2) h + Real.sqrt (2 * γ) * ξ 0)
      (klmcGaussian γ h) := (integrable_const _).add (hv 0)
  have h2 : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) =>
      frozenPosition γ state.2 state.1 (force state.2) h + Real.sqrt (2 * γ) * ξ 1)
      (klmcGaussian γ h) := (integrable_const _).add (hv 1)
  have hi (a : ℝ) (j : Fin 2) :
      (∫ ξ : EuclideanSpace ℝ (Fin 2), a + Real.sqrt (2 * γ) * ξ j
        ∂klmcGaussian γ h) = a := by
    rw [integral_add (integrable_const a) (hv j), integral_const_mul]
    simp [klmcGaussian, kernelGaussian_coordinate_mean]
  exact (integral_pair h1 h2).trans (Prod.ext (hi _ 0) (hi _ 1))

/-- The cross covariance of the actual phase-space transition retains the
Brownian correlation between position and velocity. -/
theorem klmcScalarTransition_crossCovariance (force : ℝ → ℝ) (γ h : ℝ)
    (hγ : 0 ≤ γ) (hh : 0 ≤ h) (state : PhaseSpace ℝ) :
    cov[Prod.fst, Prod.snd; klmcScalarTransition force γ h state] =
      2 * γ * klmcCovariance γ h 0 1 := by
  rw [klmcScalarTransition, covariance_map_fun (by fun_prop) (by fun_prop) (by
    unfold klmcStep exponentialStep
    fun_prop)]
  change cov[fun ξ : EuclideanSpace ℝ (Fin 2) =>
      frozenVelocity γ state.1 (force state.2) h + Real.sqrt (2 * γ) * ξ 0,
    fun ξ : EuclideanSpace ℝ (Fin 2) =>
      frozenPosition γ state.2 state.1 (force state.2) h + Real.sqrt (2 * γ) * ξ 1;
    klmcGaussian γ h] = _
  have hi (j : Fin 2) : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) =>
      Real.sqrt (2 * γ) * ξ j) (klmcGaussian γ h) :=
    ((kernelGaussian_coordinate_memLp (klmcKernels γ) h j).integrable (by norm_num)).const_mul _
  rw [covariance_const_add_left (hi 0), covariance_const_add_right (hi 1),
    covariance_const_mul_left, covariance_const_mul_right]
  change Real.sqrt (2 * γ) * (Real.sqrt (2 * γ) *
    cov[fun ξ => ξ 0, fun ξ => ξ 1; kernelGaussian (klmcKernels γ) h]) = _
  rw [kernelGaussian_covariance _ (continuous_klmcKernels γ) hh]
  change Real.sqrt (2 * γ) * (Real.sqrt (2 * γ) * klmcCovariance γ h 0 1) = _
  rw [← mul_assoc, Real.mul_self_sqrt (mul_nonneg (by norm_num) hγ)]

end KineticLangevin
