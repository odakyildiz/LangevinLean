import AverageLMC.LaplacianGenerator
import AverageLMC.GeneratorProduct
import AverageLMC.CompactC2Taylor
import AverageLMC.LaplacianCompactTest
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option linter.style.header false
set_option maxHeartbeats 800000
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators ContDiff

namespace AverageLMC

def radialCutoffBump {p : ℕ} (n : ℕ) : ContDiffBump (0 : State p) where
  rIn := (n : ℝ) + 1
  rOut := 2 * ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith [Nat.cast_nonneg (α := ℝ) n]

/-- A smooth cutoff equal to one on radius `n+1`, with support inside
radius `2(n+1)`. -/
def radialCutoff {p : ℕ} (n : ℕ) : State p → ℝ := radialCutoffBump n

theorem radialCutoff_contDiff {p : ℕ} (n : ℕ) : ContDiff ℝ ∞ (@radialCutoff p n) :=
  (radialCutoffBump n).contDiff

theorem radialCutoff_compactSupport {p : ℕ} (n : ℕ) :
    HasCompactSupport (@radialCutoff p n) := (radialCutoffBump n).hasCompactSupport

theorem radialCutoff_mem_Icc {p : ℕ} (n : ℕ) (x : State p) :
    radialCutoff n x ∈ Icc (0 : ℝ) 1 :=
  ⟨(radialCutoffBump n).nonneg, (radialCutoffBump n).le_one⟩

theorem radialCutoff_eq_scaled {p : ℕ} (n : ℕ) (x : State p) :
    radialCutoff n x = radialCutoff 0 ((((n : ℝ) + 1)⁻¹) • x) := by
  have hr : 2 * ((n : ℝ) + 1) / ((n : ℝ) + 1) = 2 := by field_simp
  simp [radialCutoff, ContDiffBump.toFun, radialCutoffBump, hr]

/-- At each fixed point the cutoff is eventually locally equal to one,
so every derivative of any fixed test is eventually unchanged. -/
theorem radialCutoff_eventuallyEq_one {p : ℕ} (x : State p) :
    ∀ᶠ n : ℕ in atTop, radialCutoff n =ᶠ[𝓝 x] 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply (radialCutoffBump n).eventuallyEq_one_of_mem_ball
  rw [Metric.mem_ball, dist_zero_right]
  change ‖x‖ < (n : ℝ) + 1
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The cutoff family has uniform bounds on its first two derivatives.
They follow by rescaling one fixed compact smooth bump. -/
theorem radialCutoff_derivative_bounds {p : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n k, k ≤ 2 → ∀ x : State p,
      ‖iteratedFDeriv ℝ k (radialCutoff n) x‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := (radialCutoff_compactSupport (p := p) 0).exists_bound_iteratedFDeriv
    (radialCutoff_contDiff 0) 2
  refine ⟨C, hC, ?_⟩
  intro n k hk x
  have hfun : radialCutoff n = fun y : State p ↦ radialCutoff 0 (((n : ℝ) + 1)⁻¹ • y) :=
    funext (radialCutoff_eq_scaled n)
  rw [hfun, iteratedFDeriv_comp_const_smul ((n : ℝ) + 1)⁻¹
    ((radialCutoff_contDiff 0).of_le (by simp))]
  simp only [norm_smul, Real.norm_eq_abs, abs_pow, abs_inv,
    abs_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)]
  have ha : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hp : (((n : ℝ) + 1)⁻¹) ^ k ≤ 1 := pow_le_one₀ (by positivity) ha
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (radialCutoff 0) (((n : ℝ) + 1)⁻¹ • x)‖ :=
      mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ ≤ C := by simpa only [one_mul] using hb k hk _

theorem radialCutoff_gradient_laplacian_bounds {p : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (x : State p),
      ‖gradient (radialCutoff n) x‖ ≤ C ∧
        |laplacian (radialCutoff n) x| ≤ (p : ℝ) * C := by
  obtain ⟨C, hC, hb⟩ := radialCutoff_derivative_bounds (p := p)
  refine ⟨C, hC, fun n x ↦ ⟨?_, ?_⟩⟩
  · have hnorm : ‖gradient (radialCutoff n) x‖ = ‖fderiv ℝ (radialCutoff n) x‖ := by
      rw [gradient, LinearIsometryEquiv.norm_map]
    rw [hnorm, ← norm_iteratedFDeriv_one]
    exact hb n 1 (by norm_num) x
  · rw [laplacian, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin p) ℝ)]
    simp only [EuclideanSpace.basisFun_apply]
    calc
      _ ≤ ∑ j : Fin p, |iteratedFDeriv ℝ 2 (radialCutoff n) x
          ![coordinateVector j, coordinateVector j]| := by
        simpa only [coordinateVector] using Finset.abs_sum_le_sum_abs
          (fun j : Fin p ↦ iteratedFDeriv ℝ 2 (radialCutoff n) x
            ![coordinateVector j, coordinateVector j]) Finset.univ
      _ ≤ ∑ _j : Fin p, C := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← Real.norm_eq_abs]
        have h := (iteratedFDeriv ℝ 2 (radialCutoff n) x).le_opNorm
          ![coordinateVector j, coordinateVector j]
        simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          norm_coordinateVector, one_mul, mul_one] at h
        exact h.trans (hb n 2 le_rfl x)
      _ = _ := by simp [mul_comm]

/-- Every positive finite moment of each coordinate of the true Gibbs
score follows from its sub-Gaussian MGF. -/
theorem memLp_gradient_gibbs_all {p : ℕ}
    (f : State p → ℝ) (M : ℝ≥0) (hf : Differentiable ℝ f)
    (hLip : LipschitzWith M (gradient f)) (hZ : ULA.gibbsPartition f ≠ ⊤)
    (q : ℝ≥0) : MemLp (gradient f) q (ULA.gibbsMeasure f) := by
  apply memLp_piLp_iff.mpr
  intro j
  have hs := ULA.gibbs_score_subgaussian f M hf hLip hZ (coordinateVector j)
  simpa only [inner_coordinateVector] using hs.memLp q

/-- Multiplying a C² field by the radial cutoff yields a compact C² test. -/
theorem radialCutoff_mul_contDiff {p : ℕ} (ψ : State p → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (n : ℕ) :
    ContDiff ℝ 2 (fun x ↦ radialCutoff n x * ψ x) :=
  ((radialCutoff_contDiff n).of_le (by simp)).mul hψ

theorem radialCutoff_mul_compactSupport {p : ℕ} (ψ : State p → ℝ) (n : ℕ) :
    HasCompactSupport (fun x ↦ radialCutoff n x * ψ x) :=
  (radialCutoff_compactSupport n).mul_right

/-- Cutoff tests and their genuine generators eventually coincide pointwise
with the unbounded C² test and its generator. -/
theorem radialCutoff_generator_eventually_eq {p : ℕ} (f ψ : State p → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (x : State p) :
    ∀ᶠ n : ℕ in atTop,
      (radialCutoff n x * ψ x = ψ x) ∧
      ULA.langevinGenerator f (fun y ↦ radialCutoff n y * ψ y) x =
        ULA.langevinGenerator f ψ x := by
  filter_upwards [radialCutoff_eventuallyEq_one x] with n hn
  have heq : (fun y ↦ radialCutoff n y * ψ y) =ᶠ[𝓝 x] ψ := by
    filter_upwards [hn] with y hy
    simp only [hy, Pi.one_apply, one_mul]
  refine ⟨heq.eq_of_nhds, ?_⟩
  rw [ULA.langevinGenerator_eq_laplacian_sub_inner f _ (radialCutoff_mul_contDiff ψ hψ n),
    ULA.langevinGenerator_eq_laplacian_sub_inner f ψ hψ]
  have hLap : Laplacian.laplacian (fun y ↦ radialCutoff n y * ψ y) x =
      Laplacian.laplacian ψ x := (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
  have hgrad : gradient (fun y ↦ radialCutoff n y * ψ y) x = gradient ψ x := by
    unfold gradient
    rw [heq.fderiv_eq]
  rw [hLap, hgrad]

/-- An explicit dominated L² convergence principle for eventually identical
cutoff tests. It is stated with actual squared integrals, so no quotient
representative or finite-norm convention is implicit. -/
theorem integral_sq_sub_tendsto_zero_of_eventually_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (G B : Ω → ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hG : AEStronglyMeasurable G μ)
    (hB : Integrable (fun a ↦ B a ^ 2) μ)
    (hbound : ∀ n, ∀ᵐ a ∂μ, |F n a| ≤ B a)
    (hGbound : ∀ᵐ a ∂μ, |G a| ≤ B a)
    (heq : ∀ᵐ a ∂μ, ∀ᶠ n : ℕ in atTop, F n a = G a) :
    Tendsto (fun n ↦ ∫ a, (F n a - G a) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hd := tendsto_integral_of_dominated_convergence
    (F := fun n a ↦ (F n a - G a) ^ 2) (f := fun _ : Ω ↦ (0 : ℝ))
    (fun a ↦ 4 * B a ^ 2)
    (fun n ↦ ((hF n).sub hG).pow 2)
    (hB.const_mul 4)
    (fun n ↦ ?_) (show ∀ᵐ a ∂μ,
      Tendsto (fun n ↦ (F n a - G a) ^ 2) atTop (𝓝 (0 : ℝ)) from ?_)
  · simpa only [integral_zero] using hd
  · filter_upwards [hbound n, hGbound] with a ha hGa
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h : |F n a - G a| ≤ 2 * B a := (abs_sub _ _).trans (by linarith)
    have hnonneg : 0 ≤ B a := (abs_nonneg _).trans ha
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * B a)).mpr h
    simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using hs
  · filter_upwards [heq] with a ha
    apply tendsto_const_nhds.congr'
    filter_upwards [ha] with n hn
    simp [hn]

theorem continuous_langevinGenerator_test {p : ℕ} (f ψ : State p → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (hψ : ContDiff ℝ 2 ψ) :
    Continuous (ULA.langevinGenerator f ψ) := by
  have heq : ULA.langevinGenerator f ψ = fun x ↦ Laplacian.laplacian ψ x -
      inner ℝ (gradient f x) (gradient ψ x) :=
    funext (ULA.langevinGenerator_eq_laplacian_sub_inner f ψ hψ)
  rw [heq]
  have hgrad : Continuous (gradient ψ) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (State p)).symm.continuous.comp
      (hψ.continuous_fderiv (by norm_num))
  exact (compactC2_continuous_laplacian ψ hψ).sub (hLip.continuous.inner hgrad)

theorem gradient_score_coordinate_norm_le {p : ℕ} (f : State p → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (j : Fin p) (x : State p) :
    ‖gradient (fun y ↦ (gradient f y) j) x‖ ≤ (M : ℝ) := by
  have hψLip : LipschitzWith M (fun y ↦ (gradient f y) j) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [dist_eq_norm]
    exact (show ‖(gradient f y) j - (gradient f z) j‖ ≤ ‖gradient f y - gradient f z‖
      from by simpa using PiLp.norm_apply_le (gradient f y - gradient f z) j).trans
      (hLip.norm_sub_le y z)
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact norm_fderiv_le_of_lipschitz ℝ hψLip

/-- A single square-integrable majorant controls every cutoff generator.
Only the score's fourth moment is needed; it is derived from its MGF below. -/
theorem scoreCutoff_generator_bound {p : ℕ} (f : State p → ℝ) (M : ℝ≥0)
    (hLip : LipschitzWith M (gradient f)) (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta)
    (hδ : LaplacianSmooth f Mdelta) (j : Fin p) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n x,
      |ULA.langevinGenerator f (fun y ↦ radialCutoff n y * (gradient f y) j) x| ≤
        B * (1 + ‖gradient f x‖ ^ 2) := by
  obtain ⟨C, hC, hb⟩ := radialCutoff_gradient_laplacian_bounds (p := p)
  let D := Mdelta * Real.sqrt (p : ℝ)
  let B := D + (M : ℝ) + (p : ℝ) * C + C + 2 * C * (M : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  intro n x
  let s := ‖gradient f x‖
  have hs : 0 ≤ s := norm_nonneg _
  let ψ : State p → ℝ := fun y ↦ (gradient f y) j
  have hψ : ContDiff ℝ 2 ψ := by
    change ContDiff ℝ 2 ((EuclideanSpace.proj j) ∘ gradient f)
    exact (EuclideanSpace.proj j).contDiff.comp (contDiff_gradient_of_three f hδ.1)
  have hψabs : |ψ x| ≤ s := by
    simpa only [ψ, Real.norm_eq_abs] using PiLp.norm_apply_le (gradient f x) j
  have hGψ : |ULA.langevinGenerator f ψ x| ≤ D + (M : ℝ) * s := by
    rw [langevinGenerator_coordinate_gradient f hδ.1 j x]
    calc
      _ ≤ ‖gradientGenerator f x‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (gradientGenerator f x) j
      _ ≤ ‖gradient (laplacian f) x‖ +
          ‖fderiv ℝ (gradient f) x (gradient f x)‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (gradient_laplacian_norm_le f Mdelta hMdelta hδ x)
        (hessian_gradient_norm_le f M hLip x)
  have hχabs : |radialCutoff n x| ≤ 1 :=
    (abs_of_nonneg (radialCutoff_mem_Icc n x).1).le.trans (radialCutoff_mem_Icc n x).2
  have hχG : |ULA.langevinGenerator f (radialCutoff n) x| ≤ (p : ℝ) * C + s * C := by
    rw [ULA.langevinGenerator_eq_laplacian_sub_inner f _
      ((radialCutoff_contDiff n).of_le (by simp))]
    exact (abs_sub _ _).trans (add_le_add (hb n x).2
      ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hb n x).1 hs)))
  have hcross : |inner ℝ (gradient (radialCutoff n) x) (gradient ψ x)| ≤ C * (M : ℝ) :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hb n x).1
      (gradient_score_coordinate_norm_le f M hLip j x) (norm_nonneg _) hC)
  have hraw : |ULA.langevinGenerator f (fun y ↦ radialCutoff n y * ψ y) x| ≤
      D + (M : ℝ) * s + s * ((p : ℝ) * C + s * C) + 2 * C * (M : ℝ) := by
    rw [langevinGenerator_mul f _ ψ ((radialCutoff_contDiff n).of_le (by simp)) hψ x]
    calc
      _ ≤ |radialCutoff n x * ULA.langevinGenerator f ψ x| +
          |ψ x * ULA.langevinGenerator f (radialCutoff n) x| +
          |2 * inner ℝ (gradient (radialCutoff n) x) (gradient ψ x)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have h1 := mul_le_mul hχabs hGψ (abs_nonneg _) (by positivity : 0 ≤ (1 : ℝ))
        have h2 := mul_le_mul hψabs hχG (abs_nonneg _) hs
        have h3 := mul_le_mul_of_nonneg_left hcross (by norm_num : (0 : ℝ) ≤ 2)
        nlinarith
  apply hraw.trans
  have hsquad : s ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
  have hlinear := mul_le_mul_of_nonneg_left hsquad
    (by positivity : 0 ≤ (M : ℝ) + (p : ℝ) * C)
  have hrest : 0 ≤ (D + C + 2 * C * (M : ℝ)) * s ^ 2 := by positivity
  dsimp [B]
  nlinarith

/-- Compact C² approximations of an actual coordinate score converge in
Gibbs L² together with their genuine Langevin generators. All moments and
the common domination are consequences of the potential assumptions. -/
theorem score_coordinate_compact_approximation {p : ℕ}
    (f : State p → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (hZ : ULA.gibbsPartition f ≠ ⊤) (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta)
    (hδ : LaplacianSmooth f Mdelta) (j : Fin p) :
    ∃ φ : ℕ → State p → ℝ,
      (∀ n, ContDiff ℝ 2 (φ n) ∧ HasCompactSupport (φ n)) ∧
      Tendsto (fun n ↦ ∫ x, (φ n x - (gradient f x) j) ^ 2 ∂ULA.gibbsMeasure f)
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ x, (ULA.langevinGenerator f (φ n) x -
        (gradientGenerator f x) j) ^ 2 ∂ULA.gibbsMeasure f) atTop (𝓝 0) := by
  have hf : Differentiable ℝ f := hδ.1.differentiable (by norm_num)
  letI : IsProbabilityMeasure (ULA.gibbsMeasure f) := by
    constructor
    rw [ULA.gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ULA.gibbsPartition_pos f hf)) hZ
  let ψ : State p → ℝ := fun x ↦ (gradient f x) j
  let φ : ℕ → State p → ℝ := fun n x ↦ radialCutoff n x * ψ x
  have hψ : ContDiff ℝ 2 ψ := by
    change ContDiff ℝ 2 ((EuclideanSpace.proj j) ∘ gradient f)
    exact (EuclideanSpace.proj j).contDiff.comp (contDiff_gradient_of_three f hδ.1)
  have hφ (n : ℕ) : ContDiff ℝ 2 (φ n) := radialCutoff_mul_contDiff ψ hψ n
  refine ⟨φ, fun n ↦ ⟨hφ n, radialCutoff_mul_compactSupport ψ n⟩, ?_, ?_⟩
  · have hs2 := memLp_gradient_gibbs_all f M hf hLip hZ 2
    have hs : Integrable (fun x ↦ ‖gradient f x‖ ^ 2) (ULA.gibbsMeasure f) :=
      hs2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    apply integral_sq_sub_tendsto_zero_of_eventually_eq (ULA.gibbsMeasure f) φ ψ
      (fun x ↦ ‖gradient f x‖) (fun n ↦ (hφ n).continuous.aestronglyMeasurable)
      hψ.continuous.aestronglyMeasurable hs
    · intro n
      apply ae_of_all
      intro x
      have hχ : |radialCutoff n x| ≤ 1 := by
        rw [abs_of_nonneg (radialCutoff_mem_Icc n x).1]
        exact (radialCutoff_mem_Icc n x).2
      have hψb : |ψ x| ≤ ‖gradient f x‖ := by
        simpa only [ψ, Real.norm_eq_abs] using PiLp.norm_apply_le (gradient f x) j
      dsimp [φ]
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hχ (abs_nonneg _)).trans (by simpa using hψb)
    · exact ae_of_all _ fun x ↦ by
        simpa only [ψ, Real.norm_eq_abs] using PiLp.norm_apply_le (gradient f x) j
    · exact ae_of_all _ fun x ↦ (radialCutoff_generator_eventually_eq f ψ hψ x).mono
        (fun n hn ↦ hn.1)
  · obtain ⟨B, hB, hb⟩ := scoreCutoff_generator_bound f M hLip Mdelta hMdelta hδ j
    have hs4 : MemLp (gradient f) (4 : ℝ≥0∞) (ULA.gibbsMeasure f) := by
      simpa using memLp_gradient_gibbs_all f M hf hLip hZ 4
    have hfour := hs4.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    have hsquare : MemLp (fun x ↦ ‖gradient f x‖ ^ 2) 2 (ULA.gibbsMeasure f) := by
      apply (memLp_two_iff_integrable_sq (hLip.continuous.norm.pow 2).aestronglyMeasurable).mpr
      convert hfour using 1
      funext x
      simp only [Pi.pow_apply]
      ring
    have hboundLp : MemLp (fun x ↦ B * (1 + ‖gradient f x‖ ^ 2)) 2
        (ULA.gibbsMeasure f) := ((memLp_const (1 : ℝ)).add hsquare).const_mul B
    have hboundSq := (memLp_two_iff_integrable_sq hboundLp.aestronglyMeasurable).mp hboundLp
    have hgen := integral_sq_sub_tendsto_zero_of_eventually_eq (ULA.gibbsMeasure f)
      (fun n ↦ ULA.langevinGenerator f (φ n)) (ULA.langevinGenerator f ψ)
      (fun x ↦ B * (1 + ‖gradient f x‖ ^ 2))
      (fun n ↦ (continuous_langevinGenerator_test f (φ n) M hLip (hφ n)).aestronglyMeasurable)
      (continuous_langevinGenerator_test f ψ M hLip hψ).aestronglyMeasurable hboundSq
      (fun n ↦ ae_of_all _ fun x ↦ hb n x)
      (ae_of_all _ fun x ↦ ?_) (ae_of_all _ fun x ↦ ?_)
    · simpa only [ψ, langevinGenerator_coordinate_gradient f hδ.1] using hgen
    · obtain ⟨n, hn⟩ := (radialCutoff_generator_eventually_eq f ψ hψ x).exists
      rw [← hn.2]
      exact hb n x
    · exact (radialCutoff_generator_eventually_eq f ψ hψ x).mono (fun n hn ↦ hn.2)

theorem integral_norm_sq_toLp_sub_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) (F : ℕ → Fin p → Ω → ℝ) (G : Ω → State p)
    (hF : ∀ n, MemLp (fun a ↦ WithLp.toLp 2 (fun j ↦ F n j a)) 2 μ)
    (hG : MemLp G 2 μ)
    (hconv : ∀ j, Tendsto (fun n ↦ ∫ a, (F n j a - (G a) j) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ a, ‖WithLp.toLp 2 (fun j ↦ F n j a) - G a‖ ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have heq (n : ℕ) : (∫ a, ‖WithLp.toLp 2 (fun j ↦ F n j a) - G a‖ ^ 2 ∂μ) =
      ∑ j : Fin p, ∫ a, (F n j a - (G a) j) ^ 2 ∂μ := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    rw [integral_finsetSum]
    · rfl
    · intro j hj
      have hd := ((hF n).sub hG).eval_piLp j
      exact (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mp hd
  simp_rw [heq]
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ ↦ hconv j)

theorem gradientGenerator_gibbs_memLp {p : ℕ}
    (f : State p → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (hZ : ULA.gibbsPartition f ≠ ⊤) (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta)
    (hδ : LaplacianSmooth f Mdelta) :
    MemLp (gradientGenerator f) 2 (ULA.gibbsMeasure f) := by
  have hf : Differentiable ℝ f := hδ.1.differentiable (by norm_num)
  letI : IsProbabilityMeasure (ULA.gibbsMeasure f) := by
    constructor
    rw [ULA.gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ULA.gibbsPartition_pos f hf)) hZ
  have hs : MemLp (gradient f) 2 (ULA.gibbsMeasure f) :=
    memLp_gradient_gibbs_all f M hf hLip hZ 2
  have hb0 : MemLp (fun _ : State p ↦ Mdelta * Real.sqrt (p : ℝ)) 2
      (ULA.gibbsMeasure f) := memLp_const _
  have hb := hb0.add (hs.norm.const_mul (M : ℝ))
  change MemLp (fun x ↦ Mdelta * Real.sqrt (p : ℝ) + (M : ℝ) * ‖gradient f x‖) 2
    (ULA.gibbsMeasure f) at hb
  apply hb.of_le_mul (c := (1 : ℝ)) (continuous_gradientGenerator f hδ.1).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖gradientGenerator f x‖ ≤ 1 * ‖Mdelta * Real.sqrt (p : ℝ) + (M : ℝ) * ‖gradient f x‖‖
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ Mdelta * Real.sqrt (p : ℝ) + (M : ℝ) * ‖gradient f x‖)]
  exact (norm_sub_le (gradient (laplacian f) x)
    (fderiv ℝ (gradient f) x (gradient f x))).trans
    (add_le_add (gradient_laplacian_norm_le f Mdelta hMdelta hδ x)
      (hessian_gradient_norm_le f M hLip x))

/-- A single vector family of compact C² tests approximates the entire
score and its entire actual generator in Gibbs L². Explicit L² membership
is supplied for every approximant and both targets. -/
theorem score_vector_compact_approximation {p : ℕ}
    (f : State p → ℝ) (M : ℝ≥0) (hLip : LipschitzWith M (gradient f))
    (hZ : ULA.gibbsPartition f ≠ ⊤) (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta)
    (hδ : LaplacianSmooth f Mdelta) :
    ∃ φ : ℕ → Fin p → State p → ℝ,
      (∀ n j, ContDiff ℝ 2 (φ n j) ∧ HasCompactSupport (φ n j)) ∧
      (∀ n, MemLp (fun x ↦ WithLp.toLp 2 (fun j ↦ φ n j x)) 2 (ULA.gibbsMeasure f)) ∧
      (∀ n, MemLp (fun x ↦ WithLp.toLp 2 (fun j ↦
        ULA.langevinGenerator f (φ n j) x)) 2 (ULA.gibbsMeasure f)) ∧
      MemLp (gradient f) 2 (ULA.gibbsMeasure f) ∧
      MemLp (gradientGenerator f) 2 (ULA.gibbsMeasure f) ∧
      Tendsto (fun n ↦ ∫ x, ‖WithLp.toLp 2 (fun j ↦ φ n j x) - gradient f x‖ ^ 2
        ∂ULA.gibbsMeasure f) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ x, ‖WithLp.toLp 2 (fun j ↦ ULA.langevinGenerator f (φ n j) x) -
        gradientGenerator f x‖ ^ 2 ∂ULA.gibbsMeasure f) atTop (𝓝 0) := by
  classical
  have hf : Differentiable ℝ f := hδ.1.differentiable (by norm_num)
  letI : IsProbabilityMeasure (ULA.gibbsMeasure f) := by
    constructor
    rw [ULA.gibbsMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ULA.gibbsPartition_pos f hf)) hZ
  choose φ hφ hscore hgen using (fun j : Fin p ↦
    score_coordinate_compact_approximation f M hLip hZ Mdelta hMdelta hδ j)
  let Φ : ℕ → Fin p → State p → ℝ := fun n j ↦ φ j n
  have hΦ (n : ℕ) : MemLp (fun x ↦ WithLp.toLp 2 (fun j ↦ Φ n j x)) 2
      (ULA.gibbsMeasure f) := by
    apply memLp_piLp_iff.mpr
    intro j
    obtain ⟨huc, C, hC, hb⟩ := compact_test_bounded_uniformContinuous (φ j n)
      (hφ j n).1 (hφ j n).2
    exact MemLp.of_bound (hφ j n).1.continuous.aestronglyMeasurable C
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)
  have hGΦ (n : ℕ) : MemLp (fun x ↦ WithLp.toLp 2 (fun j ↦
      ULA.langevinGenerator f (Φ n j) x)) 2 (ULA.gibbsMeasure f) := by
    apply memLp_piLp_iff.mpr
    intro j
    obtain ⟨huc, C, hC, hb⟩ := compact_test_generator_bounded_uniformContinuous f M hLip
      (φ j n) (hφ j n).1 (hφ j n).2
    exact MemLp.of_bound (continuous_langevinGenerator_test f (φ j n) M hLip
      (hφ j n).1).aestronglyMeasurable C
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using hb x)
  have hscore2 : MemLp (gradient f) 2 (ULA.gibbsMeasure f) :=
    memLp_gradient_gibbs_all f M hf hLip hZ 2
  have hgen2 := gradientGenerator_gibbs_memLp f M hLip hZ Mdelta hMdelta hδ
  refine ⟨Φ, fun n j ↦ hφ j n, hΦ, hGΦ, hscore2, hgen2, ?_, ?_⟩
  · exact integral_norm_sq_toLp_sub_tendsto_zero (ULA.gibbsMeasure f) Φ
      (gradient f) hΦ hscore2 hscore
  · exact integral_norm_sq_toLp_sub_tendsto_zero (ULA.gibbsMeasure f)
      (fun n j ↦ ULA.langevinGenerator f (Φ n j)) (gradientGenerator f) hGΦ hgen2 hgen

end AverageLMC
