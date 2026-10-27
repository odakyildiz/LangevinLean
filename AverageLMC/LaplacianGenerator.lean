import AverageLMC.LaplacianGradient

set_option linter.style.header false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace AverageLMC

/-- The genuine Langevin generator applied to the potential's gradient. -/
def gradientGenerator {p : ℕ} (f : State p → ℝ) (x : State p) : State p :=
  gradient (laplacian f) x - fderiv ℝ (gradient f) x (gradient f x)

/-- C³ potentials have a C¹ Laplacian. -/
theorem contDiff_laplacian_one {p : ℕ} (f : State p → ℝ) (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 1 (laplacian f) := by
  rw [laplacian_eq_directionalDerivative f (hf.of_le (by norm_num))]
  exact ContDiff.sum fun i _ ↦ contDiff_directionalDerivative _
    (contDiff_directionalDerivative f hf (coordinateVector i)) (coordinateVector i)

/-- The generator is a continuous vector field under the paper's C³ assumption. -/
theorem continuous_gradientGenerator {p : ℕ} (f : State p → ℝ) (hf : ContDiff ℝ 3 f) :
    Continuous (gradientGenerator f) := by
  have hgrad := contDiff_gradient_of_three f hf
  have hLap := contDiff_laplacian_one f hf
  have hG : Continuous (gradient (laplacian f)) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (State p)).symm.continuous.comp
      (hLap.continuous_fderiv (by norm_num))
  exact hG.sub ((hgrad.continuous_fderiv (by norm_num)).clm_apply hgrad.continuous)

/-- The vector field in the Dynkin formula is the actual Laplacian of the
gradient minus its derivative along the actual gradient. -/
theorem gradientGenerator_eq {p : ℕ} (f : State p → ℝ) (hf : ContDiff ℝ 3 f) (x : State p) :
    gradientGenerator f x = Laplacian.laplacian (gradient f) x -
      fderiv ℝ (gradient f) x (gradient f x) := by
  rw [laplacian_gradient_eq_gradient_laplacian f hf]
  rfl

/-- Lipschitz regularity bounds the actual Hessian applied to the gradient,
without any Lipschitz condition on the Hessian. -/
theorem hessian_gradient_norm_le {p : ℕ} (f : State p → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient f)) (x : State p) :
    ‖fderiv ℝ (gradient f) x (gradient f x)‖ ≤ (L : ℝ) * ‖gradient f x‖ :=
  ((fderiv ℝ (gradient f) x).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hLip) (norm_nonneg _))

/-- The paper's squared Laplacian-gradient condition gives the pointwise bound
with exactly its dimension factor. -/
theorem gradient_laplacian_norm_le {p : ℕ} (f : State p → ℝ) (Mdelta : ℝ)
    (hMdelta : 0 ≤ Mdelta) (hδ : LaplacianSmooth f Mdelta) (x : State p) :
    ‖gradient (laplacian f) x‖ ≤ Mdelta * Real.sqrt (p : ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ Mdelta ^ 2 * (p : ℝ) := hδ.2 x
    _ = (Mdelta * Real.sqrt (p : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg p)]

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The Laplacian-gradient part of the actual generator is square integrable. -/
theorem laplacian_gradient_memLp {p : ℕ} (f : State p → ℝ) (Mdelta : ℝ)
    (hMdelta : 0 ≤ Mdelta) (hδ : LaplacianSmooth f Mdelta) (Y : Lp (State p) 2 P) :
    MemLp (fun ω ↦ gradient (laplacian f) (Y ω)) 2 P := by
  have hLap := contDiff_laplacian_one f hδ.1
  have hc : Continuous (gradient (laplacian f)) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (State p)).symm.continuous.comp
      (hLap.continuous_fderiv (by norm_num))
  apply (memLp_const (1 : ℝ)).of_le_mul
    (hc.aestronglyMeasurable.comp_aemeasurable (Lp.aestronglyMeasurable Y).aemeasurable)
  exact ae_of_all _ fun ω ↦ by simpa using gradient_laplacian_norm_le f Mdelta hMdelta hδ (Y ω)

/-- The Hessian-gradient part has finite second moments from the Lipschitz gradient. -/
theorem hessian_gradient_memLp {p : ℕ} (f : State p → ℝ) (L : ℝ≥0)
    (hf : ContDiff ℝ 3 f) (hLip : LipschitzWith L (gradient f)) (Y : Lp (State p) 2 P) :
    MemLp (fun ω ↦ fderiv ℝ (gradient f) (Y ω) (gradient f (Y ω))) 2 P := by
  have hgrad := contDiff_gradient_of_three f hf
  have hc : Continuous (fun x ↦ fderiv ℝ (gradient f) x (gradient f x)) :=
    (hgrad.continuous_fderiv (by norm_num)).clm_apply hgrad.continuous
  exact (ULA.lpDrift_memLp P (gradient f) hLip Y).of_le_mul
    (hc.aestronglyMeasurable.comp_aemeasurable (Lp.aestronglyMeasurable Y).aemeasurable)
    (ae_of_all _ fun ω ↦ hessian_gradient_norm_le f L hLip (Y ω))

/-- The actual generator has finite second moments; no generator moment
hypothesis is assumed. -/
theorem gradientGenerator_memLp {p : ℕ} (f : State p → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient f)) (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta)
    (hδ : LaplacianSmooth f Mdelta) (Y : Lp (State p) 2 P) :
    MemLp (fun ω ↦ gradientGenerator f (Y ω)) 2 P :=
  (laplacian_gradient_memLp P f Mdelta hMdelta hδ Y).sub
    (hessian_gradient_memLp P f L hδ.1 hLip Y)

/-- The true generator's L² norm is bounded by the true score norm and the
paper's Laplacian-gradient constant. -/
theorem lp_gradientGenerator_norm_le {p : ℕ} (f : State p → ℝ) (L : ℝ≥0)
    (hLip : LipschitzWith L (gradient f)) (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta)
    (hδ : LaplacianSmooth f Mdelta) (Y : Lp (State p) 2 P) :
    ‖(gradientGenerator_memLp P f L hLip Mdelta hMdelta hδ Y).toLp
      (fun ω ↦ gradientGenerator f (Y ω))‖ ≤
      (L : ℝ) * ‖ULA.lpDrift P (gradient f) hLip Y‖ + Mdelta * Real.sqrt (p : ℝ) := by
  let D := fun ω ↦ gradient (laplacian f) (Y ω)
  let H := fun ω ↦ fderiv ℝ (gradient f) (Y ω) (gradient f (Y ω))
  let hD := laplacian_gradient_memLp P f Mdelta hMdelta hδ Y
  let hH := hessian_gradient_memLp P f L hδ.1 hLip Y
  have heq : (gradientGenerator_memLp P f L hLip Mdelta hMdelta hδ Y).toLp
      (fun ω ↦ gradientGenerator f (Y ω)) = hD.toLp D - hH.toLp H := rfl
  have hDbound : ‖hD.toLp D‖ ≤ Mdelta * Real.sqrt (p : ℝ) := by
    have hb := Lp.norm_le_of_ae_bound (f := hD.toLp D) (by positivity : 0 ≤ Mdelta * Real.sqrt (p : ℝ))
      (show ∀ᵐ ω ∂P, ‖hD.toLp D ω‖ ≤ Mdelta * Real.sqrt (p : ℝ) from by
        filter_upwards [hD.coeFn_toLp] with ω hω
        rw [hω]
        exact gradient_laplacian_norm_le f Mdelta hMdelta hδ (Y ω))
    simpa [measureUnivNNReal, measure_univ] using hb
  have hHbound : ‖hH.toLp H‖ ≤ (L : ℝ) * ‖ULA.lpDrift P (gradient f) hLip Y‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hH.coeFn_toLp, ULA.lpDrift_coe P (gradient f) hLip Y] with ω hω hg
    rw [hω, hg]
    exact hessian_gradient_norm_le f L hLip (Y ω)
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Under the constructed stationary Gibbs law, the sharp coordinate score
moment supplies the paper's generator constant. -/
theorem lp_gradientGenerator_gibbs_norm_le {p : ℕ} (hp : 0 < p)
    (f : State p → ℝ) (m : ℝ) (L : ℝ≥0) (hm : 0 < m)
    (hsc : StrongConvexOn univ m f) (hLip : LipschitzWith L (gradient f))
    (Mdelta : ℝ) (hMdelta : 0 ≤ Mdelta) (hδ : LaplacianSmooth f Mdelta)
    (Y : Lp (State p) 2 P) (hlaw : P.map Y = ULA.gibbsMeasure f) :
    ‖(gradientGenerator_memLp P f L hLip Mdelta hMdelta hδ Y).toLp
      (fun ω ↦ gradientGenerator f (Y ω))‖ ≤
      (L : ℝ) * Real.sqrt (averageSmoothness f * (p : ℝ)) + Mdelta * Real.sqrt (p : ℝ) := by
  have hf : Differentiable ℝ f := hδ.1.differentiable (by norm_num)
  have hs := integral_norm_sq_gradient_gibbs_le hp f m L hm hf hsc hLip
  have hscore : ‖ULA.lpDrift P (gradient f) hLip Y‖ ^ 2 ≤ averageSmoothness f * (p : ℝ) := by
    rw [ULA.lpDrift_norm_sq]
    have he := integral_map (Lp.aestronglyMeasurable Y).aemeasurable
      (hLip.continuous.norm.pow 2).aestronglyMeasurable
    rw [hlaw] at he
    change (∫ x, ‖gradient f x‖ ^ 2 ∂ULA.gibbsMeasure f) =
      ∫ ω, ‖gradient f (Y ω)‖ ^ 2 ∂P at he
    rw [← he]
    simpa only [mul_comm] using hs
  exact (lp_gradientGenerator_norm_le P f L hLip Mdelta hMdelta hδ Y).trans
    (add_le_add (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hscore) L.coe_nonneg) le_rfl)

end AverageLMC
