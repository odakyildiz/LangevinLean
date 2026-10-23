import KineticLangevin.HessianRemainder
import KineticLangevin.RandomOperatorLp
import KineticLangevin.LpMomentBounds

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace KineticLangevin
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] (P : Measure Ω) [IsFiniteMeasure P]

/-- The actual random Hessian at the initial position acts as a bounded operator on L². -/
def lpHessian (g : E → E) (H : E → E →L[ℝ] E) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 H)
    (hg : ∀ x,HasFDerivAt g (H x) x) (Y : Lp E 2 P) : Lp E 2 P →L[ℝ] Lp E 2 P :=
  randomOperatorLp P (fun ω ↦ H (Y ω))
    (hH.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable Y)) M
    (Filter.Eventually.of_forall (fun ω ↦ (hg (Y ω)).le_of_lipschitz hG))

theorem lpHessian_coe (g : E → E) (H : E → E →L[ℝ] E) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 H)
    (hg : ∀ x,HasFDerivAt g (H x) x) (Y X : Lp E 2 P) :
    lpHessian P g H M M2 hG hH hg Y X =ᵐ[P] fun ω ↦ H (Y ω) (X ω) :=
  randomOperatorLp_coe ..

theorem lpHessian_norm_le (g : E → E) (H : E → E →L[ℝ] E) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 H)
    (hg : ∀ x,HasFDerivAt g (H x) x) (Y : Lp E 2 P) :
    ‖lpHessian P g H M M2 hG hH hg Y‖≤(M : ℝ) :=
  randomOperatorLp_norm_le _ _ _ _ M.coe_nonneg _

/-- The genuine frozen-random-Hessian Taylor remainder has the L² bound from the displacement L4 radius. -/
theorem lpHessian_taylor_bound (g : E → E) (H : E → E →L[ℝ] E) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 H)
    (hg : ∀ x,HasFDerivAt g (H x) x) (X Y : Lp E 2 P) (C : ℝ) (hC : 0≤C)
    (hfour : eLpNorm (X-Y) 4 P≤ENNReal.ofReal C) :
    ‖ULA.lpDrift P g hG X-ULA.lpDrift P g hG Y-
      lpHessian P g H M M2 hG hH hg Y (X-Y)‖≤(M2 : ℝ)/2*C^2 := by
  apply lp_norm_le_quadratic P _ (X-Y) _ C (by positivity) hC hfour
  filter_upwards [Lp.coeFn_sub (ULA.lpDrift P g hG X-ULA.lpDrift P g hG Y)
      (lpHessian P g H M M2 hG hH hg Y (X-Y)),
    Lp.coeFn_sub (ULA.lpDrift P g hG X) (ULA.lpDrift P g hG Y),
    ULA.lpDrift_coe P g hG X,ULA.lpDrift_coe P g hG Y,
    lpHessian_coe P g H M M2 hG hH hg Y (X-Y),Lp.coeFn_sub X Y]
    with ω hsub hsubG hGX hGY hHX hXY
  simp only [Pi.sub_apply,hsub,hsubG,hGX,hGY,hHX,hXY]
  exact force_taylor_remainder_bound g H M2 hH hg (X ω) (Y ω)

variable {ι : Type*} [Fintype ι]
/-- Actual Gaussian velocity marginals and the actual kinematic equation give the paper's quadratic-in-time Taylor defect. -/
theorem lpHessian_stationary_taylor_bound
    (g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (H : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (M M2 : ℝ≥0) (hG : LipschitzWith M g) (hH : LipschitzWith M2 H)
    (hg : ∀ x,HasFDerivAt g (H x) x)
    (X V : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hV : Continuous V) (T : ℝ)
    (hkin : ∀ t ∈ Icc 0 T,X t-X 0=∫ r in 0..t,V r)
    (hlaw : ∀ t ∈ Icc 0 T,HasLaw (V t) (stdGaussian (EuclideanSpace ℝ ι)) P)
    {t : ℝ} (ht : t∈Icc 0 T) :
    ‖ULA.lpDrift P g hG (X t)-ULA.lpDrift P g hG (X 0)-
      lpHessian P g H M M2 hG hH hg (X 0) (X t-X 0)‖≤
      (M2 : ℝ)/2*Real.sqrt ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))*t^2 := by
  let D : ℝ := (Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ)
  have hD : 0≤D := by dsimp [D];positivity
  have hr : (D^(1/4 : ℝ))^2=Real.sqrt D := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hD,Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hb := lpHessian_taylor_bound P g H M M2 hG hH hg (X t) (X 0)
    (t*D^(1/4 : ℝ)) (mul_nonneg ht.1 (Real.rpow_nonneg hD _))
    (gaussian_kinematic_four_bound P X V hV T hkin hlaw ht)
  rw [mul_pow,hr] at hb
  nlinarith only [hb]

end KineticLangevin
