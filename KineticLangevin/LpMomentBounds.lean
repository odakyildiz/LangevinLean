import KineticLangevin.GaussianFourth
import KineticLangevin.LpMomentIntegral
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Function.Holder

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace KineticLangevin
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]

/-- A quadratic pointwise remainder is square-integrable with the square of its L4 radius. -/
theorem lp_norm_le_quadratic (P : Measure Ω) (D X : Lp E 2 P) (a C : ℝ)
    (ha : 0≤a) (hC : 0≤C) (hX : eLpNorm X 4 P≤ENNReal.ofReal C)
    (hbound : ∀ᵐ ω ∂P,‖D ω‖≤a*‖X ω‖^2) : ‖D‖≤a*C^2 := by
  let c : ℝ≥0 := ⟨a,ha⟩
  have hb : ∀ᵐ ω ∂P,‖D ω‖₊≤c*‖(‖X ω‖ : ℝ)^(2 : ℝ)‖₊ := by
    filter_upwards [hbound] with ω hω
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_mul,NNReal.coe_mk,show (c : ℝ)=a from rfl,coe_nnnorm,Real.rpow_two,
      Real.norm_eq_abs,abs_sq] using hω
  have he := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Lp.aestronglyMeasurable D) hb 2
  rw [eLpNorm_norm_rpow X (Lp.aestronglyMeasurable X) (by norm_num : (0 : ℝ)<2)] at he
  norm_num only [ENNReal.ofReal_ofNat,ENNReal.smul_def,NNReal.smul_def,show (2 : ℝ≥0∞)*2=4 by norm_num,ENNReal.rpow_two] at he
  have hc : (c : ℝ≥0∞)=ENNReal.ofReal a := by
    exact ENNReal.coe_nnreal_eq c
  have hh : eLpNorm D 2 P≤ENNReal.ofReal (a*C^2) := by
    calc
      _ ≤ ENNReal.ofReal a*(eLpNorm X 4 P)^2  := by simpa [smul_eq_mul,ENNReal.smul_def,NNReal.smul_def,hc] using he
      _ ≤ ENNReal.ofReal a*(ENNReal.ofReal C)^2 := by gcongr
      _ = _ := by rw [ENNReal.ofReal_mul ha,ENNReal.ofReal_pow hC]
  rw [Lp.norm_def]
  exact (ENNReal.toReal_mono (by simp) hh).trans_eq (ENNReal.toReal_ofReal (by positivity))

variable {ι : Type*} [Fintype ι]
/-- Exact standard-Gaussian L4 radius on any actual probability-space realization. -/
theorem gaussian_eLpNorm_four (P : Measure Ω) (V : Ω → EuclideanSpace ℝ ι)
    (hV : HasLaw V (stdGaussian (EuclideanSpace ℝ ι)) P) :
    eLpNorm V 4 P=ENNReal.ofReal (((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))^(1/4 : ℝ)) := by
  have hm : MemLp V 4 P := hV.memLp (IsGaussian.memLp_id _ 4 (by norm_num))
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num : (4 : ℝ≥0∞)≠0) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
  rw [gaussian_vector_fourth_moment P V hV]

/-- The existing L² kinematic equation inherits its displacement L4 estimate from actual Gaussian velocities. -/
theorem gaussian_kinematic_four_bound (P : Measure Ω)
    (X V : ℝ → Lp (EuclideanSpace ℝ ι) 2 P) (hV : Continuous V)
    (T : ℝ) (hkin : ∀ t ∈ Set.Icc 0 T,X t-X 0=∫ r in 0..t,V r)
    (hlaw : ∀ t ∈ Set.Icc 0 T,HasLaw (V t) (stdGaussian (EuclideanSpace ℝ ι)) P)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    eLpNorm (X t-X 0) 4 P≤ENNReal.ofReal
      (t*(((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))^(1/4 : ℝ))) := by
  let R : ℝ := ((Fintype.card ι : ℝ)^2+2*(Fintype.card ι : ℝ))^(1/4 : ℝ)
  rw [hkin t ht]
  calc
    _ ≤ ENNReal.ofReal t*ENNReal.ofReal R :=
      eLpNorm_four_integral_le P V hV t ht.1 (ENNReal.ofReal R) (fun s hs ↦
        le_of_eq (gaussian_eLpNorm_four P (V s) (hlaw s ⟨hs.1,hs.2.trans ht.2⟩)))
    _ = _ := (ENNReal.ofReal_mul ht.1).symm

end KineticLangevin
