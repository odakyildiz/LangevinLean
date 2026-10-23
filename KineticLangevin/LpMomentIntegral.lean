import KineticLangevin.LpHamiltonianLaw
import Mathlib.Analysis.Convex.Integral

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace KineticLangevin
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] (P : Measure Ω)

def lpFourthBall (R : ℝ≥0∞) : Set (Lp E 2 P) := {X | eLpNorm X 4 P ≤ R}

theorem isClosed_lpFourthBall (R : ℝ≥0∞) : IsClosed (lpFourthBall (E := E) P R) := by
  apply isSeqClosed_iff_isClosed.mp
  intro Xn X hXn hlim
  exact eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hXn)
    (tendstoInMeasure_of_tendsto_Lp hlim) (fun n ↦ Lp.aestronglyMeasurable (Xn n))

theorem convex_lpFourthBall (R : ℝ≥0∞) : Convex ℝ (lpFourthBall (E := E) P R) := by
  intro X hX Y hY a b ha hb hab
  have hcoe : ((a • X + b • Y : Lp E 2 P) : Ω → E) =ᵐ[P]
      fun ω ↦ a • X ω + b • Y ω := by
    filter_upwards [Lp.coeFn_add (a • X) (b • Y),Lp.coeFn_smul a X,Lp.coeFn_smul b Y]
      with ω hadd hX hY
    simp only [Pi.add_apply,Pi.smul_apply] at hadd hX hY
    rw [hadd,hX,hY]
  change eLpNorm (a • X + b • Y : Lp E 2 P) 4 P ≤ R
  rw [eLpNorm_congr_ae hcoe]
  change eLpNorm ((a • (X : Ω → E)) + (b • (Y : Ω → E))) 4 P ≤ R
  calc
    _ ≤ eLpNorm (a • (X : Ω → E)) 4 P + eLpNorm (b • (Y : Ω → E)) 4 P := eLpNorm_add_le (by norm_num)
    _ = ENNReal.ofReal a * eLpNorm X 4 P + ENNReal.ofReal b * eLpNorm Y 4 P := by
      rw [eLpNorm_const_smul,eLpNorm_const_smul,Real.enorm_eq_ofReal ha,Real.enorm_eq_ofReal hb]
    _ ≤ ENNReal.ofReal a * R + ENNReal.ofReal b * R := by
      gcongr
      · exact hX
      · exact hY
    _ = R := by rw [← add_mul,← ENNReal.ofReal_add ha hb,hab];simp

theorem eLpNorm_four_integral_le (v : ℝ → Lp E 2 P) (hv : Continuous v)
    (T : ℝ) (hT : 0 ≤ T) (R : ℝ≥0∞)
    (hbound : ∀ t ∈ Icc 0 T, eLpNorm (v t) 4 P ≤ R) :
    eLpNorm (∫ t in 0..T, v t : Lp E 2 P) 4 P ≤ ENNReal.ofReal T * R := by
  rcases eq_or_lt_of_le hT with hzero | hpos
  · rw [← hzero]
    simp only [intervalIntegral.integral_same,ENNReal.ofReal_zero,zero_mul]
    rw [eLpNorm_congr_ae (Lp.coeFn_zero E 2 P),eLpNorm_zero]
  have hμ0 : (volume : Measure ℝ) (Ioc 0 T) ≠ 0 := by simp [Real.volume_Ioc,sub_zero,ENNReal.ofReal_ne_zero_iff,hpos]
  have hμfinite : (volume : Measure ℝ) (Ioc 0 T) ≠ ⊤ := by simp [Real.volume_Ioc]
  have hmem : ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), v t ∈ lpFourthBall P R := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hbound t ⟨ht.1.le,ht.2⟩
  have havg := (convex_lpFourthBall (E := E) P R).set_average_mem (isClosed_lpFourthBall P R)
    hμ0 hμfinite hmem (hv.intervalIntegrable (μ := volume) 0 T).1
  have heq : (⨍ t in Ioc 0 T, v t) = T⁻¹ • ∫ t in 0..T, v t := by
    rw [average_eq,intervalIntegral.integral_of_le hT]
    simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal hT]
  change eLpNorm (⨍ t in Ioc 0 T, v t : Lp E 2 P) 4 P ≤ R at havg
  rw [heq,eLpNorm_congr_ae (Lp.coeFn_smul T⁻¹ (∫ t in 0..T, v t))] at havg
  change eLpNorm (T⁻¹ • (((∫ t in 0..T, v t : Lp E 2 P)) : Ω → E)) 4 P ≤ R at havg
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal (inv_nonneg.mpr hT)] at havg
  calc
    _ = ENNReal.ofReal T * (ENNReal.ofReal T⁻¹ * eLpNorm (∫ t in 0..T, v t : Lp E 2 P) 4 P) := by
      rw [← mul_assoc,← ENNReal.ofReal_mul hT,mul_inv_cancel₀ hpos.ne',ENNReal.ofReal_one,one_mul]
    _ ≤ _ := by gcongr

end KineticLangevin
