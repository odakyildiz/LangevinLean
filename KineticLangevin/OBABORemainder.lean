import KineticLangevin.OBABOEnergy

/-! # Quantitative OBABO remainders

The approximate centered sector is combined with exact algebra and a weighted
Hilbert norm.  Every local error term is bounded from its actual components;
the final algebra theorem recovers the source constant 33 in the step size.
-/

noncomputable section
set_option linter.style.header false
open scoped RealInnerProductSpace
namespace KineticLangevin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def weightedPhaseTransform (a b : ℝ) (s : E × E) : WithLp 2 (E × E) :=
  WithLp.toLp 2 (s.2 + b • s.1, Real.sqrt (a - b ^ 2) • s.1)

def weightedPhaseNorm (a b : ℝ) (s : E × E) : ℝ := ‖weightedPhaseTransform a b s‖

def weightedPhasePairing (a b : ℝ) (s t : E × E) : ℝ :=
  ⟪s.2, t.2⟫ + b * (⟪s.2, t.1⟫ + ⟪s.1, t.2⟫) + a * ⟪s.1, t.1⟫

theorem weightedPhaseNorm_sq (a b : ℝ) (hab : b ^ 2 ≤ a) (s : E × E) :
    weightedPhaseNorm a b s ^ 2 = weightedPhaseEnergy a b s := by
  rw [weightedPhaseNorm, WithLp.prod_norm_sq_eq_of_L2]
  change ‖s.2 + b • s.1‖ ^ 2 + ‖Real.sqrt (a - b ^ 2) • s.1‖ ^ 2 = _
  rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    real_inner_smul_right, mul_pow, mul_pow, sq_abs, sq_abs,
    Real.sq_sqrt (sub_nonneg.mpr hab)]
  unfold weightedPhaseEnergy
  ring

theorem weightedPhasePairing_eq_inner (a b : ℝ) (hab : b ^ 2 ≤ a) (s t : E × E) :
    weightedPhasePairing a b s t =
      ⟪weightedPhaseTransform a b s, weightedPhaseTransform a b t⟫ := by
  simp only [weightedPhasePairing, weightedPhaseTransform, WithLp.prod_inner_apply,
    WithLp.toLp_fst, WithLp.toLp_snd, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  have hs := Real.sq_sqrt (sub_nonneg.mpr hab)
  have hs' := congrArg (fun r : ℝ ↦ r * ⟪s.1, t.1⟫) hs
  nlinarith

theorem weightedPhasePairing_le (a b : ℝ) (hab : b ^ 2 ≤ a) (s t : E × E) :
    weightedPhasePairing a b s t ≤ weightedPhaseNorm a b s * weightedPhaseNorm a b t := by
  rw [weightedPhasePairing_eq_inner a b hab]
  exact real_inner_le_norm _ _

theorem weightedPhaseEnergy_add (a b : ℝ) (s t : E × E) :
    weightedPhaseEnergy a b (s + t) = weightedPhaseEnergy a b s +
      2 * weightedPhasePairing a b s t + weightedPhaseEnergy a b t := by
  simp only [weightedPhaseEnergy, weightedPhasePairing, Prod.fst_add, Prod.snd_add,
    norm_add_sq_real, inner_add_left, inner_add_right, real_inner_comm t.2 s.1]
  ring

theorem weightedPhaseEnergy_smul (a b c : ℝ) (s : E × E) :
    weightedPhaseEnergy a b (c • s) = c ^ 2 * weightedPhaseEnergy a b s := by
  simp only [weightedPhaseEnergy, Prod.smul_fst, Prod.smul_snd, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
  ring

theorem weightedPhaseEnergy_add_le (a b : ℝ) (hab : b ^ 2 ≤ a) (s t : E × E) :
    weightedPhaseEnergy a b (s + t) ≤
      2 * weightedPhaseEnergy a b s + 2 * weightedPhaseEnergy a b t := by
  rw [weightedPhaseEnergy_add]
  have hp := weightedPhasePairing_le a b hab s t
  have hs := sq_nonneg (weightedPhaseNorm a b s - weightedPhaseNorm a b t)
  rw [sub_sq, weightedPhaseNorm_sq a b hab s, weightedPhaseNorm_sq a b hab t] at hs
  nlinarith

theorem weightedPhaseEnergy_euler_remainder (a b h : ℝ) (hab : b ^ 2 ≤ a)
    (s drift remainder : E × E) :
    weightedPhaseEnergy a b (s + h • drift + remainder) ≤
      weightedPhaseEnergy a b s + 2 * h * weightedPhasePairing a b s drift +
      2 * weightedPhaseNorm a b s * weightedPhaseNorm a b remainder +
      2 * h ^ 2 * weightedPhaseEnergy a b drift + 2 * weightedPhaseEnergy a b remainder := by
  have he : s + h • drift + remainder = s + (h • drift + remainder) := by abel
  rw [he, weightedPhaseEnergy_add]
  have hp : weightedPhasePairing a b s (h • drift + remainder) =
      h * weightedPhasePairing a b s drift + weightedPhasePairing a b s remainder := by
    simp only [weightedPhasePairing, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
      inner_add_right, real_inner_smul_right]
    ring
  rw [hp]
  have hpair := weightedPhasePairing_le a b hab s remainder
  have henergy := weightedPhaseEnergy_add_le a b hab (h • drift) remainder
  rw [weightedPhaseEnergy_smul] at henergy
  nlinarith

theorem weightedPhasePairing_kinetic (γ L : ℝ) (hγ : γ ≠ 0) (hL : L ≠ 0) (v x force : E) :
    2 * weightedPhasePairing (1 / L) (1 / γ) (v, x) (-γ • v - force, v) =
      obaboEnergyDerivative γ L v x force := by
  simp only [weightedPhasePairing, obaboEnergyDerivative, inner_sub_right, inner_neg_right,
    real_inner_smul_right, real_inner_smul_left, real_inner_self_eq_norm_sq,
    real_inner_comm v x]
  field_simp [hγ, hL]
  ring

theorem obabo_drift_energy_bound (γ L : ℝ) (hγ : 0 < γ) (hL : 0 < L)
    (hfriction : 4 * L ≤ γ ^ 2) (v x force : E)
    (hforce : ‖force‖ ≤ (17 / 16 : ℝ) * L * ‖x‖ + γ / 8 * ‖v‖) :
    weightedPhaseEnergy (1 / L) (1 / γ) (-γ • v - force, v) ≤
      (13 / 4 : ℝ) * γ ^ 2 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by
  have hequiv := weightedPhaseEnergy_equiv (1 / L) (1 / γ) (by positivity)
    (obabo_metric_condition γ L hγ hL hfriction) (v, x)
  have hbase : L * ‖x‖ ^ 2 + ‖v‖ ^ 2 ≤
      2 * L * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by
    have hs := mul_le_mul_of_nonneg_left hequiv.1 (by positivity : 0 ≤ 2 * L)
    unfold weightedBaseEnergy at hs
    convert hs using 1 <;> field_simp
  have hid : L * weightedPhaseEnergy (1 / L) (1 / γ) (-γ • v - force, v) =
      (γ ^ 2 - L) * ‖v‖ ^ 2 + ‖force‖ ^ 2 +
        2 * (γ - L / γ) * ⟪v, force⟫ := by
    simp only [weightedPhaseEnergy, norm_sub_sq_real, norm_neg, norm_smul,
      Real.norm_eq_abs, abs_neg, abs_of_pos hγ, mul_pow, inner_neg_left,
      inner_sub_right, real_inner_smul_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hc : 0 ≤ γ - L / γ := by
    have hg : L / γ ≤ γ := (div_le_iff₀ hγ).mpr (by nlinarith)
    linarith
  have hi := mul_le_mul_of_nonneg_left (real_inner_le_norm v force)
    (by positivity : 0 ≤ 2 * (γ - L / γ))
  have hnorm : 0 ≤ ‖v‖ * ‖force‖ := by positivity
  have hLg : 0 ≤ L / γ := by positivity
  have hn : (γ - L / γ) * (‖v‖ * ‖force‖) ≤ γ * (‖v‖ * ‖force‖) := by
    exact mul_le_mul_of_nonneg_right (by linarith) hnorm
  have hsq := (sq_le_sq₀ (norm_nonneg force) (by positivity :
    0 ≤ (17 / 16 : ℝ) * L * ‖x‖ + γ / 8 * ‖v‖)).mpr hforce
  have hlinear := mul_le_mul_of_nonneg_left hforce (by positivity : 0 ≤ 2 * γ * ‖v‖)
  have hyoung := sq_nonneg (γ * ‖x‖ - 2 * ‖v‖)
  have hyoungScaled := mul_nonneg (by positivity : 0 ≤ (153 / 256 : ℝ) * L) hyoung
  have hLX := mul_nonneg (by nlinarith : 0 ≤ γ ^ 2 - 4 * L)
    (by positivity : 0 ≤ (289 / 1024 : ℝ) * L * ‖x‖ ^ 2)
  have hLV := mul_nonneg (by nlinarith : 0 ≤ γ ^ 2 - 4 * L)
    (by positivity : 0 ≤ (89 / 256 : ℝ) * ‖v‖ ^ 2)
  have hraw : L * weightedPhaseEnergy (1 / L) (1 / γ) (-γ • v - force, v) ≤
      (13 / 8 : ℝ) * γ ^ 2 * (L * ‖x‖ ^ 2 + ‖v‖ ^ 2) := by
    have hX : 0 ≤ (13 / 8 - 901 / 1024 : ℝ) * γ ^ 2 * L * ‖x‖ ^ 2 := by positivity
    have hV : 0 ≤ (13 / 8 - 413 / 256 : ℝ) * γ ^ 2 * ‖v‖ ^ 2 := by positivity
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ (13 / 8 : ℝ) * γ ^ 2)
  have hfinal : L * weightedPhaseEnergy (1 / L) (1 / γ) (-γ • v - force, v) ≤
      L * ((13 / 4 : ℝ) * γ ^ 2 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x)) := by nlinarith
  exact (mul_le_mul_iff_right₀ hL).mp hfinal

theorem obabo_remainder_energy_bound (γ L h : ℝ) (hγ : 0 < γ) (hL : 0 < L)
    (hfriction : 4 * L ≤ γ ^ 2) (v x : E) (r : E × E)
    (hposition : ‖r.2‖ ≤ h ^ 2 * (γ / 2 * ‖v‖ + L / 2 * ‖x‖))
    (hvelocity : ‖r.1‖ ≤ h ^ 2 * ((9 / 16 : ℝ) * γ * L * ‖x‖ +
      (5 / 8 : ℝ) * γ ^ 2 * ‖v‖)) :
    weightedPhaseEnergy (1 / L) (1 / γ) r ≤
      3 * h ^ 4 * γ ^ 4 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by
  have hmetric := obabo_metric_condition γ L hγ hL hfriction
  have he0 := (weightedPhaseEnergy_equiv (1 / L) (1 / γ) (by positivity) hmetric (v, x)).1
  have heR := (weightedPhaseEnergy_equiv (1 / L) (1 / γ) (by positivity) hmetric r).2
  have hbase : L * ‖x‖ ^ 2 + ‖v‖ ^ 2 ≤
      2 * L * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by
    have hs := mul_le_mul_of_nonneg_left he0 (by positivity : 0 ≤ 2 * L)
    unfold weightedBaseEnergy at hs
    convert hs using 1 <;> field_simp
  have hRupper : L * weightedPhaseEnergy (1 / L) (1 / γ) r ≤
      (3 / 2 : ℝ) * (L * ‖r.2‖ ^ 2 + ‖r.1‖ ^ 2) := by
    have hs := mul_le_mul_of_nonneg_left heR hL.le
    unfold weightedBaseEnergy at hs
    convert hs using 1 <;> field_simp
  have hpSq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hposition
  have hvSq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hvelocity
  have hpSum := sq_nonneg (γ / 2 * ‖v‖ - L / 2 * ‖x‖)
  have hvSum := sq_nonneg ((9 / 16 : ℝ) * γ * L * ‖x‖ - (5 / 8 : ℝ) * γ ^ 2 * ‖v‖)
  have hpSumScaled := mul_nonneg (sq_nonneg (h ^ 2)) hpSum
  have hvSumScaled := mul_nonneg (sq_nonneg (h ^ 2)) hvSum
  have hpBound : ‖r.2‖ ^ 2 ≤ h ^ 4 * (γ ^ 2 / 2 * ‖v‖ ^ 2 + L ^ 2 / 2 * ‖x‖ ^ 2) := by
    nlinarith
  have hvBound : ‖r.1‖ ^ 2 ≤ h ^ 4 *
      ((81 / 128 : ℝ) * γ ^ 2 * L ^ 2 * ‖x‖ ^ 2 + (25 / 32 : ℝ) * γ ^ 4 * ‖v‖ ^ 2) := by
    nlinarith
  have hLG := mul_le_mul_of_nonneg_right hfriction (sq_nonneg γ)
  have hLsq := (sq_le_sq₀ hL.le (by positivity : 0 ≤ γ ^ 2 / 4)).mpr
    (show L ≤ γ ^ 2 / 4 by linarith)
  have hcX : L ^ 2 / 2 + (81 / 128 : ℝ) * γ ^ 2 * L ≤ γ ^ 4 := by nlinarith
  have hcV : L * γ ^ 2 / 2 + (25 / 32 : ℝ) * γ ^ 4 ≤ γ ^ 4 := by nlinarith
  have hcXscaled := mul_le_mul_of_nonneg_right hcX
    (by positivity : 0 ≤ (3 / 2 : ℝ) * h ^ 4 * L * ‖x‖ ^ 2)
  have hcVscaled := mul_le_mul_of_nonneg_right hcV
    (by positivity : 0 ≤ (3 / 2 : ℝ) * h ^ 4 * ‖v‖ ^ 2)
  have hpScaled := mul_le_mul_of_nonneg_left hpBound (by positivity : 0 ≤ (3 / 2 : ℝ) * L)
  have hvScaled := mul_le_mul_of_nonneg_left hvBound (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hraw : L * weightedPhaseEnergy (1 / L) (1 / γ) r ≤
      (3 / 2 : ℝ) * h ^ 4 * γ ^ 4 * (L * ‖x‖ ^ 2 + ‖v‖ ^ 2) := by
    nlinarith only [hRupper, hpScaled, hvScaled, hcXscaled, hcVscaled]
  have hscaled := mul_le_mul_of_nonneg_left hbase
    (by positivity : 0 ≤ (3 / 2 : ℝ) * h ^ 4 * γ ^ 4)
  have hfinal : L * weightedPhaseEnergy (1 / L) (1 / γ) r ≤
      L * (3 * h ^ 4 * γ ^ 4 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x)) := by nlinarith only [hraw, hscaled]
  exact (mul_le_mul_iff_right₀ hL).mp hfinal

theorem obabo_sector_correction_bound (γ L h err : ℝ)
    (hγ : 0 < γ) (hL : 0 < L) (hh : 0 ≤ h) (hfriction : 4 * L ≤ γ ^ 2)
    (hsmall : γ * h ≤ 1) (herr : 0 ≤ err) (v x : E)
    (herrBound : err ≤ h * L * (‖v‖ / 2 + γ * ‖x‖ / 16)) :
    h * (2 * err * ‖x‖ / γ + err ^ 2 / (γ * L)) ≤
      (1 / 2 : ℝ) * γ ^ 2 * h ^ 2 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by
  have hmetric := obabo_metric_condition γ L hγ hL hfriction
  have he0 := (weightedPhaseEnergy_equiv (1 / L) (1 / γ) (by positivity) hmetric (v, x)).1
  have hbase : L * ‖x‖ ^ 2 + ‖v‖ ^ 2 ≤
      2 * L * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by
    have hs := mul_le_mul_of_nonneg_left he0 (by positivity : 0 ≤ 2 * L)
    unfold weightedBaseEnergy at hs
    convert hs using 1 <;> field_simp
  have hsq := (sq_le_sq₀ herr (by positivity)).mpr herrBound
  have hyoung := sq_nonneg (‖v‖ / 2 - γ * ‖x‖ / 16)
  have hyoungScaled := mul_nonneg (by positivity : 0 ≤ h ^ 2 * L ^ 2) hyoung
  have herrSq : err ^ 2 ≤ h ^ 2 * (L ^ 2 / 2 * ‖v‖ ^ 2 + γ ^ 2 * L ^ 2 / 128 * ‖x‖ ^ 2) := by
    nlinarith only [hsq, hyoungScaled]
  have heX := mul_le_mul_of_nonneg_right herrBound (by positivity : 0 ≤ 2 * L * h * ‖x‖)
  have hvx := sq_nonneg (γ * ‖x‖ - 2 * ‖v‖)
  have hvxScaled := mul_nonneg (by positivity : 0 ≤ h ^ 2 * L ^ 2 / 4) hvx
  have heXγ := mul_le_mul_of_nonneg_left heX hγ.le
  have heXBound : γ * (2 * L * h * err * ‖x‖) ≤
      h ^ 2 * ((3 / 8 : ℝ) * γ ^ 2 * L ^ 2 * ‖x‖ ^ 2 + L ^ 2 * ‖v‖ ^ 2) := by
    nlinarith only [heXγ, hvxScaled]
  have herrSqScaled := mul_le_mul_of_nonneg_left herrSq (mul_nonneg hγ.le hh)
  have hsX := mul_le_mul_of_nonneg_right hsmall
    (by positivity : 0 ≤ h ^ 2 * γ ^ 2 * L ^ 2 / 128 * ‖x‖ ^ 2)
  have hsV := mul_le_mul_of_nonneg_right hsmall
    (by positivity : 0 ≤ h ^ 2 * L ^ 2 / 2 * ‖v‖ ^ 2)
  have herrSqBound : γ * (h * err ^ 2) ≤ h ^ 2 *
      (γ ^ 2 * L ^ 2 / 128 * ‖x‖ ^ 2 + L ^ 2 / 2 * ‖v‖ ^ 2) := by
    nlinarith only [herrSqScaled, hsX, hsV]
  have hcV := mul_le_mul_of_nonneg_right hfriction
    (by positivity : 0 ≤ h ^ 2 * L / 2 * ‖v‖ ^ 2)
  have hraw : γ * (2 * L * h * err * ‖x‖ + h * err ^ 2) ≤
      (1 / 2 : ℝ) * γ ^ 2 * L * h ^ 2 * (L * ‖x‖ ^ 2 + ‖v‖ ^ 2) := by
    have hxpos : 0 ≤ (15 / 128 : ℝ) * γ ^ 2 * L ^ 2 * h ^ 2 * ‖x‖ ^ 2 := by positivity
    have hvpos : 0 ≤ (1 / 2 : ℝ) * L ^ 2 * h ^ 2 * ‖v‖ ^ 2 := by positivity
    nlinarith only [heXBound, herrSqBound, hcV, hxpos, hvpos]
  have henergy := weightedPhaseEnergy_nonneg (1 / L) (1 / γ) (by positivity) hmetric (v, x)
  have hb := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ γ ^ 2 * L * h ^ 2 / 2)
  have hc := mul_le_mul_of_nonneg_right hfriction
    (by positivity : 0 ≤ γ ^ 2 * L * h ^ 2 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) / 4)
  have hclear : γ * (2 * L * h * err * ‖x‖ + h * err ^ 2) ≤
      γ ^ 2 * L * ((1 / 2 : ℝ) * γ ^ 2 * h ^ 2 *
        weightedPhaseEnergy (1 / L) (1 / γ) (v, x)) := by
    have hepos : 0 ≤ γ ^ 4 * L * h ^ 2 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) / 4 := by positivity
    nlinarith only [hraw, hb, hc, hepos]
  have hdiv := div_le_div_of_nonneg_right hclear (by positivity : 0 ≤ γ ^ 2 * L)
  convert hdiv using 1 <;> field_simp <;> ring

theorem obabo_euler_remainder_contraction (γ L m h err : ℝ)
    (hγ : 0 < γ) (hL : 0 < L) (hh : 0 ≤ h) (hfriction : 4 * L ≤ γ ^ 2)
    (hsmall : γ * h ≤ 1) (hsmallSq : 12 * γ ^ 2 * h ^ 2 ≤ 1)
    (hstep : 33 * γ ^ 3 * h ≤ m) (herr : 0 ≤ err) (v x force : E) (r : E × E)
    (herrBound : err ≤ h * L * (‖v‖ / 2 + γ * ‖x‖ / 16))
    (hforce : ‖force‖ ≤ (17 / 16 : ℝ) * L * ‖x‖ + γ / 8 * ‖v‖)
    (hposition : ‖r.2‖ ≤ h ^ 2 * (γ / 2 * ‖v‖ + L / 2 * ‖x‖))
    (hvelocity : ‖r.1‖ ≤ h ^ 2 * ((9 / 16 : ℝ) * γ * L * ‖x‖ +
      (5 / 8 : ℝ) * γ ^ 2 * ‖v‖))
    (hdrift : obaboEnergyDerivative γ L v x force ≤
      (-2 * m / (3 * γ)) * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) +
        2 * err * ‖x‖ / γ + err ^ 2 / (γ * L)) :
    weightedPhaseEnergy (1 / L) (1 / γ) ((v, x) + h • (-γ • v - force, v) + r) ≤
      (1 - m * h / (3 * γ)) * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by
  have hmetric := obabo_metric_condition γ L hγ hL hfriction
  have hab : (1 / γ) ^ 2 ≤ 1 / L := by nlinarith [sq_nonneg (1 / γ)]
  have he := weightedPhaseEnergy_euler_remainder (1 / L) (1 / γ) h hab
    (v, x) (-γ • v - force, v) r
  have hA := obabo_drift_energy_bound γ L hγ hL hfriction v x force hforce
  have hR := obabo_remainder_energy_bound γ L h hγ hL hfriction v x r hposition hvelocity
  have hcorrection := obabo_sector_correction_bound γ L h err hγ hL hh hfriction hsmall herr v x herrBound
  have hE := weightedPhaseEnergy_nonneg (1 / L) (1 / γ) (by positivity) hmetric (v, x)
  have hN0 : 0 ≤ weightedPhaseNorm (1 / L) (1 / γ) (v, x) := norm_nonneg _
  have hNR : 0 ≤ weightedPhaseNorm (1 / L) (1 / γ) r := norm_nonneg _
  have hNRsq := weightedPhaseNorm_sq (1 / L) (1 / γ) hab r
  have hN0sq := weightedPhaseNorm_sq (1 / L) (1 / γ) hab (v, x)
  have hNRbound : weightedPhaseNorm (1 / L) (1 / γ) r ≤
      (7 / 4 : ℝ) * h ^ 2 * γ ^ 2 * weightedPhaseNorm (1 / L) (1 / γ) (v, x) := by
    apply (sq_le_sq₀ hNR (by positivity)).mp
    have hgap : 0 ≤ (1 / 16 : ℝ) * h ^ 4 * γ ^ 4 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by positivity
    rw [mul_pow, mul_pow, mul_pow, hN0sq, hNRsq]
    norm_num
    simp only [one_div] at hR hgap
    nlinarith only [hR, hgap]
  have hcross := mul_le_mul_of_nonneg_left hNRbound (by positivity : 0 ≤ 2 * weightedPhaseNorm (1 / L) (1 / γ) (v, x))
  rw [show 2 * weightedPhaseNorm (1 / L) (1 / γ) (v, x) *
      ((7 / 4 : ℝ) * h ^ 2 * γ ^ 2 * weightedPhaseNorm (1 / L) (1 / γ) (v, x)) =
      (7 / 2 : ℝ) * h ^ 2 * γ ^ 2 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) by
        calc
          _ = (7 / 2 : ℝ) * h ^ 2 * γ ^ 2 * weightedPhaseNorm (1 / L) (1 / γ) (v, x) ^ 2 := by ring
          _ = _ := by rw [hN0sq]] at hcross
  have hAscaled := mul_le_mul_of_nonneg_left hA (by positivity : 0 ≤ 2 * h ^ 2)
  have hRscaled := mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 2)
  have hsmallScaled := mul_le_mul_of_nonneg_right hsmallSq
    (by positivity : 0 ≤ h ^ 2 * γ ^ 2 * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) / 2)
  have hdriftScaled := mul_le_mul_of_nonneg_left hdrift hh
  rw [← weightedPhasePairing_kinetic γ L hγ.ne' hL.ne' v x force] at hdriftScaled
  have hpre : weightedPhaseEnergy (1 / L) (1 / γ) ((v, x) + h • (-γ • v - force, v) + r) ≤
      (1 - 2 * m * h / (3 * γ) + 11 * γ ^ 2 * h ^ 2) *
        weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by
    simp only [div_eq_mul_inv, mul_inv_rev, one_mul] at he hcross hAscaled hRscaled hsmallScaled hdriftScaled hcorrection ⊢
    nlinarith only [he, hcross, hAscaled, hRscaled, hsmallScaled, hdriftScaled, hcorrection]
  have hs := mul_le_mul_of_nonneg_right hstep hh
  have hsdiv : 11 * γ ^ 2 * h ^ 2 ≤ m * h / (3 * γ) := by
    apply (le_div_iff₀ (by positivity : 0 < 3 * γ)).mpr
    nlinarith only [hs]
  have hlast := mul_le_mul_of_nonneg_right hsdiv hE
  simp only [div_eq_mul_inv, mul_inv_rev] at hpre hlast ⊢
  nlinarith only [hpre, hlast]

theorem obabo_algebra_contraction (γ L m h δ err : ℝ)
    (hγ : 0 < γ) (hL : 0 < L) (hh : 0 ≤ h) (hfriction : 4 * L ≤ γ ^ 2)
    (hsmall : γ * h ≤ 1) (hsmallSq : 12 * γ ^ 2 * h ^ 2 ≤ 1)
    (hstep : 33 * γ ^ 3 * h ≤ m) (herr : 0 ≤ err)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hδgap : 1 - δ ≤ γ * h / 2)
    (hδsq0 : 0 ≤ δ ^ 2 - 1 + γ * h)
    (hδsq : δ ^ 2 - 1 + γ * h ≤ γ ^ 2 * h ^ 2 / 2)
    (v x F0 force : E) (hF0 : ‖F0‖ ≤ L * ‖x‖)
    (herrBound : err ≤ L / 2 * (h * ‖v‖ + h ^ 2 * L / 2 * ‖x‖))
    (hforce0 : ‖force‖ ≤ L * ‖x‖ + err)
    (hdrift : obaboEnergyDerivative γ L v x force ≤
      (-2 * m / (3 * γ)) * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) +
        2 * err * ‖x‖ / γ + err ^ 2 / (γ * L)) :
    weightedPhaseEnergy (1 / L) (1 / γ)
      (δ ^ 2 • v - (h * δ) • force, x + (h * δ) • v - (h ^ 2 / 2) • F0) ≤
      (1 - m * h / (3 * γ)) * weightedPhaseEnergy (1 / L) (1 / γ) (v, x) := by
  have hLh : L * h ≤ γ / 4 := by
    have hf := mul_le_mul_of_nonneg_right hfriction hh
    have hs := mul_le_mul_of_nonneg_left hsmall hγ.le
    nlinarith only [hf, hs]
  have heB : err ≤ h * L * (‖v‖ / 2 + γ * ‖x‖ / 16) := by
    have hs := mul_le_mul_of_nonneg_right hLh (by positivity : 0 ≤ h * L * ‖x‖ / 4)
    nlinarith only [herrBound, hs]
  have hforce : ‖force‖ ≤ (17 / 16 : ℝ) * L * ‖x‖ + γ / 8 * ‖v‖ := by
    have hsX := mul_le_mul_of_nonneg_right hsmall (by positivity : 0 ≤ L * ‖x‖ / 16)
    have hsV := mul_le_mul_of_nonneg_right hLh (by positivity : 0 ≤ ‖v‖ / 2)
    nlinarith only [hforce0, heB, hsX, hsV]
  let r : E × E := ((δ ^ 2 - 1 + γ * h) • v + (h * (1 - δ)) • force,
    (h * (δ - 1)) • v - (h ^ 2 / 2) • F0)
  have hposition : ‖r.2‖ ≤ h ^ 2 * (γ / 2 * ‖v‖ + L / 2 * ‖x‖) := by
    have ht := norm_sub_le ((h * (δ - 1)) • v) ((h ^ 2 / 2) • F0)
    simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hh,
      abs_of_nonpos (sub_nonpos.mpr hδ1), abs_of_nonneg (by positivity : 0 ≤ h ^ 2 / 2)] at ht
    have hg := mul_le_mul_of_nonneg_right hδgap (by positivity : 0 ≤ h * ‖v‖)
    have hf := mul_le_mul_of_nonneg_left hF0 (by positivity : 0 ≤ h ^ 2 / 2)
    dsimp [r]
    nlinarith only [ht, hg, hf]
  have hvelocity : ‖r.1‖ ≤ h ^ 2 * ((9 / 16 : ℝ) * γ * L * ‖x‖ + (5 / 8 : ℝ) * γ ^ 2 * ‖v‖) := by
    have ht := norm_add_le ((δ ^ 2 - 1 + γ * h) • v) ((h * (1 - δ)) • force)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδsq0,
      abs_of_nonneg (mul_nonneg hh (sub_nonneg.mpr hδ1))] at ht
    have hg := mul_le_mul_of_nonneg_right hδgap (by positivity : 0 ≤ h * ‖force‖)
    have hf := mul_le_mul_of_nonneg_left hforce (by positivity : 0 ≤ γ * h ^ 2 / 2)
    have hs := mul_le_mul_of_nonneg_right hδsq (norm_nonneg v)
    have hxpos : 0 ≤ γ * L * h ^ 2 * ‖x‖ / 32 := by positivity
    have hvpos : 0 ≤ γ ^ 2 * h ^ 2 * ‖v‖ / 16 := by positivity
    dsimp [r]
    nlinarith only [ht, hg, hf, hs, hxpos, hvpos]
  have he := obabo_euler_remainder_contraction γ L m h err hγ hL hh hfriction
    hsmall hsmallSq hstep herr v x force r heB hforce hposition hvelocity hdrift
  have hid : (v, x) + h • (-γ • v - force, v) + r =
      (δ ^ 2 • v - (h * δ) • force, x + (h * δ) • v - (h ^ 2 / 2) • F0) := by
    dsimp [r]
    ext <;> module
  rwa [hid] at he

end KineticLangevin
