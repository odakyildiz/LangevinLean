import KineticLangevin.SecondOrderRecurrence

noncomputable section
namespace KineticLangevin

/-- Exponential decay is bounded by a reciprocal without an asymptotic assumption. -/
theorem exp_neg_le_reciprocal (x : ℝ) (hx : 0<x) : Real.exp (-x)≤1/x := by
  rw [Real.exp_neg]
  have he : x≤Real.exp x := by linarith [Real.add_one_le_exp x]
  simpa only [one_div] using one_div_le_one_div_of_le hx he

/-- The source cutoff tail admits a global quadratic step-size envelope. -/
theorem secondOrderCutoff_tail_quadratic (m M2 h p : ℝ) (hm : 0<m) (hM2 : 0<M2)
    (hh : 0<h) (hp : 0≤p) (hdim : 4*Real.sqrt (5*p)*M2*h≤m) :
    Real.exp (-(secondOrderCutoff m M2 h-p)/8)≤160*M2^2*h^2/m^2 := by
  have ht := (secondOrderCutoff_tail m M2 h p hm hM2 hh hp hdim).2
  have he := exp_neg_le_reciprocal (m^2/(160*M2^2*h^2)) (by positivity)
  have hid : 1/(m^2/(160*M2^2*h^2))=160*M2^2*h^2/m^2 := by field_simp
  rw [hid] at he
  have he' : Real.exp (-m^2/(160*M2^2*h^2))≤160*M2^2*h^2/m^2 := by simpa only [neg_div] using he
  exact ht.trans he'

/-- A fully explicit coefficient for the second-order bias, uniform in the step h≤1. -/
def secondOrderBiasCoefficient (m M M2 p : ℝ) : ℝ :=
  Real.sqrt 2*(M2*Real.sqrt (p^2+2*p)+M*Real.sqrt (M*p))/m+1280*M*M2^2/m^3

/-- The complete corrected KLMC2 persistent floor is at most an explicit coefficient times h². -/
theorem secondOrder_bias_quadratic (m M M2 h p : ℝ) (hm : 0<m) (hmM : m≤M)
    (hM2 : 0<M2) (hh : 0<h) (hh1 : h≤1) (hp : 0≤p)
    (hdim : 4*Real.sqrt (5*p)*M2*h≤m) :
    Real.sqrt 2*h^2*(M2*Real.sqrt (p^2+2*p)+M*Real.sqrt (M*p))/m+
      8*(M-m)*h/m*Real.exp (-(secondOrderCutoff m M2 h-p)/8)≤
      secondOrderBiasCoefficient m M M2 p*h^2 := by
  have hM : 0≤M := hm.le.trans hmM
  have hB : 0≤M-m := sub_nonneg.mpr hmM
  have ht := secondOrderCutoff_tail_quadratic m M2 h p hm hM2 hh hp hdim
  have h3 : h^3≤h^2 := by nlinarith [mul_le_mul_of_nonneg_left hh1 (sq_nonneg h)]
  have htail : 8*(M-m)*h/m*Real.exp (-(secondOrderCutoff m M2 h-p)/8)≤1280*M*M2^2/m^3*h^2 := by
    calc
      _ ≤ 8*(M-m)*h/m*(160*M2^2*h^2/m^2) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ 8*M*h/m*(160*M2^2*h^2/m^2) := by gcongr;linarith
      _ = (1280*M*M2^2/m^3)*h^3 := by field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)
  calc
    _ ≤ Real.sqrt 2*h^2*(M2*Real.sqrt (p^2+2*p)+M*Real.sqrt (M*p))/m+(1280*M*M2^2/m^3)*h^2 := add_le_add le_rfl htail
    _ = _ := by unfold secondOrderBiasCoefficient;ring

/-- An explicit positive step satisfying both source restrictions and the quadratic epsilon budget. -/
def secondOrderAccuracyStep (m M γ M2 p ε : ℝ) : ℝ :=
  min 1 (min (m/(5*γ*M)) (min (m/(4*Real.sqrt (5*p)*M2))
    (Real.sqrt ((47/50:ℝ)*ε/secondOrderBiasCoefficient m M M2 p))))

/-- The explicit second-order step has all stability, dimension and accuracy properties. -/
theorem secondOrderAccuracyStep_spec (m M γ M2 p ε : ℝ) (hm : 0<m) (hM : 0<M)
    (hγ : 0<γ) (hM2 : 0<M2) (hp : 0<p) (hε : 0<ε) :
    0<secondOrderAccuracyStep m M γ M2 p ε ∧ secondOrderAccuracyStep m M γ M2 p ε≤1 ∧
    5*γ*M*secondOrderAccuracyStep m M γ M2 p ε≤m ∧
    4*Real.sqrt (5*p)*M2*secondOrderAccuracyStep m M γ M2 p ε≤m ∧
    secondOrderBiasCoefficient m M M2 p*(secondOrderAccuracyStep m M γ M2 p ε)^2≤(47/50:ℝ)*ε := by
  let B := secondOrderBiasCoefficient m M M2 p
  have hB : 0<B := by dsimp only [B,secondOrderBiasCoefficient];positivity
  let h := secondOrderAccuracyStep m M γ M2 p ε
  have hh : 0<h := by dsimp only [h,secondOrderAccuracyStep];positivity
  have hcap : h≤1 := min_le_left _ _
  have htail : h≤min (m/(5*γ*M)) (min (m/(4*Real.sqrt (5*p)*M2)) (Real.sqrt ((47/50:ℝ)*ε/B))) := min_le_right _ _
  have hstable := htail.trans (min_le_left _ _)
  have hdim := (htail.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hbias := (htail.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : h^2≤(47/50:ℝ)*ε/B := by
    have he := (sq_le_sq₀ hh.le (Real.sqrt_nonneg _)).mpr hbias
    simpa only [Real.sq_sqrt (by positivity : 0≤(47/50:ℝ)*ε/B)] using he
  refine ⟨hh,hcap,?_,?_,?_⟩
  · have he := (le_div_iff₀ (by positivity : 0<5*γ*M)).mp hstable
    nlinarith
  · have he := (le_div_iff₀ (by positivity : 0<4*Real.sqrt (5*p)*M2)).mp hdim
    nlinarith
  · have he := (le_div_iff₀ hB).mp hs
    change B*h^2≤_
    nlinarith

end KineticLangevin
