import KineticLangevin.Complexity
import KineticLangevin.ConditionNumber
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

noncomputable section
namespace KineticLangevin

/-- The manuscript's explicit second-order prescription when its last, exponential tail is omitted.
The requested error is normalized as epsilon/sqrt(m). -/
def secondOrderTailFreeStep (m M γ M2 p ε : ℝ) : ℝ :=
  min (m/(5*γ*M)) (min (m/(4*Real.sqrt (5*p)*M2))
    (Real.sqrt (ε*Real.sqrt m/(4*M2*p+2*M*Real.sqrt (2*M*p)))))

/-- The exact reciprocal of the three-way minimum, with no asymptotic simplification. -/
def secondOrderTailFreeInverse (m M γ M2 p ε : ℝ) : ℝ :=
  max (5*γ*M/m) (max (4*Real.sqrt (5*p)*M2/m)
    (Real.sqrt ((4*M2*p+2*M*Real.sqrt (2*M*p))/(ε*Real.sqrt m))))

/-- All source restrictions and the exact normalized quadratic-bias budget hold for the chosen step. -/
theorem secondOrderTailFreeStep_spec (m M γ M2 p ε : ℝ)
    (hm : 0<m) (hM : 0<M) (hγ : 0<γ) (hM2 : 0<M2) (hp : 0<p) (hε : 0<ε) :
    0<secondOrderTailFreeStep m M γ M2 p ε ∧
    5*γ*M*secondOrderTailFreeStep m M γ M2 p ε≤m ∧
    4*Real.sqrt (5*p)*M2*secondOrderTailFreeStep m M γ M2 p ε≤m ∧
    2*(secondOrderTailFreeStep m M γ M2 p ε)^2*M2*p/m+
      (secondOrderTailFreeStep m M γ M2 p ε)^2*M*Real.sqrt (2*M*p)/m≤ε/(2*Real.sqrt m) := by
  let B := 4*M2*p+2*M*Real.sqrt (2*M*p)
  have hB : 0<B := by dsimp [B]; positivity
  let h := secondOrderTailFreeStep m M γ M2 p ε
  have hh : 0<h := by dsimp [h,secondOrderTailFreeStep]; positivity
  have hstable : h≤m/(5*γ*M) := min_le_left _ _
  have hdim : h≤m/(4*Real.sqrt (5*p)*M2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have haccurate : h≤Real.sqrt (ε*Real.sqrt m/B) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsq : h^2≤ε*Real.sqrt m/B := by
    have hs := (sq_le_sq₀ hh.le (Real.sqrt_nonneg _)).mpr haccurate
    simpa only [Real.sq_sqrt (by positivity : 0≤ε*Real.sqrt m/B)] using hs
  have hb : B*h^2≤ε*Real.sqrt m := by
    have hb := (le_div_iff₀ hB).mp hsq
    nlinarith only [hb]
  refine ⟨hh,?_,?_,?_⟩
  · have hs := (le_div_iff₀ (by positivity : 0<5*γ*M)).mp hstable
    nlinarith only [hs]
  · have hd := (le_div_iff₀ (by positivity : 0<4*Real.sqrt (5*p)*M2)).mp hdim
    nlinarith only [hd]
  · change 2*h^2*M2*p/m+h^2*M*Real.sqrt (2*M*p)/m≤_
    calc
      _ = B*h^2/(2*m) := by dsimp [B]; ring
      _ ≤ ε*Real.sqrt m/(2*m) := div_le_div_of_nonneg_right hb (by positivity)
      _ = ε/(2*Real.sqrt m) := by
        have hs : 0<Real.sqrt m := Real.sqrt_pos.mpr hm
        apply (div_eq_div_iff (by positivity : (2*m:ℝ)≠0) (by positivity : (2*Real.sqrt m:ℝ)≠0)).mpr
        calc
          ε*Real.sqrt m*(2*Real.sqrt m)=2*ε*(Real.sqrt m)^2 := by ring
          _=ε*(2*m) := by rw [Real.sq_sqrt hm.le]; ring

/-- Inversion exchanges a positive minimum with the maximum of its reciprocals. -/
theorem inverse_min_of_pos (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (min a b)⁻¹=max a⁻¹ b⁻¹ := by
  rcases le_total a b with hab|hba
  · have hi : b⁻¹≤a⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le ha hab
    rw [min_eq_left hab,max_eq_left hi]
  · have hi : a⁻¹≤b⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hb hba
    rw [min_eq_right hba,max_eq_right hi]

/-- The inverse-step identity retains all three possible active restrictions exactly. -/
theorem secondOrderTailFreeStep_inverse (m M γ M2 p ε : ℝ)
    (hm : 0<m) (hM : 0<M) (hγ : 0<γ) (hM2 : 0<M2) (hp : 0<p) (hε : 0<ε) :
    (secondOrderTailFreeStep m M γ M2 p ε)⁻¹=secondOrderTailFreeInverse m M γ M2 p ε := by
  unfold secondOrderTailFreeStep secondOrderTailFreeInverse
  rw [inverse_min_of_pos _ _ (by positivity) (by positivity),
    inverse_min_of_pos _ _ (by positivity) (by positivity)]
  simp only [inv_div,← Real.sqrt_inv,inv_div]

/-- This is the exact reciprocal-step factor printed before the manuscript's condition-number shorthand. -/
theorem secondOrderTailFreeStep_work (m M γ M2 p ε : ℝ)
    (hm : 0<m) (hM : 0<M) (hγ : 0<γ) (hM2 : 0<M2) (hp : 0<p) (hε : 0<ε) :
    Real.sqrt M/(m*secondOrderTailFreeStep m M γ M2 p ε)=
      (Real.sqrt M/m)*secondOrderTailFreeInverse m M γ M2 p ε := by
  rw [← secondOrderTailFreeStep_inverse m M γ M2 p ε hm hM hγ hM2 hp hε]
  ring

/-- Rounding the logarithmic threshold to a natural number adds strictly less than one iteration. -/
theorem firstOrderIterationCount_lt (α D ε : ℝ) (hα : 0<α) :
    (firstOrderIterationCount α D ε:ℝ)<1+max 0 (Real.log (24*D/ε))/α := by
  have hc := Nat.ceil_lt_add_one (le_max_left (0:ℝ) (Real.log (24*D/ε)/α))
  have he : max 0 (Real.log (24*D/ε)/α)=max 0 (Real.log (24*D/ε))/α := by
    simpa only [zero_div] using max_div_div_right hα.le (0:ℝ) (Real.log (24*D/ε))
  simpa only [firstOrderIterationCount,he,add_comm] using hc

/-- A fully explicit integer-count upper bound for normalized epsilon precision in the tail-free prescription. -/
theorem secondOrderTailFree_iterationCount_lt (m M γ M2 p ε D : ℝ)
    (hm : 0<m) (hM : 0<M) (hγ : 0<γ) (hM2 : 0<M2) (hp : 0<p) (hε : 0<ε) :
    (firstOrderIterationCount (m*secondOrderTailFreeStep m M γ M2 p ε/(4*γ)) D
      (ε/Real.sqrt m):ℝ)<
      1+(4*γ/m)*secondOrderTailFreeInverse m M γ M2 p ε*
        max 0 (Real.log (24*D*Real.sqrt m/ε)) := by
  have hh := (secondOrderTailFreeStep_spec m M γ M2 p ε hm hM hγ hM2 hp hε).1
  have hc := firstOrderIterationCount_lt
    (m*secondOrderTailFreeStep m M γ M2 p ε/(4*γ)) D (ε/Real.sqrt m) (by positivity)
  have he : 24*D/(ε/Real.sqrt m)=24*D*Real.sqrt m/ε := by field_simp
  rw [he] at hc
  convert hc using 1
  rw [← secondOrderTailFreeStep_inverse m M γ M2 p ε hm hM hγ hM2 hp hε]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

/-- Increasing positive friction makes the source's admissible minimum step no larger. -/
theorem secondOrderTailFreeStep_antitone_friction (m M γ γ' M2 p ε : ℝ)
    (hm : 0≤m) (hM : 0<M) (hγ : 0<γ) (hγγ' : γ≤γ') :
    secondOrderTailFreeStep m M γ' M2 p ε≤secondOrderTailFreeStep m M γ M2 p ε := by
  unfold secondOrderTailFreeStep
  apply min_le_min
  · exact div_le_div_of_nonneg_left hm (by positivity) (by gcongr)
  · exact le_rfl

/-- The geometric part of the source bound is monotone in positive friction at fixed step. -/
theorem secondOrder_transient_monotone_friction (m h γ γ' D : ℝ) (n : ℕ)
    (hm : 0≤m) (hh : 0≤h) (hγ : 0<γ) (hγγ' : γ≤γ')
    (hstable : m*h≤4*γ) (hD : 0≤D) :
    Real.sqrt 2*(1-m*h/(4*γ))^n*D≤Real.sqrt 2*(1-m*h/(4*γ'))^n*D := by
  have hα : m*h/(4*γ')≤m*h/(4*γ) :=
    div_le_div_of_nonneg_left (mul_nonneg hm hh) (by positivity) (by gcongr)
  have hα1 : m*h/(4*γ)≤1 := (div_le_one (by positivity)).mpr hstable
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) n)
      (Real.sqrt_nonneg 2)) hD

/-- Exact normalization connects the reciprocal step to the corrected dimensionless condition-number analysis. -/
theorem secondOrderTailFreeInverse_normalized_work (m M M2 p ε : ℝ)
    (hm : 0<m) (hM : 0≤M) (hε : ε≠0) :
    (4*Real.sqrt (m+M)/m)*secondOrderTailFreeInverse m M (Real.sqrt (m+M)) M2 p ε=
      secondOrderNormalizedWork (M/m) (M2/(m*Real.sqrt m)) p ε := by
  have hs : 0<Real.sqrt m := Real.sqrt_pos.mpr hm
  have hγ : Real.sqrt (m+M)=Real.sqrt m*Real.sqrt (1+M/m) := by
    have he : m+M=m*(1+M/m) := by field_simp
    rw [he,Real.sqrt_mul hm.le]
  have hκ : Real.sqrt (M/m)=Real.sqrt M/Real.sqrt m := Real.sqrt_div hM m
  have hMp : Real.sqrt (2*M*p)=Real.sqrt 2*Real.sqrt M*Real.sqrt p := by
    rw [mul_assoc,Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_mul hM]
    ring
  have hfirst : 5*Real.sqrt (m+M)*M/m=
      Real.sqrt m*(5*(M/m)*Real.sqrt (1+M/m)) := by rw [hγ]; ring
  have hsecond : 4*Real.sqrt (5*p)*M2/m=
      Real.sqrt m*(4*Real.sqrt (5*p)*(M2/(m*Real.sqrt m))) := by
    field_simp
  have hN : (4*M2*p+2*M*Real.sqrt (2*M*p))/(ε*Real.sqrt m)=
      m*((4*(M2/(m*Real.sqrt m))*p+
        2*Real.sqrt 2*(M/m)*Real.sqrt (M/m)*Real.sqrt p)/ε) := by
    rw [hκ,hMp]
    field_simp
  have hthird : Real.sqrt ((4*M2*p+2*M*Real.sqrt (2*M*p))/(ε*Real.sqrt m))=
      Real.sqrt m*Real.sqrt ((4*(M2/(m*Real.sqrt m))*p+
        2*Real.sqrt 2*(M/m)*Real.sqrt (M/m)*Real.sqrt p)/ε) := by
    rw [hN,Real.sqrt_mul hm.le]
  have hQ : secondOrderTailFreeInverse m M (Real.sqrt (m+M)) M2 p ε=
      Real.sqrt m*max (5*(M/m)*Real.sqrt (1+M/m))
        (max (4*Real.sqrt (5*p)*(M2/(m*Real.sqrt m)))
          (Real.sqrt ((4*(M2/(m*Real.sqrt m))*p+
            2*Real.sqrt 2*(M/m)*Real.sqrt (M/m)*Real.sqrt p)/ε))) := by
    unfold secondOrderTailFreeInverse
    rw [hfirst,hsecond,hthird,← mul_max_of_nonneg _ _ hs.le,← mul_max_of_nonneg _ _ hs.le]
  rw [hQ,hγ,secondOrderNormalizedWork]
  calc
    _ = ((Real.sqrt m)^2/m)*
        (4*Real.sqrt (1+M/m)*max (5*(M/m)*Real.sqrt (1+M/m))
          (max (4*Real.sqrt (5*p)*(M2/(m*Real.sqrt m)))
            (Real.sqrt ((4*(M2/(m*Real.sqrt m))*p+
              2*Real.sqrt 2*(M/m)*Real.sqrt (M/m)*Real.sqrt p)/ε)))) := by ring
    _ = _ := by rw [Real.sq_sqrt hm.le,div_self hm.ne',one_mul]

/-- The selected natural iteration count satisfies the corrected physical condition-number refinement. -/
theorem secondOrderTailFree_iterationCount_conditionNumber (m M M2 p ε D : ℝ)
    (hm : 0<m) (hmM : m≤M) (hM2 : 0<M2) (hp : 1≤p) (hε : 0<ε) :
    (firstOrderIterationCount
      (m*secondOrderTailFreeStep m M (Real.sqrt (m+M)) M2 p ε/(4*Real.sqrt (m+M))) D
      (ε/Real.sqrt m):ℝ)<
      1+64*secondOrderRefinement (max (kineticConditionNumber m M)
        (sourceHessianConditionNumber m M M2 p)) p ε*
          max 0 (Real.log (24*D*Real.sqrt m/ε)) := by
  have hM : 0<M := hm.trans_le hmM
  have hc := secondOrderTailFree_iterationCount_lt m M (Real.sqrt (m+M)) M2 p ε D
    hm hM (by positivity) hM2 (by linarith) hε
  rw [secondOrderTailFreeInverse_normalized_work m M M2 p ε hm hM.le hε.ne'] at hc
  have hwork := secondOrderNormalizedWork_physical_bound m M M2 p ε hm hmM hM2.le hp hε
  exact hc.trans_le (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hwork (le_max_left (0:ℝ) (Real.log (24*D*Real.sqrt m/ε)))))

end KineticLangevin
