import KineticLangevin.LpHessian
import KineticLangevin.SplittingLaw

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace KineticLangevin
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] (P : Measure Ω) [IsFiniteMeasure P]

/-- Every scalar affine Hessian correction in the L² update has the original pointwise representative. -/
theorem affineHessian_lp_coe (a b c d : ℝ) (V G HV N HN : Lp E 2 P) :
    (a • V-b • G-c • HV+d • (N-HN) : Lp E 2 P) =ᵐ[P]
      fun ω => a • V ω-b • G ω-c • HV ω+d • (N ω-HN ω) := by
  filter_upwards [Lp.coeFn_add (a • V-b • G-c • HV) (d • (N-HN)),
    Lp.coeFn_sub (a • V-b • G) (c • HV),Lp.coeFn_sub (a • V) (b • G),
    Lp.coeFn_smul a V,Lp.coeFn_smul b G,Lp.coeFn_smul c HV,
    Lp.coeFn_smul d (N-HN),Lp.coeFn_sub N HN] with ω ha hs ht hv hg hhv hn hhn
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply] at ha hs ht hv hg hhv hn hhn
  rw [ha,hs,ht,hv,hg,hhv,hn,hhn]

/-- The actual random-Hessian L² update is precisely the original four-noise KLMC2 update. -/
theorem lp_klmc2Step_coe (g : E → E) (H : E → E →L[ℝ] E) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 H) (hg : ∀ x,HasFDerivAt g (H x) x)
    (γ h : ℝ) (S : Lp E 2 P × Lp E 2 P) (N : Fin 4 → Lp E 2 P) :
    lpPhaseCoe P (klmc2Step (ULA.lpDrift P g hG) (lpHessian P g H M M2 hG hH hg) γ h S N) =ᵐ[P]
      fun ω => klmc2Step g H γ h (lpPhaseCoe P S ω) (fun j => N j ω) := by
  let G := ULA.lpDrift P g hG
  let A := lpHessian P g H M M2 hG hH hg S.2
  let pv := psi γ 0 h • S.1-psi γ 1 h • G S.2-phi γ 2 h • A S.1+
    Real.sqrt (2*γ) • (N 0-A (N 2))
  let px := psi γ 1 h • S.1-psi γ 2 h • G S.2-phi γ 3 h • A S.1+
    Real.sqrt (2*γ) • (N 1-A (N 3))
  have hv := affineHessian_lp_coe P (psi γ 0 h) (psi γ 1 h) (phi γ 2 h) (Real.sqrt (2*γ))
    S.1 (G S.2) (A S.1) (N 0) (A (N 2))
  have hx := affineHessian_lp_coe P (psi γ 1 h) (psi γ 2 h) (phi γ 3 h) (Real.sqrt (2*γ))
    S.1 (G S.2) (A S.1) (N 1) (A (N 3))
  have hpos : (klmc2Step G (lpHessian P g H M M2 hG hH hg) γ h S N).2=S.2+px := by
    unfold klmc2Step px A
    abel
  filter_upwards [hv,hx,Lp.coeFn_add S.2 px,ULA.lpDrift_coe P g hG S.2,
    lpHessian_coe P g H M M2 hG hH hg S.2 S.1,
    lpHessian_coe P g H M M2 hG hH hg S.2 (N 2),
    lpHessian_coe P g H M M2 hG hH hg S.2 (N 3)] with ω hv hx hadd hGω hA hN2 hN3
  apply Prod.ext
  · change pv ω = _
    rw [hv,hGω,hA,hN2]
    rfl
  · change (klmc2Step G (lpHessian P g H M M2 hG hH hg) γ h S N).2 ω = _
    rw [hpos,hadd,Pi.add_apply,hx,hGω,hA,hN3]
    change S.2 ω + (_ - _ - _ + _) = _
    dsimp only [klmc2Step,lpPhaseCoe]
    abel

/-- Every actual L² second-order iterate represents the implemented vector chain on the same noise. -/
theorem lp_klmc2Chain_coe (g : E → E) (H : E → E →L[ℝ] E) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 H) (hg : ∀ x,HasFDerivAt g (H x) x)
    (γ h : ℝ) (S : Lp E 2 P × Lp E 2 P) (N : ℕ → Fin 4 → Lp E 2 P) (n : ℕ) :
    lpPhaseCoe P (klmc2Chain (ULA.lpDrift P g hG) (lpHessian P g H M M2 hG hH hg) γ h S N n) =ᵐ[P]
      fun ω => klmc2Chain g H γ h (lpPhaseCoe P S ω) (fun k j => N k j ω) n := by
  induction n with
  | zero => exact ae_of_all _ (fun _ => rfl)
  | succ n ih =>
    filter_upwards [ih,lp_klmc2Step_coe P g H M M2 hG hH hg γ h
      (klmc2Chain (ULA.lpDrift P g hG) (lpHessian P g H M M2 hG hH hg) γ h S N n) (N n)] with ω hi hs
    change lpPhaseCoe P (klmc2Step _ _ γ h (klmc2Chain _ _ γ h S N n) (N n)) ω = _
    rw [hs,hi]
    rfl

section Laws
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual Hessian-corrected vector update is jointly measurable in state and all four noises. -/
theorem klmc2Step_measurable (g : E → E) (H : E → E →L[ℝ] E)
    (hG : Continuous g) (hH : Continuous H) (γ h : ℝ) :
    Measurable (Function.uncurry (klmc2Step g H γ h)) := by
  apply Continuous.measurable
  unfold Function.uncurry klmc2Step
  fun_prop

/-- The implemented second-order chain is exactly the general random recursion with the same four-noise step. -/
theorem klmc2Chain_eq_noiseDrivenChain (g : E → E) (H : E → E →L[ℝ] E) (γ h : ℝ)
    (S : E×E) (N : ℕ → Fin 4 → E) (n : ℕ) :
    klmc2Chain g H γ h S N n=ULA.noiseDrivenChain (klmc2Step g H γ h) S N n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [klmc2Chain,ULA.noiseDrivenChain_succ,ih]

/-- A proved actual initial/four-noise-stream law determines the exact Markov law of every actual L² KLMC2 iterate. -/
theorem lp_klmc2Chain_law_of_jointLaw [IsProbabilityMeasure P]
    (g : E → E) (H : E → E →L[ℝ] E) (M M2 : ℝ≥0)
    (hG : LipschitzWith M g) (hH : LipschitzWith M2 H) (hg : ∀ x,HasFDerivAt g (H x) x)
    (γ h : ℝ) (S : Lp E 2 P × Lp E 2 P) (N : ℕ → Fin 4 → Lp E 2 P)
    (π : Measure (E×E)) [IsProbabilityMeasure π] (η : Measure (Fin 4 → E)) [IsProbabilityMeasure η]
    (hjoint : HasLaw (fun ω => (lpPhaseCoe P S ω,fun k j => N k j ω))
      (π.prod (Measure.infinitePi (fun _ : ℕ => η))) P) (n : ℕ) :
    P.map (lpPhaseCoe P (klmc2Chain (ULA.lpDrift P g hG) (lpHessian P g H M M2 hG hH hg) γ h S N n)) =
      ULA.markovLaws (klmc2Step g H γ h) η π n := by
  rw [Measure.map_congr (lp_klmc2Chain_coe P g H M M2 hG hH hg γ h S N n)]
  simp_rw [klmc2Chain_eq_noiseDrivenChain]
  exact noiseDrivenChain_law_of_jointLaw P (klmc2Step g H γ h)
    (klmc2Step_measurable g H hG.continuous hH.continuous γ h) π η _ _ hjoint n

end Laws
end KineticLangevin
