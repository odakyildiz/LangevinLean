import KineticLangevin.KineticSplittingConvergence
import KineticLangevin.LpDynamics

/-! # The actual L² splitting chain represents the vector splitting chain -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace KineticLangevin
section Noise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original splitting chain driven by an explicit sequence of filtered
velocity innovations. -/
def kineticSplitNoiseChain (g : E → E) (γ h : ℝ) (initial : E×E) (N : ℕ → E) : ℕ → E×E
  | 0 => initial
  | k+1 => kineticSplitStep g γ h (kineticSplitNoiseChain g γ h initial N k) (N k)

/-- The continuous-input chain uses precisely its explicit OU increments. -/
theorem kineticSplitChain_eq_noiseChain [CompleteSpace E] (g : E → E) (γ h : ℝ)
    (initial : E×E) (B : ℝ → E) (n : ℕ) :
    kineticSplitChain g γ h initial B n = kineticSplitNoiseChain g γ h initial
      (fun k ↦ ouInputIncrement γ B ((k : ℝ)*h) h) n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [kineticSplitChain,kineticSplitNoiseChain,ih]
end Noise

section Lp
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] (P : Measure Ω) [IsFiniteMeasure P]

/-- A lifted force kick is the actual pointwise vector kick almost everywhere. -/
theorem lp_kickStep_coe (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (h : ℝ) (S : Lp E 2 P × Lp E 2 P) :
    lpPhaseCoe P (kickStep (ULA.lpDrift P g hg) h S) =ᵐ[P]
      fun ω ↦ kickStep g h (lpPhaseCoe P S ω) := by
  filter_upwards [Lp.coeFn_sub S.1 (h • ULA.lpDrift P g hg S.2),
    Lp.coeFn_smul h (ULA.lpDrift P g hg S.2),ULA.lpDrift_coe P g hg S.2]
    with ω hsub hsm hgω
  simp only [Pi.sub_apply,Pi.smul_apply] at hsub hsm
  apply Prod.ext
  · change (S.1-h • ULA.lpDrift P g hg S.2 : Lp E 2 P) ω =
      S.1 ω-h • g (S.2 ω)
    rw [hsub,hsm,hgω]
  · rfl

/-- A lifted free drift is the actual pointwise vector drift almost everywhere. -/
theorem lp_driftStep_coe (h : ℝ) (S : Lp E 2 P × Lp E 2 P) :
    lpPhaseCoe P (driftStep h S) =ᵐ[P] fun ω ↦ driftStep h (lpPhaseCoe P S ω) := by
  filter_upwards [Lp.coeFn_add S.2 (h • S.1),Lp.coeFn_smul h S.1] with ω hadd hsm
  simp only [Pi.add_apply,Pi.smul_apply] at hadd hsm
  apply Prod.ext
  · rfl
  · change (S.2+h • S.1 : Lp E 2 P) ω = S.2 ω+h • S.1 ω
    rw [hadd,hsm]

/-- A lifted OU update retains exactly its pointwise supplied innovation. -/
theorem lp_ornsteinStep_coe (δ σ : ℝ) (Ξ : Lp E 2 P) (S : Lp E 2 P × Lp E 2 P) :
    lpPhaseCoe P (ornsteinStep δ σ Ξ S) =ᵐ[P]
      fun ω ↦ ornsteinStep δ σ (Ξ ω) (lpPhaseCoe P S ω) := by
  filter_upwards [Lp.coeFn_add (δ • S.1) (σ • Ξ),Lp.coeFn_smul δ S.1,
    Lp.coeFn_smul σ Ξ] with ω hadd hv hΞ
  simp only [Pi.add_apply,Pi.smul_apply] at hadd hv hΞ
  apply Prod.ext
  · change (δ • S.1+σ • Ξ : Lp E 2 P) ω = δ • S.1 ω+σ • Ξ ω
    rw [hadd,hv,hΞ]
  · rfl

/-- The lifted Hamiltonian Verlet map is the actual vector map. -/
theorem lp_verletStep_coe (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (h : ℝ) (S : Lp E 2 P × Lp E 2 P) :
    lpPhaseCoe P (verletStep (ULA.lpDrift P g hg) h S) =ᵐ[P]
      fun ω ↦ verletStep g h (lpPhaseCoe P S ω) := by
  let G := ULA.lpDrift P g hg
  filter_upwards [lp_kickStep_coe P g M hg (h/2) S,
    lp_driftStep_coe P h (kickStep G (h/2) S),
    lp_kickStep_coe P g M hg (h/2) (driftStep h (kickStep G (h/2) S))]
    with ω h1 h2 h3
  change lpPhaseCoe P (kickStep G (h/2) (driftStep h (kickStep G (h/2) S))) ω = _
  rw [h3,h2,h1]
  rfl

/-- The actual lifted Verlet--OU step represents the original pointwise step. -/
theorem lp_kineticSplitStep_coe (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (γ h : ℝ) (S : Lp E 2 P × Lp E 2 P) (N : Lp E 2 P) :
    lpPhaseCoe P (kineticSplitStep (ULA.lpDrift P g hg) γ h S N) =ᵐ[P]
      fun ω ↦ kineticSplitStep g γ h (lpPhaseCoe P S ω) (N ω) := by
  filter_upwards [lp_verletStep_coe P g M hg h S,
    lp_ornsteinStep_coe P (Real.exp (-γ*h)) 1 N (verletStep (ULA.lpDrift P g hg) h S)]
    with ω hV hO
  change lpPhaseCoe P (ornsteinStep (Real.exp (-γ*h)) 1 N
    (verletStep (ULA.lpDrift P g hg) h S)) ω = _
  rw [hO,hV]
  rfl

/-- Every lifted splitting iterate represents the original vector chain
with the same initial state and the same supplied innovations. -/
theorem lp_kineticSplitNoiseChain_coe (g : E → E) (M : ℝ≥0) (hg : LipschitzWith M g)
    (γ h : ℝ) (initial : Lp E 2 P × Lp E 2 P) (N : ℕ → Lp E 2 P) (n : ℕ) :
    lpPhaseCoe P (kineticSplitNoiseChain (ULA.lpDrift P g hg) γ h initial N n) =ᵐ[P]
      fun ω ↦ kineticSplitNoiseChain g γ h (lpPhaseCoe P initial ω) (fun k ↦ N k ω) n := by
  induction n with
  | zero => exact Eventually.of_forall fun _ ↦ rfl
  | succ n ih =>
      filter_upwards [ih,lp_kineticSplitStep_coe P g M hg γ h
        (kineticSplitNoiseChain (ULA.lpDrift P g hg) γ h initial N n) (N n)] with ω hp hs
      simpa only [kineticSplitNoiseChain,hp] using hs

end Lp
end KineticLangevin
