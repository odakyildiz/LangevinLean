import PBGSO.DiracOptimizerGrowth
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! # Primitive joint monotonicity bounds frozen drift anchors and energy
The entire weighted Dirac field is monotone in the actual Euclidean product
Hilbert space. Finite-dimensional local boundedness gives a uniform drift
anchor bound on optimizer compact sets; frozen dissipativity then derives a
constant radial energy bound. Neither drift-norm growth nor universal finite
work integrability is required for these moment prerequisites.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.DiracSamplerCoercivity
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z] [Fintype I]
  (M : Model S Θ Z X I) (D : TwistedGeometry S Z)

/-- The actual weighted full Dirac field, on the L² product Hilbert norm. -/
def fullField (x : WithLp 2 (S × Z)) : WithLp 2 (S × Z) :=
  WithLp.toLp 2 (DiracOptimizerGrowth.field M D x.ofLp.1 x.ofLp.2,
    -D.samplerWeight (M.drift (M.parameter x.ofLp.1) x.ofLp.2))

variable (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
include hρ hmono

/-- Source A3 on one-point empirical laws proves actual full-field
monotonicity. The nonnegative diffusion correction may be discarded. -/
theorem fullField_monotone (x y : WithLp 2 (S × Z)) :
    0 ≤ ⟪x-y,fullField M D x-fullField M D y⟫_ℝ := by
  have h := DiracOptimizerGrowth.dirac_work_le_zero M D ρ hρ hmono
    x.ofLp.1 y.ofLp.1 x.ofLp.2 y.ofLp.2
  have hn : 0 ≤ (1/2 : ℝ)*∑ i,
      D.samplerSq (M.diffusion (M.parameter x.ofLp.1) x.ofLp.2 i-
        M.diffusion (M.parameter y.ofLp.1) y.ofLp.2 i) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => D.samplerSq_nonneg _))
  rw [samplerCouplingWork] at h
  simp only [WithLp.prod_inner_apply,WithLp.ofLp_sub,Prod.fst_sub,Prod.snd_sub,
    fullField,WithLp.ofLp_toLp,DiracOptimizerGrowth.field,
    inner_sub_right,inner_neg_right,map_sub] at ⊢
  simp only [Prod.fst,Prod.snd,map_sub,inner_sub_right] at h
  linarith

/-- The actual weighted frozen drift at z=0 is uniformly bounded on every
optimizer compact set, derived solely from full Dirac monotonicity. -/
theorem drift_anchor_bound [FiniteDimensional ℝ S] [FiniteDimensional ℝ Z]
    (K : Set S) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ K, ‖D.samplerWeight (M.drift (M.parameter s) 0)‖ ≤ B := by
  let C : Set (WithLp 2 (S × Z)) := (fun s : S => WithLp.toLp 2 (s,(0 : Z))) '' K
  have hC : IsCompact C := hK.image (by fun_prop)
  obtain ⟨B,hB,hbound⟩ := MonotoneLocalBound.uniform_growth_on_compact
    (fun _ : Unit => fullField M D) (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (fun _ x y => fullField_monotone M D ρ hρ hmono x y)
    (fun x => ⟨‖fullField M D x‖,norm_nonneg _,fun _ => le_of_eq (mul_one _).symm⟩) C hC
  refine ⟨B,hB,?_⟩
  intro s hs
  have hh := hbound (WithLp.toLp 2 (s,(0 : Z))) ⟨s,hs,rfl⟩ ()
  have he := WithLp.norm_snd_le (p := (2 : ENNReal)) (α := S) (β := Z) (fullField M D (WithLp.toLp 2 (s,(0 : Z))))
  simpa only [fullField,WithLp.ofLp_toLp,WithLp.snd,norm_neg,mul_one] using he.trans hh

/-- Positive source dissipation and the proved compact drift-anchor bound
yield a uniform constant radial-energy ceiling, despite superlinear drift
norms. This is the primitive hypothesis needed by stopped moment/Fatou. -/
theorem radial_coercivity_on_compact [FiniteDimensional ℝ S] [FiniteDimensional ℝ Z]
    (hρpos : 0 < ρ) (K : Set S) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ z : Z,
      ⟪z,D.samplerWeight (M.drift (M.parameter s) z)⟫_ℝ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := drift_anchor_bound M D ρ hρ hmono K hK
  let ε := ρ*D.lower
  have hε : 0 < ε := mul_pos hρpos D.lower_pos
  let C := B ^ 2/ε
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) hε.le
  have heC : ε*C = B ^ 2 := by dsimp only [C]; field_simp
  refine ⟨C,hC,?_⟩
  intro s hs z
  have hf := ConstantNoiseWork.frozen_drift_le M D ρ hmono s z 0
  simp only [sub_zero,TwistedGeometry.samplerSq] at hf
  have hl := D.sampler_lower z
  have hlow := mul_le_mul_of_nonneg_left hl hρ
  have ha := real_inner_le_norm z (D.samplerWeight (M.drift (M.parameter s) 0))
  have hb : ⟪z,D.samplerWeight (M.drift (M.parameter s) 0)⟫_ℝ ≤ ‖z‖*B :=
    ha.trans (mul_le_mul_of_nonneg_left (hbound s hs) (norm_nonneg _))
  rw [map_sub,inner_sub_right] at hf
  have hq : ⟪z,D.samplerWeight (M.drift (M.parameter s) z)⟫_ℝ ≤ -ε*‖z‖ ^ 2+‖z‖*B := by
    dsimp only [ε]
    nlinarith
  apply (mul_le_mul_iff_of_pos_left hε).mp
  rw [heC]
  have hh := mul_le_mul_of_nonneg_left hq hε.le
  nlinarith [sq_nonneg (ε*‖z‖-B)]

end PBGSO.DiracSamplerCoercivity
