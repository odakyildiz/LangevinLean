import PBGSO.ConstantNoiseWork
import PBGSO.UniversalMomentGrowth
import PBGSO.MonotoneLocalBound
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Quadratic Dirac-optimizer growth from finite coupling work
This module makes the finite-work reading of the source condition explicit:
for each fixed optimizer pair, the signed sampler coupling work has quadratic
growth. Universal finite P₂ work integrability can supply that premise.
Dirac instances of source A3 then derive the weighted Dirac optimizer growth;
no optimizer continuity or Lipschitz gradient-response condition is assumed.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace InnerProductSpace
namespace PBGSO.DiracOptimizerGrowth
variable {S Θ Z X I : Type*}
  [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [MeasurableSpace Z] [MeasurableSingletonClass Z] [Fintype I]
  (M : Model S Θ Z X I) (D : TwistedGeometry S Z)

/-- Negative metric-weighted optimizer evaluated at one actual Dirac
observation, at the fixed source time zero. -/
def field (s : S) (z : Z) : S :=
  -D.optimizerWeight (M.optimizer 0 s (M.observation (M.parameter s) (M.position z)))

/-- Fixed optimizer-pair quadratic growth of the original signed sampler
work. This is an intermediate finite-integrability certificate, not an
assumed contraction or positive-work conclusion for a solution. -/
def WorkGrowth : Prop := ∀ s s' : S, ∃ C : ℝ, 0 ≤ C ∧ ∀ z w : Z,
  |samplerCouplingWork M D s s' (z,w)| ≤ C*(1+‖z‖ ^ 2+‖w‖ ^ 2)

variable (ρ : ℝ) (hρ : 0 ≤ ρ) (hmono : TwistedJointMonotonicity M D ρ)
include hρ hmono

/-- Actual one-point empirical laws yield the joint Dirac work inequality. -/
theorem dirac_work_le_zero (s s' : S) (z w : Z) :
    ⟪s-s',D.optimizerWeight
      (M.optimizer 0 s (M.observation (M.parameter s) (M.position z))-
       M.optimizer 0 s' (M.observation (M.parameter s') (M.position w)))⟫_ℝ +
      samplerCouplingWork M D s s' (z,w) ≤ 0 := by
  have h := particleCouplingWork_le M D ρ hmono 1 (by norm_num) 0 (by norm_num)
    s s' (fun _ => z) (fun _ => w)
  have hh : ⟪s-s',D.optimizerWeight
      (M.optimizer 0 s (M.observation (M.parameter s) (M.position z))-
       M.optimizer 0 s' (M.observation (M.parameter s') (M.position w)))⟫_ℝ +
      samplerCouplingWork M D s s' (z,w) ≤
      -ρ*(D.optimizerSq (s-s')+D.samplerSq (z-w)) := by
    simpa [particleCouplingWork,particleCouplingEnergy,Model.particleField,
      Model.particleGradient,Fin.sum_univ_one] using h
  exact hh.trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ)
    (add_nonneg (D.optimizerSq_nonneg _) (D.samplerSq_nonneg _)))

/-- Finite work at the two optimizer anchors s±v bounds the corresponding
component of the actual weighted Dirac optimizer field. -/
theorem component_growth (hwork : WorkGrowth M D) (s v : S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Z,
      |⟪v,field M D s z⟫_ℝ| ≤ C*(1+‖z‖ ^ 2) := by
  obtain ⟨Cp,hCp,hp⟩ := hwork s (s+v)
  obtain ⟨Cm,hCm,hm⟩ := hwork s (s-v)
  let Bp := |⟪v,field M D (s+v) 0⟫_ℝ|
  let Bm := |⟪v,field M D (s-v) 0⟫_ℝ|
  refine ⟨Cp+Cm+Bp+Bm,by dsimp [Bp,Bm]; positivity,?_⟩
  intro z
  have hpz := hp z 0
  have hmz := hm z 0
  norm_num at hpz hmz
  have hplus := dirac_work_le_zero M D ρ hρ hmono s (s+v) z 0
  have hminus := dirac_work_le_zero M D ρ hρ hmono s (s-v) z 0
  have hep : s-(s+v) = -v := by abel
  have hem : s-(s-v) = v := by abel
  rw [hep,map_sub,inner_neg_left,inner_sub_right] at hplus
  rw [hem,map_sub,inner_sub_right] at hminus
  have hfield (a : S) (w : Z) :
      ⟪v,field M D a w⟫_ℝ =
      -⟪v,D.optimizerWeight (M.optimizer 0 a (M.observation (M.parameter a) (M.position w)))⟫_ℝ := by
    simp only [field,inner_neg_right]
  have h_upper : ⟪v,field M D s z⟫_ℝ ≤ Cp*(1+‖z‖ ^ 2)+Bp := by
    have ha := neg_abs_le (samplerCouplingWork M D s (s+v) (z,0))
    have hb := le_abs_self ⟪v,field M D (s+v) 0⟫_ℝ
    dsimp only [Bp]
    simp only [hfield] at hb ⊢
    linarith
  have h_lower : -⟪v,field M D s z⟫_ℝ ≤ Cm*(1+‖z‖ ^ 2)+Bm := by
    have ha := neg_abs_le (samplerCouplingWork M D s (s-v) (z,0))
    have hb := neg_abs_le ⟪v,field M D (s-v) 0⟫_ℝ
    dsimp only [Bm]
    simp only [hfield] at hb ⊢
    linarith
  have hK : 1 ≤ 1+‖z‖ ^ 2 := le_add_of_nonneg_right (sq_nonneg _)
  have hBpn : 0 ≤ Bp := abs_nonneg _
  have hBmn : 0 ≤ Bm := abs_nonneg _
  apply abs_le.mpr
  constructor
  · have hrest : 0 ≤ Cp*(1+‖z‖ ^ 2)+Bp := by positivity
    have hBm := mul_le_mul_of_nonneg_left hK hBmn
    nlinarith
  · have hrest : 0 ≤ Cm*(1+‖z‖ ^ 2)+Bm := by positivity
    have hBp := mul_le_mul_of_nonneg_left hK hBpn
    nlinarith

/-- An actual finite orthonormal basis converts all proved directional
bounds into a norm bound for each fixed optimizer state. -/
theorem field_growth {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ S)
    (hwork : WorkGrowth M D) (s : S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Z, ‖field M D s z‖ ≤ C*(1+‖z‖ ^ 2) := by
  classical
  choose C hC hbound using fun i => component_growth M D ρ hρ hmono hwork s (b i)
  refine ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro z
  calc
    ‖field M D s z‖ = ‖∑ i, ⟪b i,field M D s z⟫_ℝ • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i, ‖⟪b i,field M D s z⟫_ℝ • b i‖ := norm_sum_le _ _
    _ = ∑ i, |⟪b i,field M D s z⟫_ℝ| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,b.orthonormal.norm_eq_one,mul_one,Real.norm_eq_abs]
    _ ≤ ∑ i, C i*(1+‖z‖ ^ 2) := Finset.sum_le_sum (fun i _ => hbound i z)
    _ = (∑ i, C i)*(1+‖z‖ ^ 2) := (Finset.sum_mul _ _ _).symm

/-- Explicit finite-integral reading of the source's universal P₂ sampler
work domain. The weight is exactly one plus the two second moments. -/
def FiniteCouplingWork : Prop := ∀ s s' (Λ : Measure (Z × Z)),
  IsProbabilityMeasure Λ → Integrable (fun p : Z × Z => 1+‖p.1‖ ^ 2+‖p.2‖ ^ 2) Λ →
    Integrable (samplerCouplingWork M D s s') Λ

omit hρ hmono in
/-- Universal finite P₂ work integrability actually derives the fixed-pair
quadratic work bound by the atomic probability argument. -/
theorem workGrowth_of_finiteCouplingWork (hfull : FiniteCouplingWork M D) : WorkGrowth M D := by
  intro s s'
  obtain ⟨C,hC,hb⟩ := UniversalMomentGrowth.growth_of_probability_integrability
    (fun p : Z × Z => 1+‖p.1‖ ^ 2+‖p.2‖ ^ 2)
    (fun p => by nlinarith [sq_nonneg ‖p.1‖,sq_nonneg ‖p.2‖])
    (samplerCouplingWork M D s s') (fun Λ hp hi => hfull s s' Λ hp hi)
  exact ⟨C,hC,fun z w => by simpa only [Real.norm_eq_abs] using hb (z,w)⟩

/-- For each fixed sampler point the weighted Dirac optimizer is an
actual everywhere-defined monotone finite-dimensional field. -/
theorem field_monotone (z : Z) (s s' : S) :
    0 ≤ ⟪s-s',field M D s z-field M D s' z⟫_ℝ := by
  have h := dirac_work_le_zero M D ρ hρ hmono s s' z z
  have hn : 0 ≤ samplerCouplingWork M D s s' (z,z) := by
    simp only [samplerCouplingWork,sub_self,inner_zero_left,zero_add]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => D.samplerSq_nonneg _))
  dsimp only [field]
  rw [inner_sub_right,inner_neg_right,inner_neg_right]
  rw [map_sub,inner_sub_right] at h
  linarith

/-- In finite optimizer dimension, the explicit universal finite-work
interpretation of A3 derives fixed-state quadratic Dirac response growth. -/
theorem field_growth_of_finiteCouplingWork [FiniteDimensional ℝ S]
    (hfull : FiniteCouplingWork M D) (s : S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Z, ‖field M D s z‖ ≤ C*(1+‖z‖ ^ 2) :=
  field_growth M D ρ hρ hmono (stdOrthonormalBasis ℝ S)
    (workGrowth_of_finiteCouplingWork M D hfull) s

/-- Monotonicity in the optimizer and its proved fixed-state growth make
that quadratic bound uniform on every actual compact optimizer set. -/
theorem field_growth_on_compact [FiniteDimensional ℝ S]
    (hfull : FiniteCouplingWork M D) (K : Set S) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ z : Z,
      ‖field M D s z‖ ≤ C*(1+‖z‖ ^ 2) := by
  exact MonotoneLocalBound.uniform_growth_on_compact
    (fun z s => field M D s z) (fun z => 1+‖z‖ ^ 2)
    (fun z => by positivity)
    (fun z s s' => field_monotone M D ρ hρ hmono z s s')
    (fun s => field_growth_of_finiteCouplingWork M D ρ hρ hmono hfull s) K hK

/-- At the fixed time zero, Dirac A3 and the proved compact quadratic
response bound give a uniform positive SAMPLER-work bound. Since sampler
coefficients have no time argument, it holds along any optimizer schedule.
The finite-work reading of A3 is explicit; no response Lipschitz condition
or continuity has been inserted. -/
theorem positive_sampler_work_growth_on_compact [FiniteDimensional ℝ S]
    (hfull : FiniteCouplingWork M D) (K : Set S) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ s' ∈ K, ∀ z w : Z,
      max (samplerCouplingWork M D s s' (z,w)) 0 ≤ C*(1+‖z‖ ^ 2+‖w‖ ^ 2) := by
  obtain ⟨C,hC,hfield⟩ := field_growth_on_compact M D ρ hρ hmono hfull K hK
  obtain ⟨R0,hR0⟩ := hK.exists_bound_of_continuousOn (continuous_id.continuousOn : ContinuousOn (fun s : S => s) K)
  let R := max 0 R0
  have hR : 0 ≤ R := le_max_left _ _
  have hbound (s : S) (hs : s ∈ K) : ‖s‖ ≤ R := (hR0 s hs).trans (le_max_right _ _)
  refine ⟨4*R*C,by positivity,?_⟩
  intro s hs s' hs' z w
  have hδ : ‖s-s'‖ ≤ 2*R := (norm_sub_le s s').trans (by linarith [hbound s hs,hbound s' hs'])
  have ha : ‖field M D s z-field M D s' w‖ ≤ C*(2+‖z‖ ^ 2+‖w‖ ^ 2) := by
    apply (norm_sub_le _ _).trans
    have hsum := add_le_add (hfield s hs z) (hfield s' hs' w)
    convert hsum using 1 <;> ring
  have hd := dirac_work_le_zero M D ρ hρ hmono s s' z w
  have he : ⟪s-s',D.optimizerWeight
      (M.optimizer 0 s (M.observation (M.parameter s) (M.position z))-
       M.optimizer 0 s' (M.observation (M.parameter s') (M.position w)))⟫_ℝ =
      -⟪s-s',field M D s z-field M D s' w⟫_ℝ := by
    simp only [field,map_sub,inner_sub_right,inner_neg_right]
    ring
  rw [he] at hd
  apply max_le
  · calc
      samplerCouplingWork M D s s' (z,w) ≤ ⟪s-s',field M D s z-field M D s' w⟫_ℝ := by linarith
      _ ≤ ‖s-s'‖ * ‖field M D s z-field M D s' w‖ := real_inner_le_norm _ _
      _ ≤ (2*R)*(C*(2+‖z‖ ^ 2+‖w‖ ^ 2)) :=
        mul_le_mul hδ ha (norm_nonneg _) (by positivity)
      _ ≤ (2*R)*(C*(2*(1+‖z‖ ^ 2+‖w‖ ^ 2))) := by
        gcongr
        nlinarith [sq_nonneg ‖z‖,sq_nonneg ‖w‖]
      _ = (4*R*C)*(1+‖z‖ ^ 2+‖w‖ ^ 2) := by ring
  · positivity

end PBGSO.DiracOptimizerGrowth
