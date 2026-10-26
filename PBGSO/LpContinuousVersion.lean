import PBGSO.LpJointRepresentative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Simultaneous continuous versions of actual additive integral processes

A joint L¹ drift representative is constructed, then its literal pathwise
primitive supplies one process version at every time. Continuity of the actual
raw additive input is explicit; a merely pre-Brownian Driver does not assert
sample-path continuity. The nonlinear drift equation is transferred using
joint measurability and Fubini, not a separate equation at each exceptional set.
-/
noncomputable section
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace PBGSO.LpContinuousVersion
variable {Ω R : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  (Q : Measure Ω) [IsProbabilityMeasure Q]

def primitive (g : ℝ → Ω → R) (t : ℝ) (ω : Ω) : R := ∫ s in Ioc 0 t, g s ω

theorem primitive_stronglyMeasurable (g : ℝ → Ω → R)
    (hg : StronglyMeasurable (Function.uncurry g)) :
    StronglyMeasurable (Function.uncurry (primitive g)) := by
  let K : (ℝ × Ω) × ℝ → R :=
    ({p | 0 < p.2 ∧ p.2 ≤ p.1.1} : Set ((ℝ × Ω) × ℝ)).indicator
      (fun p => g p.2 p.1.2)
  have hset : MeasurableSet ({p | 0 < p.2 ∧ p.2 ≤ p.1.1} : Set ((ℝ × Ω) × ℝ)) := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
  have hK : StronglyMeasurable K :=
    (hg.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).indicator hset
  have hi := hK.integral_prod_right' (ν := (volume : Measure ℝ))
  convert hi using 1
  funext p
  change (∫ s in Ioc 0 p.1, g s p.2) = ∫ s, K (p, s)
  rw [← integral_indicator measurableSet_Ioc]
  congr 1

theorem primitive_continuousOn (g : ℝ → Ω → R) (T : ℝ) (_hT : 0 ≤ T)
    (ω : Ω) (hi : IntegrableOn (fun s => g s ω) (Icc 0 T)) :
    ContinuousOn (fun t => primitive g t ω) (Icc 0 T) := by
  exact intervalIntegral.continuousOn_primitive hi

/-- Construct one jointly strongly measurable continuous path version of an
actual L² integral process, with its literal original nonlinear drift equation.
All pathwise assertions hold on one spatial full-measure set for every time in
the finite horizon. -/
theorem exists_continuous_integral_version
    (T : ℝ) (hT : 0 ≤ T) (Y F B : ℝ → Lp R 2 Q)
    (hF : IntegrableOn F (Icc 0 T))
    (b : ℝ → Ω → R) (hb : StronglyMeasurable (Function.uncurry b))
    (hbEq : ∀ t ∈ Icc 0 T, b t =ᵐ[Q] B t)
    (hbCont : ∀ᵐ ω ∂Q, ContinuousOn (fun t => b t ω) (Icc 0 T))
    (f : ℝ → R → R) (hf : Continuous (Function.uncurry f))
    (hfield : ∀ t ∈ Icc 0 T, F t =ᵐ[Q] (fun ω => f t (Y t ω)))
    (heq : ∀ t ∈ Icc 0 T, Y t - Y 0 = (∫ s in 0..t, F s) + B t) :
    ∃ u : ℝ → Ω → R,
      StronglyMeasurable (Function.uncurry u) ∧
      (∀ t ∈ Icc 0 T, u t =ᵐ[Q] Y t) ∧
      ∀ᵐ ω ∂Q,
        ContinuousOn (fun t => u t ω) (Icc 0 T) ∧
        u 0 ω = Y 0 ω ∧
        ∀ t ∈ Icc 0 T,
          u t ω - u 0 ω = (∫ s in 0..t, f s (u s ω)) + b t ω := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let g : ℝ → Ω → R := LpJointRepresentative.jointRepresentative μ Q F hF
  have hg : StronglyMeasurable (Function.uncurry g) :=
    LpJointRepresentative.jointRepresentative_stronglyMeasurable μ Q F hF
  have hgi : Integrable (Function.uncurry g) (μ.prod Q) :=
    LpJointRepresentative.jointRepresentative_integrable μ Q F hF
  have hgs : ∀ᵐ t ∂μ, g t =ᵐ[Q] F t :=
    LpJointRepresentative.jointRepresentative_section μ Q F hF
  let u : ℝ → Ω → R := fun t ω => Y 0 ω + primitive g t ω + b t ω
  have hu : StronglyMeasurable (Function.uncurry u) :=
    ((Lp.stronglyMeasurable (Y 0)).comp_snd.add (primitive_stronglyMeasurable g hg)).add hb
  have hurep (t : ℝ) (ht : t ∈ Icc 0 T) : u t =ᵐ[Q] Y t := by
    have hsub : Ioc 0 t ⊆ Icc 0 T := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
    have hi := LpJointRepresentative.jointRepresentative_setIntegral μ Q F hF (Ioc 0 t)
    rw [Measure.restrict_restrict_of_subset hsub] at hi
    have he := heq t ht
    rw [intervalIntegral.integral_of_le ht.1] at he
    filter_upwards [hi, hbEq t ht, Lp.coeFn_sub (Y t) (Y 0),
      Lp.coeFn_add (∫ s in Ioc 0 t, F s) (B t)] with ω hω hbω hYω hBω
    have heω := congrArg (fun V : Lp R 2 Q => V ω) he
    rw [hYω, hBω] at heω
    simp only [Pi.sub_apply, Pi.add_apply] at heω
    change (∫ s in Ioc 0 t, F s) ω = ∫ s in Ioc 0 t, g s ω at hω
    rw [hω] at heω
    dsimp [u, primitive]
    rw [hbω]
    calc
      Y 0 ω + (∫ s in Ioc 0 t, g s ω) + B t ω =
          ((∫ s in Ioc 0 t, g s ω) + B t ω) + Y 0 ω := by abel
      _ = Y t ω := (eq_add_of_sub_eq heω).symm
  have hcomp : StronglyMeasurable (fun p : ℝ × Ω => f p.1 (u p.1 p.2)) :=
    hf.comp_stronglyMeasurable (measurable_fst.stronglyMeasurable.prodMk hu)
  have hprod : (Function.uncurry g) =ᵐ[μ.prod Q]
      (fun p => f p.1 (u p.1 p.2)) := by
    apply (Measure.ae_prod_iff_ae_ae (hg.measurableSet_eq_fun hcomp)).mpr
    filter_upwards [hgs, ae_restrict_mem measurableSet_Icc] with t ht hti
    exact ht.trans ((hfield t hti).trans ((hurep t hti).symm.fun_comp (f t)))
  have hpath : ∀ᵐ ω ∂Q, ∀ᵐ s ∂μ, g s ω = f s (u s ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := Q) (ν := μ)).quasiMeasurePreserving.ae_eq_comp hprod)
  have hzero : B 0 = 0 := by
    have hh := heq 0 ⟨le_rfl, hT⟩
    simpa only [sub_self, intervalIntegral.integral_same, zero_add] using hh.symm
  have hbzero : b 0 =ᵐ[Q] (fun _ => 0) := by
    have hh := hbEq 0 ⟨le_rfl, hT⟩
    rw [hzero] at hh
    exact hh.trans (Lp.coeFn_zero R 2 Q)
  refine ⟨u, hu, hurep, ?_⟩
  filter_upwards [hgi.prod_left_ae, hbCont, hpath, hbzero] with ω hi hc hp hz
  have hcU : ContinuousOn (fun t => u t ω) (Icc 0 T) :=
    (continuousOn_const.add (primitive_continuousOn g T hT ω hi)).add hc
  have hu0 : u 0 ω = Y 0 ω := by simp [u, primitive, hz]
  refine ⟨hcU, hu0, ?_⟩
  intro t ht
  have hsub : Ioc 0 t ⊆ Icc 0 T := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hpeq : (fun s => g s ω) =ᵐ[volume.restrict (Ioc 0 t)] (fun s => f s (u s ω)) :=
    hp.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub))
  rw [intervalIntegral.integral_of_le ht.1, ← integral_congr_ae hpeq, hu0]
  dsimp [u, primitive]
  abel
end PBGSO.LpContinuousVersion
