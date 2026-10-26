import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.MetricSpace.Isometry

/-! # Isometric extension from actual finite data to its literal closure -/
noncomputable section
set_option linter.unusedSectionVars false
open Set Filter
namespace PBGSO.ClosedIsometricExtension
variable {A H K : Type*} [MetricSpace H] [MetricSpace K] [CompleteSpace K]
  (f : A → H) (g : A → K)
  (hiso : ∀ a b, dist (g a) (g b) = dist (f a) (f b))

/-- The value on a represented finite input. Equal representations give
the same output because their actual output distance is zero. -/
def onRange (u : Set.range f) : K := g (Classical.choose u.property)

include hiso in
theorem onRange_isometry : Isometry (onRange f g) := by
  apply Isometry.of_dist_eq
  intro u v
  change dist (g (Classical.choose u.property)) (g (Classical.choose v.property)) = dist u.val v.val
  rw [hiso, Classical.choose_spec u.property, Classical.choose_spec v.property]

abbrev Domain := closure (Set.range f)

def inclusion : Set.range f → Domain f := Set.inclusion subset_closure

theorem inclusion_isometry : Isometry (inclusion f) := Isometry.of_dist_eq (fun _ _ => rfl)

theorem inclusion_dense : DenseRange (inclusion f) :=
  (denseRange_inclusion_iff subset_closure).mpr subset_rfl

/-- The actual isometric extension to the closure of represented inputs. -/
def extend : Domain f → K :=
  ((inclusion_isometry f).isUniformInducing.isDenseInducing (inclusion_dense f)).extend (onRange f g)

include hiso in
theorem extend_eq (u : Set.range f) : extend f g (inclusion f u) = onRange f g u :=
  uniformly_extend_of_ind (inclusion_isometry f).isUniformInducing (inclusion_dense f)
    (onRange_isometry f g hiso).uniformContinuous u

include hiso in
theorem extend_continuous : Continuous (extend f g) :=
  (uniformContinuous_uniformly_extend (inclusion_isometry f).isUniformInducing (inclusion_dense f)
    (onRange_isometry f g hiso).uniformContinuous).continuous

include hiso in
/-- The completion preserves exact distances; no norm or isometry premise
is imposed on the extension. -/
theorem extend_isometry : Isometry (extend f g) := by
  apply Isometry.of_dist_eq
  intro u v
  refine (inclusion_dense f).induction_on₂
    (p := fun u v => dist (extend f g u) (extend f g v) = dist u v)
    (isClosed_eq ((extend_continuous f g hiso).comp continuous_fst |>.dist
      ((extend_continuous f g hiso).comp continuous_snd))
      (continuous_fst.dist continuous_snd))
    (fun a b => ?_) u v
  rw [extend_eq f g hiso, extend_eq f g hiso]
  exact (onRange_isometry f g hiso).dist_eq a b

include hiso in
/-- Every convergent sequence of represented finite inputs has the
constructed output limit, independently of representation choices. -/
theorem tendsto_extend {ι : Type*} {l : Filter ι} (a : ι → A) (u : Domain f)
    (hu : Tendsto (fun i => f (a i)) l (nhds u.val)) :
    Tendsto (fun i => g (a i)) l (nhds (extend f g u)) := by
  have hsub : Tendsto (fun i => (⟨f (a i), subset_closure (mem_range_self _)⟩ : Domain f)) l (nhds u) :=
    tendsto_subtype_rng.mpr hu
  have hext := (extend_continuous f g hiso).continuousAt.tendsto.comp hsub
  apply hext.congr'
  apply Eventually.of_forall
  intro i
  have he := extend_eq f g hiso (⟨f (a i), mem_range_self _⟩ : Set.range f)
  change extend f g (inclusion f ⟨f (a i), mem_range_self _⟩) = g (a i)
  rw [he]
  apply dist_eq_zero.mp
  have hchosen : f (Classical.choose (⟨f (a i), mem_range_self _⟩ : Set.range f).property) = f (a i) :=
    Classical.choose_spec (⟨f (a i), mem_range_self _⟩ : Set.range f).property
  change dist (g (Classical.choose (⟨f (a i), mem_range_self _⟩ : Set.range f).property)) (g (a i)) = 0
  rw [hiso, hchosen, dist_self]

end PBGSO.ClosedIsometricExtension
