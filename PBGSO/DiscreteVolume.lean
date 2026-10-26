import PBGSO.Volume
import Mathlib.LinearAlgebra.Determinant

/-! # Signed Jacobian determinant of the actual frictionless B-A-B map

The force may be arbitrary differentiable; no joint potential is required.
The kick and drift Fréchet derivatives are actual triangular linear shears.
Their determinants are computed in a product basis, then the chain rule gives
the determinant one statement for the original `interwovenBAB` implementation.
-/

noncomputable section
namespace PBGSO
namespace DiscreteVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def upperShear (L : E →L[ℝ] E) : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.fst ℝ E E + L.comp (ContinuousLinearMap.snd ℝ E E)).prod
    (ContinuousLinearMap.snd ℝ E E)

def lowerShear (L : E →L[ℝ] E) : (E × E) →L[ℝ] (E × E) :=
  (ContinuousLinearMap.fst ℝ E E).prod
    (ContinuousLinearMap.snd ℝ E E + L.comp (ContinuousLinearMap.fst ℝ E E))

theorem upperShear_det (L : E →L[ℝ] E) : (upperShear L).det = 1 := by
  classical
  let b := Module.finBasis ℝ E
  change LinearMap.det _ = 1
  rw [← LinearMap.det_toMatrix (b.prod b)]
  have hm : LinearMap.toMatrix (b.prod b) (b.prod b) (upperShear L).toLinearMap =
      Matrix.fromBlocks 1 (LinearMap.toMatrix b b L.toLinearMap) 0 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [upperShear, LinearMap.toMatrix_apply, Module.Basis.prod_apply, Matrix.one_apply,
        Matrix.fromBlocks, Finsupp.single_apply, eq_comm]
  rw [hm, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem lowerShear_det (L : E →L[ℝ] E) : (lowerShear L).det = 1 := by
  classical
  let b := Module.finBasis ℝ E
  change LinearMap.det _ = 1
  rw [← LinearMap.det_toMatrix (b.prod b)]
  have hm : LinearMap.toMatrix (b.prod b) (b.prod b) (lowerShear L).toLinearMap =
      Matrix.fromBlocks 1 0 (LinearMap.toMatrix b b L.toLinearMap) 1 := by
    ext i j
    cases i <;> cases j <;>
      simp [lowerShear, LinearMap.toMatrix_apply, Module.Basis.prod_apply, Matrix.one_apply,
        Matrix.fromBlocks, Finsupp.single_apply, eq_comm]
  rw [hm, Matrix.det_fromBlocks_zero₁₂]
  simp

omit [FiniteDimensional ℝ E] in
/-- Actual force-kick derivative, with the signed force convention of the
implementation. -/
theorem kickStep_hasFDerivAt (F : E → E) (h : ℝ) (z : E × E)
    (hF : DifferentiableAt ℝ F z.2) :
    HasFDerivAt (KineticLangevin.kickStep F h)
      (upperShear (-(h • fderiv ℝ F z.2))) z := by
  have hs := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt (x := z)
  have hf := hF.hasFDerivAt.comp z hs
  have hd := ((ContinuousLinearMap.fst ℝ E E).hasFDerivAt (x := z).sub (hf.const_smul h)).prodMk hs
  convert hd using 1
  · rfl
  · ext v <;> simp [upperShear]

omit [FiniteDimensional ℝ E] in
/-- Actual position-drift derivative is the opposite triangular shear. -/
theorem driftStep_hasFDerivAt (h : ℝ) (z : E × E) :
    HasFDerivAt (KineticLangevin.driftStep h)
      (lowerShear (h • ContinuousLinearMap.id ℝ E)) z := by
  have hf := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt (x := z)
  have hs := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt (x := z)
  convert hf.prodMk (hs.add (hf.const_smul h)) using 1
  · rfl
  · ext v <;> simp [lowerShear]

/-- Signed Jacobian determinant of the actual force kick. -/
theorem kickStep_fderiv_det_one (F : E → E) (h : ℝ) (z : E × E)
    (hF : DifferentiableAt ℝ F z.2) :
    (fderiv ℝ (KineticLangevin.kickStep F h) z).det = 1 := by
  rw [(kickStep_hasFDerivAt F h z hF).fderiv]
  exact upperShear_det _

/-- Signed Jacobian determinant of the actual position drift. -/
theorem driftStep_fderiv_det_one (h : ℝ) (z : E × E) :
    (fderiv ℝ (KineticLangevin.driftStep h) z).det = 1 := by
  rw [(driftStep_hasFDerivAt h z).fderiv]
  exact lowerShear_det _

omit [FiniteDimensional ℝ E] in
/-- The determinant chain rule on the finite phase space. -/
theorem fderiv_det_comp (f g : E × E → E × E) (z : E × E)
    (hf : DifferentiableAt ℝ f (g z)) (hg : DifferentiableAt ℝ g z) :
    (fderiv ℝ (f ∘ g) z).det =
      (fderiv ℝ f (g z)).det * (fderiv ℝ g z).det := by
  rw [fderiv_comp z hf hg]
  change LinearMap.det (_ ∘ₗ _) = _
  exact LinearMap.det_comp _ _

/-- The full implemented frictionless B-A-B map has signed Jacobian
determinant exactly one for every step and initial state. Global force
differentiability suffices; no potential, C² force or assumed Jacobian identity
is required. -/
theorem verletStep_fderiv_det_one (F : E → E) (hF : Differentiable ℝ F)
    (h : ℝ) (z : E × E) :
    (fderiv ℝ (KineticLangevin.verletStep F h) z).det = 1 := by
  let k := KineticLangevin.kickStep F (h / 2)
  let d := KineticLangevin.driftStep (E := E) h
  have hk (x : E × E) : DifferentiableAt ℝ k x :=
    (kickStep_hasFDerivAt F (h / 2) x (hF _)).differentiableAt
  have hd (x : E × E) : DifferentiableAt ℝ d x :=
    (driftStep_hasFDerivAt h x).differentiableAt
  change (fderiv ℝ (k ∘ (d ∘ k)) z).det = 1
  rw [fderiv_det_comp k (d ∘ k) z (hk _) ((hd _).comp z (hk z)),
    fderiv_det_comp d k z (hd _) (hk z)]
  change (fderiv ℝ (KineticLangevin.kickStep F (h / 2)) _).det *
    ((fderiv ℝ (KineticLangevin.driftStep h) _).det *
      (fderiv ℝ (KineticLangevin.kickStep F (h / 2)) z).det) = 1
  rw [kickStep_fderiv_det_one F _ _ (hF _), driftStep_fderiv_det_one,
    kickStep_fderiv_det_one F _ _ (hF _)]
  norm_num

end DiscreteVolume

/-- The source's discrete signed-Jacobian assertion for the original
interwoven B-A-B implementation. -/
theorem interwovenBAB_fderiv_det_one
    {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]
    [CompleteSpace Q] [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q]
    [FiniteDimensional ℝ Q] (F : Q → Q) (hF : Differentiable ℝ F)
    (h : ℝ) (z : Q × Q) :
    (fderiv ℝ (interwovenBAB F h) z).det = 1 :=
  DiscreteVolume.verletStep_fderiv_det_one F hF h z

end PBGSO
