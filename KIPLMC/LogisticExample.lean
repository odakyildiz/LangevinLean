import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Strong
import Mathlib.Tactic

noncomputable section
open Set
open scoped RealInnerProductSpace NNReal
namespace KIPLMC.LogisticExample

/-- One Bernoulli negative log likelihood, up to the choice of response y∈{0,1}. -/
def logisticLoss (y u : ℝ) : ℝ := Real.log (1+Real.exp u)-y*u

theorem sigmoid_exp_ratio (u : ℝ) : Real.sigmoid u=Real.exp u/(1+Real.exp u) := by
  rw [Real.sigmoid_def,Real.exp_neg]
  field_simp
  ring

/-- The exact score of the source logistic likelihood. -/
theorem hasDerivAt_logisticLoss (y u : ℝ) :
    HasDerivAt (logisticLoss y) (Real.sigmoid u-y) u := by
  have hd := (((Real.hasDerivAt_exp u).const_add 1).log (by positivity)).sub
    ((hasDerivAt_id u).const_mul y)
  convert hd using 1
  · rfl
  · rw [sigmoid_exp_ratio]
    simp only [mul_one]

/-- The logistic likelihood curvature. -/
def logisticWeight (u : ℝ) : ℝ := Real.sigmoid u*(1-Real.sigmoid u)

theorem logisticWeight_pos (u : ℝ) : 0<logisticWeight u :=
  mul_pos (Real.sigmoid_pos u) (sub_pos.mpr (Real.sigmoid_lt_one u))

theorem logisticWeight_le_quarter (u : ℝ) : logisticWeight u≤1/4 := by
  unfold logisticWeight
  nlinarith [sq_nonneg (Real.sigmoid u-1/2)]

/-- The exact global 1/4 Lipschitz constant used by the source gradient bound. -/
theorem sigmoid_lipschitz : LipschitzWith (1/4 : ℝ≥0) Real.sigmoid := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun u ↦ (Real.hasDerivAt_sigmoid u).differentiableAt)
  intro u
  rw [(Real.hasDerivAt_sigmoid u).deriv]
  change |logisticWeight u|≤(1/4 : ℝ)
  rw [abs_of_pos (logisticWeight_pos u)]
  exact logisticWeight_le_quarter u

variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype J]

/-- The joint Gaussian location prior and logistic observation potential; tau=σ⁻². -/
def potential (tau : ℝ) (v : J→E) (y : J→ℝ) (z : E×E) : ℝ :=
  tau/2*‖z.2-z.1‖^2+∑ j,logisticLoss (y j) ⟪v j,z.2⟫

/-- The exact second variation of the joint potential along direction (u,w). -/
def curvature (tau : ℝ) (v : J→E) (x u w : E) : ℝ :=
  tau*‖w-u‖^2+∑ j,logisticWeight ⟪v j,x⟫*⟪v j,w⟫^2

/-- The score along an arbitrary affine line through the joint parameter/latent state. -/
def lineScore (tau : ℝ) (v : J→E) (y : J→ℝ) (z d : E×E) (t : ℝ) : ℝ :=
  tau*⟪(z.2+t • d.2)-(z.1+t • d.1),d.2-d.1⟫+
    ∑ j,(Real.sigmoid ⟪v j,z.2+t • d.2⟫-y j)*⟪v j,d.2⟫

/-- Every score and Hessian expression is derived from the actual model potential. -/
theorem potential_line_derivative (tau : ℝ) (v : J→E) (y : J→ℝ) (z d : E×E) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ potential tau v y (z+t • d)) (lineScore tau v y z d t) t := by
  have hx := (hasDerivAt_const t z.2).add ((hasDerivAt_id t).smul_const d.2)
  have hθ := (hasDerivAt_const t z.1).add ((hasDerivAt_id t).smul_const d.1)
  have hprior := ((hx.sub hθ).norm_sq).const_mul (tau/2)
  have hsum := HasDerivAt.sum (u:=Finset.univ) (fun j _ ↦
    (hasDerivAt_logisticLoss (y j) ⟪v j,z.2+t • d.2⟫).comp t
      ((hasDerivAt_const t (v j)).inner ℝ hx))
  convert hprior.add hsum using 1
  · funext s
    simp [potential,Function.comp_def]
  · simp only [lineScore,id_eq,Pi.add_apply,Pi.sub_apply,one_smul,zero_add,
      inner_zero_left,add_zero]
    ring

/-- The displayed block Hessian quadratic form is the true derivative of the line score. -/
theorem lineScore_derivative (tau : ℝ) (v : J→E) (y : J→ℝ) (z d : E×E) (t : ℝ) :
    HasDerivAt (lineScore tau v y z d) (curvature tau v (z.2+t • d.2) d.1 d.2) t := by
  have hx := (hasDerivAt_const t z.2).add ((hasDerivAt_id t).smul_const d.2)
  have hθ := (hasDerivAt_const t z.1).add ((hasDerivAt_id t).smul_const d.1)
  have hprior := (((hx.sub hθ).inner ℝ (hasDerivAt_const t (d.2-d.1))).const_mul tau)
  have hsum := HasDerivAt.sum (u:=Finset.univ) (fun j _ ↦
    (((Real.hasDerivAt_sigmoid ⟪v j,z.2+t • d.2⟫).comp t
      ((hasDerivAt_const t (v j)).inner ℝ hx)).sub_const (y j)).mul_const ⟪v j,d.2⟫)
  convert hprior.add hsum using 1
  · funext s
    simp [lineScore]
  · simp only [curvature,logisticWeight,Pi.add_apply,Pi.sub_apply,one_smul,
      zero_add,inner_zero_left,inner_zero_right,add_zero,real_inner_self_eq_norm_sq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The Gaussian prior and observation Hessian are positive semidefinite. -/
theorem curvature_nonneg (tau : ℝ) (htau : 0≤tau) (v : J→E) (x u w : E) :
    0≤curvature tau v x u w :=
  add_nonneg (mul_nonneg htau (sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (logisticWeight_pos _).le (sq_nonneg _)))

/-- Exactly the directions invisible to both prior and observations have zero second variation. -/
theorem curvature_eq_zero_iff (tau : ℝ) (htau : 0<tau) (v : J→E) (x u w : E) :
    curvature tau v x u w=0 ↔ u=w ∧ ∀ j,⟪v j,w⟫=0 := by
  have hsum : 0≤∑ j,logisticWeight ⟪v j,x⟫*⟪v j,w⟫^2 :=
    Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (logisticWeight_pos _).le (sq_nonneg _))
  constructor
  · intro hz
    have hnorm : ‖w-u‖^2=0 := by
      unfold curvature at hz
      nlinarith [sq_nonneg ‖w-u‖]
    have hwu : w=u := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
    refine ⟨hwu.symm,?_⟩
    intro j
    have hj : logisticWeight ⟪v j,x⟫*⟪v j,w⟫^2≤∑ j,logisticWeight ⟪v j,x⟫*⟪v j,w⟫^2 :=
      Finset.single_le_sum (fun (i : J) _ ↦ mul_nonneg (logisticWeight_pos ⟪v i,x⟫).le (sq_nonneg ⟪v i,w⟫)) (Finset.mem_univ j)
    unfold curvature at hz
    have hs : ⟪v j,w⟫^2=0 := by nlinarith [logisticWeight_pos ⟪v j,x⟫,sq_nonneg ⟪v j,w⟫]
    exact sq_eq_zero_iff.mp hs
  · rintro ⟨rfl,hw⟩
    simp [curvature,hw]

/-- Convexity is a global property of the exact joint potential, without a rank assumption. -/
theorem potential_convex (tau : ℝ) (htau : 0≤tau) (v : J→E) (y : J→ℝ) :
    ConvexOn ℝ Set.univ (potential tau v y) := by
  refine ⟨convex_univ,?_⟩
  intro z _ z' _ a b ha hb hab
  let F : ℝ→ℝ := fun t ↦ potential tau v y (z+t • (z'-z))
  have hD : deriv F=lineScore tau v y z (z'-z) :=
    funext (fun t ↦ (potential_line_derivative tau v y z (z'-z) t).deriv)
  have hDD : deriv (deriv F)=fun t ↦ curvature tau v (z.2+t • (z'-z).2) (z'-z).1 (z'-z).2 := by
    rw [hD]
    exact funext (fun t ↦ (lineScore_derivative tau v y z (z'-z) t).deriv)
  have hconv : ConvexOn ℝ Set.univ F := convexOn_univ_of_deriv2_nonneg
    (fun t ↦ (potential_line_derivative tau v y z (z'-z) t).differentiableAt)
    (by rw [hD]; exact fun t ↦ (lineScore_derivative tau v y z (z'-z) t).differentiableAt)
    (fun (t : ℝ) ↦ by simpa only [Function.iterate_succ_apply',Function.iterate_zero_apply,hDD] using
      curvature_nonneg tau htau v (z.2+t • (z'-z).2) (z'-z).1 (z'-z).2)
  have hv := hconv.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ)) ha hb hab
  have he : z+b • (z'-z)=a • z+b • z' := by
    calc z+b • (z'-z)=(a+b) • z+b • (z'-z) := by rw [hab,one_smul]
         _=a • z+b • z' := by module
  simpa [F,he] using hv

/-- Full span of the covariates removes precisely the nullspace in the Hessian. -/
theorem curvature_pos_of_span (tau : ℝ) (htau : 0<tau) (v : J→E)
    (hspan : Submodule.span ℝ (Set.range v)=⊤) (x u w : E) (hd : (u,w)≠0) :
    0<curvature tau v x u w := by
  refine lt_of_le_of_ne (curvature_nonneg tau htau.le v x u w) ?_
  intro hz
  obtain ⟨huw,hw⟩ := (curvature_eq_zero_iff tau htau v x u w).mp hz.symm
  have hall : ∀ a∈Submodule.span ℝ (Set.range v),⟪a,w⟫=0 := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha => obtain ⟨j,rfl⟩:=ha; exact hw j
    | zero => simp
    | add a b ha hb iha ihb => simp [inner_add_left,iha,ihb]
    | smul r a ha ih => simp [inner_smul_left,ih]
  have hww := hall w (by rw [hspan]; trivial)
  have hw0 : w=0 := inner_self_eq_zero.mp hww
  exact hd (by simp [huw,hw0])

/-- The rank condition from the experimental model yields strict convexity of the whole joint potential. -/
theorem potential_strictConvex_of_span (tau : ℝ) (htau : 0<tau) (v : J→E) (y : J→ℝ)
    (hspan : Submodule.span ℝ (Set.range v)=⊤) :
    StrictConvexOn ℝ Set.univ (potential tau v y) := by
  refine ⟨convex_univ,?_⟩
  intro z _ z' _ hzz a b ha hb hab
  let F : ℝ→ℝ := fun t ↦ potential tau v y (z+t • (z'-z))
  have hD : deriv F=lineScore tau v y z (z'-z) :=
    funext (fun t ↦ (potential_line_derivative tau v y z (z'-z) t).deriv)
  have hDD : deriv (deriv F)=fun t ↦ curvature tau v (z.2+t • (z'-z).2) (z'-z).1 (z'-z).2 := by
    rw [hD]
    exact funext (fun t ↦ (lineScore_derivative tau v y z (z'-z) t).deriv)
  have hconv : StrictConvexOn ℝ Set.univ F := strictConvexOn_univ_of_deriv2_pos
    (show Differentiable ℝ F from fun t ↦ (potential_line_derivative tau v y z (z'-z) t).differentiableAt).continuous
    (by
      intro t
      change 0 < deriv (deriv F) t
      rw [hDD]
      exact curvature_pos_of_span tau htau v hspan (z.2+t • (z'-z).2) (z'-z).1 (z'-z).2
        (by change z'-z ≠ 0; exact sub_ne_zero.mpr hzz.symm))
  have hv := hconv.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (1:ℝ)) (by norm_num) ha hb hab
  have he : z+b • (z'-z)=a • z+b • z' := by
    calc z+b • (z'-z)=(a+b) • z+b • (z'-z) := by rw [hab,one_smul]
         _=a • z+b • z' := by module
  simpa [F,he] using hv

/-- Joint states use the Euclidean product norm, as required by the paper. -/
abbrev Joint (E : Type*) := WithLp 2 (E×E)

/-- The original potential transported to the Euclidean product. -/
def jointPotential (tau : ℝ) (v : J→E) (y : J→ℝ) (z : Joint E) : ℝ :=
  potential tau v y (WithLp.ofLp z)

/-- Both displayed gradient blocks, with the common Gaussian-location coupling. -/
def jointScore (tau : ℝ) (v : J→E) (y : J→ℝ) (z : Joint E) : Joint E :=
  WithLp.toLp 2 (-tau • ((WithLp.ofLp z).2-(WithLp.ofLp z).1),
    tau • ((WithLp.ofLp z).2-(WithLp.ofLp z).1)+
      ∑ j,(Real.sigmoid ⟪v j,(WithLp.ofLp z).2⟫-y j) • v j)

/-- The joint model is differentiable at every point, with no rank assumption. -/
theorem jointPotential_differentiable (tau : ℝ) (v : J→E) (y : J→ℝ) :
    Differentiable ℝ (jointPotential tau v y) := by
  have hp : Differentiable ℝ (potential tau v y) := by
    intro z
    have hx : DifferentiableAt ℝ (fun z : E×E ↦ z.2) z := differentiableAt_snd
    have hθ : DifferentiableAt ℝ (fun z : E×E ↦ z.1) z := differentiableAt_fst
    apply DifferentiableAt.add
    · exact ((hx.sub hθ).norm_sq ℝ).const_mul (tau/2)
    · apply DifferentiableAt.fun_sum
      intro j _
      exact (hasDerivAt_logisticLoss (y j) ⟪v j,z.2⟫).differentiableAt.comp z
        ((innerSL ℝ (v j)).differentiableAt.comp z hx)
  exact hp.comp (WithLp.prodContinuousLinearEquiv 2 ℝ E E).differentiable

/-- The two score blocks are the actual Hilbert gradient of the experimental potential. -/
theorem jointPotential_hasGradientAt [CompleteSpace E] (tau : ℝ) (v : J→E) (y : J→ℝ)
    (z : Joint E) : HasGradientAt (jointPotential tau v y) (jointScore tau v y z) z := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hd := (jointPotential_differentiable tau v y z).hasFDerivAt
  convert hd using 1
  ext d
  have hline := hd.hasLineDerivAt d
  have hraw := potential_line_derivative tau v y (WithLp.ofLp z) (WithLp.ofLp d) 0
  have he : fderiv ℝ (jointPotential tau v y) z d =
      lineScore tau v y (WithLp.ofLp z) (WithLp.ofLp d) 0 := by
    apply hline.unique
    simpa only [HasLineDerivAt,jointPotential,WithLp.ofLp_add,WithLp.ofLp_smul] using hraw
  rw [InnerProductSpace.toDual_apply_apply,he]
  simp only [jointScore,WithLp.prod_inner_apply,
    lineScore,zero_smul,add_zero,inner_add_left,inner_sub_right,real_inner_smul_left,sum_inner]
  ring

/-- In particular the library gradient agrees with the two explicit source blocks. -/
theorem jointPotential_gradient [CompleteSpace E] (tau : ℝ) (v : J→E) (y : J→ℝ)
    (z : Joint E) : gradient (jointPotential tau v y) z=jointScore tau v y z :=
  (jointPotential_hasGradientAt tau v y z).gradient

omit [InnerProductSpace ℝ E] in
/-- The exact Euclidean prior block has operator norm at most two. -/
theorem priorBlock_norm_le (z : Joint E) :
    ‖WithLp.toLp 2 (-(WithLp.ofLp z).2+(WithLp.ofLp z).1,
      (WithLp.ofLp z).2-(WithLp.ofLp z).1)‖ ≤ 2*‖z‖ := by
  let a := (WithLp.ofLp z).1
  let b := (WithLp.ofLp z).2
  have ht : ‖b-a‖ ≤ ‖b‖+‖a‖ := norm_sub_le b a
  have hsq : ‖b-a‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (b-a),norm_nonneg a,norm_nonneg b]
  have hz := WithLp.prod_norm_sq_eq_of_L2 z
  have he : -b+a=-(b-a) := by module
  have hw : ‖WithLp.toLp 2 (-b+a,b-a)‖^2=2*‖b-a‖^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖-b+a‖^2+‖b-a‖^2=2*‖b-a‖^2
    rw [he,norm_neg]
    ring
  change ‖WithLp.toLp 2 (-b+a,b-a)‖≤2*‖z‖
  change ‖z‖^2=‖a‖^2+‖b‖^2 at hz
  nlinarith [norm_nonneg (WithLp.toLp 2 (-b+a,b-a)),norm_nonneg z]

/-- The logistic part contributes the source sum of quarter squared feature norms. -/
theorem observationScore_sub_norm_le (v : J→E) (z z' : Joint E) :
    ‖∑ j,(Real.sigmoid ⟪v j,(WithLp.ofLp z).2⟫-
      Real.sigmoid ⟪v j,(WithLp.ofLp z').2⟫) • v j‖ ≤
      (∑ j,‖v j‖^2/4)*‖z-z'‖ := by
  calc
    _ ≤ ∑ j,‖(Real.sigmoid ⟪v j,(WithLp.ofLp z).2⟫-
        Real.sigmoid ⟪v j,(WithLp.ofLp z').2⟫) • v j‖ := norm_sum_le _ _
    _ ≤ ∑ j,(‖v j‖^2/4)*‖z-z'‖ := by
      apply Finset.sum_le_sum
      intro j _
      have hs := sigmoid_lipschitz.dist_le_mul
        ⟪v j,(WithLp.ofLp z).2⟫ ⟪v j,(WithLp.ofLp z').2⟫
      rw [dist_eq_norm,dist_eq_norm,← inner_sub_right] at hs
      have hi := norm_inner_le_norm (𝕜:=ℝ) (v j) ((WithLp.ofLp z).2-(WithLp.ofLp z').2)
      have hp := WithLp.norm_snd_le (p:=2) (α:=E) (β:=E) (z-z')
      change ‖(WithLp.ofLp z).2-(WithLp.ofLp z').2‖≤‖z-z'‖ at hp
      rw [norm_smul]
      change |Real.sigmoid _-Real.sigmoid _| *‖v j‖≤_
      have h1 : |Real.sigmoid ⟪v j,(WithLp.ofLp z).2⟫-
          Real.sigmoid ⟪v j,(WithLp.ofLp z').2⟫| ≤ (1/4)*‖v j‖*‖z-z'‖ := by
        change |Real.sigmoid _-Real.sigmoid _| ≤ (1/4)*|⟪v j,(WithLp.ofLp z).2-(WithLp.ofLp z').2⟫| at hs
        change |⟪v j,(WithLp.ofLp z).2-(WithLp.ofLp z').2⟫| ≤ _ at hi
        nlinarith [norm_nonneg (v j),norm_nonneg (z-z')]
      nlinarith [norm_nonneg (v j)]
    _ = _ := by rw [Finset.sum_mul]

/-- The exact global source gradient bound, in the Euclidean joint norm. -/
theorem jointScore_sub_norm_le (tau : ℝ) (htau : 0≤tau) (v : J→E) (y : J→ℝ)
    (z z' : Joint E) :
    ‖jointScore tau v y z-jointScore tau v y z'‖ ≤
      (2*tau+∑ j,‖v j‖^2/4)*‖z-z'‖ := by
  let d := z-z'
  let P : Joint E := WithLp.toLp 2 (-(WithLp.ofLp d).2+(WithLp.ofLp d).1,
    (WithLp.ofLp d).2-(WithLp.ofLp d).1)
  let S : E := ∑ j,(Real.sigmoid ⟪v j,(WithLp.ofLp z).2⟫-
    Real.sigmoid ⟪v j,(WithLp.ofLp z').2⟫) • v j
  have he : jointScore tau v y z-jointScore tau v y z' =
      tau • P+WithLp.toLp 2 (0,S) := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [jointScore,P,d]; module
    · simp [jointScore,P,d,S,Finset.sum_sub_distrib,sub_smul]; module
  rw [he]
  calc
    _ ≤ ‖tau • P‖+‖WithLp.toLp 2 (0,S)‖ := norm_add_le _ _
    _ = tau*‖P‖+‖S‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg htau,WithLp.norm_toLp_snd]
    _ ≤ tau*(2*‖d‖)+(∑ j,‖v j‖^2/4)*‖d‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (priorBlock_norm_le d) htau)
        (observationScore_sub_norm_le v z z')
    _ = _ := by dsimp [d]; ring

/-- Substituting tau=σ⁻² gives exactly 2/σ²+Σ‖v_j‖²/4. -/
theorem jointPotential_gradient_lipschitz [CompleteSpace E]
    (tau : ℝ≥0) (v : J→E) (y : J→ℝ) :
    LipschitzWith (2*tau+∑ j,‖v j‖₊^2/4)
      (gradient (jointPotential (tau:ℝ) v y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  simp only [dist_eq_norm,jointPotential_gradient,NNReal.coe_add,NNReal.coe_mul,
    NNReal.coe_ofNat,NNReal.coe_sum,NNReal.coe_div,NNReal.coe_pow,coe_nnnorm]
  exact jointScore_sub_norm_le tau tau.coe_nonneg v y z z'

/-- On a perfectly separated scalar observation the loss is bounded along the common-location ray. -/
theorem logisticLoss_one_eq (t : ℝ) : logisticLoss 1 t=Real.log (1+Real.exp (-t)) := by
  have he : (1+Real.exp (-t))*Real.exp t=1+Real.exp t := by
    rw [Real.exp_neg]
    field_simp
    ring
  unfold logisticLoss
  rw [← he,Real.log_mul (by positivity) (Real.exp_ne_zero t),Real.log_exp]
  ring

/-- This ray is nonnegative and bounded, despite the feature matrix having full rank. -/
theorem logisticLoss_one_bounds (t : ℝ) (ht : 0≤t) :
    0≤logisticLoss 1 t ∧ logisticLoss 1 t≤Real.log 2 := by
  rw [logisticLoss_one_eq]
  have he : Real.exp (-t)≤1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr ht)
  exact ⟨Real.log_nonneg (by linarith [Real.exp_pos (-t)]),Real.log_le_log (by positivity) (by linarith)⟩

/-- A full-rank, strictly convex logistic joint model need not have any positive global strong-convexity constant. -/
theorem scalar_model_not_strongConvex (tau : ℝ) (m : ℝ) (hm : 0<m) :
    ¬StrongConvexOn Set.univ m
      (jointPotential tau (fun _ : Fin 1 ↦ (1:ℝ)) (fun _ ↦ 1)) := by
  intro hsc
  let t := Real.sqrt ((Real.log 2+1)/m)
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  have ht : 0≤t := Real.sqrt_nonneg _
  have ht2 : t^2=(Real.log 2+1)/m := Real.sq_sqrt (by positivity)
  have hmt : m*t^2=Real.log 2+1 := by rw [ht2]; field_simp
  let z : Joint ℝ := WithLp.toLp 2 (0,0)
  let z' : Joint ℝ := WithLp.toLp 2 (2*t,2*t)
  rcases hsc with ⟨_,hsc⟩
  have hv := hsc (Set.mem_univ z) (Set.mem_univ z')
    (a:=(1/2:ℝ)) (b:=(1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hz : jointPotential tau (fun _ : Fin 1 ↦ (1:ℝ)) (fun _ ↦ 1) z=Real.log 2 := by
    norm_num [jointPotential,potential,z,logisticLoss]
  have hz' : jointPotential tau (fun _ : Fin 1 ↦ (1:ℝ)) (fun _ ↦ 1) z'=logisticLoss 1 (2*t) := by
    simp [jointPotential,potential,z']
  have hmid : jointPotential tau (fun _ : Fin 1 ↦ (1:ℝ)) (fun _ ↦ 1)
      ((1/2:ℝ) • z+(1/2:ℝ) • z')=logisticLoss 1 t := by
    simp [jointPotential,potential,z,z',WithLp.ofLp_add,WithLp.ofLp_smul]
  have hnorm : ‖z-z'‖^2=8*t^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖(0:ℝ)-2*t‖^2+‖(0:ℝ)-2*t‖^2=8*t^2
    simp only [Real.norm_eq_abs,sq_abs]
    ring
  change _≤(1/2:ℝ)*_+(1/2:ℝ)*_-(1/2:ℝ)*(1/2:ℝ)*(m/2*‖z-z'‖^2) at hv
  rw [hz,hz',hmid,hnorm] at hv
  have h0 := (logisticLoss_one_bounds t ht).1
  have hb := (logisticLoss_one_bounds (2*t) (by positivity)).2
  nlinarith

/-- Even the counterexample has full feature span, so the caveat is about uniform curvature, not identifiability. -/
theorem scalar_features_span : Submodule.span ℝ (Set.range (fun _ : Fin 1 ↦ (1:ℝ)))=⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  have h1 : (1:ℝ)∈Submodule.span ℝ (Set.range (fun _ : Fin 1 ↦ (1:ℝ))) :=
    Submodule.subset_span ⟨0,rfl⟩
  simpa only [smul_eq_mul,mul_one] using
    (Submodule.span ℝ (Set.range (fun _ : Fin 1 ↦ (1:ℝ)))).smul_mem x h1

/-- The displayed block Hessian, first on the ordinary coordinate product. -/
def rawHessian (tau : ℝ) (v : J→E) (x : E) : (E×E)→L[ℝ](E×E) :=
  let D := ContinuousLinearMap.snd ℝ E E-ContinuousLinearMap.fst ℝ E E
  (-tau • D).prod (tau • D+∑ j,
    (logisticWeight ⟪v j,x⟫ • ((innerSL ℝ (v j)).comp (ContinuousLinearMap.snd ℝ E E))).smulRight (v j))

/-- The same block matrix as a continuous linear operator in the Euclidean joint norm. -/
def jointHessian (tau : ℝ) (v : J→E) (z : Joint E) : Joint E→L[ℝ]Joint E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap ∘L
    rawHessian tau v (WithLp.ofLp z).2 ∘L
      (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

/-- Differentiating the actual gradient gives exactly the displayed Hessian blocks. -/
theorem jointScore_hasFDerivAt (tau : ℝ) (v : J→E) (y : J→ℝ) (z : Joint E) :
    HasFDerivAt (jointScore tau v y) (jointHessian tau v z) z := by
  let p := WithLp.ofLp z
  have hx : HasFDerivAt (fun p : E×E ↦ p.2) (ContinuousLinearMap.snd ℝ E E) p :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have hθ : HasFDerivAt (fun p : E×E ↦ p.1) (ContinuousLinearMap.fst ℝ E E) p :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum (u:=Finset.univ) (fun j _ ↦
    ((((Real.hasDerivAt_sigmoid ⟪v j,p.2⟫).hasFDerivAt.comp p
      ((innerSL ℝ (v j)).hasFDerivAt.comp p hx)).sub_const (y j)).smul_const (v j)))
  have hp := ((hx.sub hθ).const_smul (-tau)).prodMk
    (((hx.sub hθ).const_smul tau).add hsum)
  have hd := (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.hasFDerivAt.comp p hp
  have he := hd.comp z (WithLp.prodContinuousLinearEquiv 2 ℝ E E).hasFDerivAt
  convert he using 1
  · rfl
  · ext d
    simp [jointHessian,rawHessian,logisticWeight,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.smulRight_apply,p,mul_comm]

/-- Thus the second Fréchet derivative is an actual explicit operator, not an assumed Hessian. -/
theorem jointPotential_fderiv_gradient [CompleteSpace E] (tau : ℝ) (v : J→E) (y : J→ℝ)
    (z : Joint E) : fderiv ℝ (gradient (jointPotential tau v y)) z=jointHessian tau v z := by
  have hg : gradient (jointPotential tau v y)=jointScore tau v y :=
    funext (jointPotential_gradient tau v y)
  rw [hg]
  exact (jointScore_hasFDerivAt tau v y z).fderiv

/-- The block Hessian and its second-variation formula agree exactly. -/
theorem jointHessian_quadratic (tau : ℝ) (v : J→E) (z d : Joint E) :
    ⟪jointHessian tau v z d,d⟫=
      curvature tau v (WithLp.ofLp z).2 (WithLp.ofLp d).1 (WithLp.ofLp d).2 := by
  simp only [jointHessian,rawHessian,ContinuousLinearMap.comp_apply]
  simp [curvature,inner_add_left,real_inner_smul_left,sum_inner]
  have hs : (∑ j,logisticWeight ⟪v j,WithLp.snd z⟫*⟪v j,WithLp.snd d⟫*⟪v j,WithLp.snd d⟫)=
      ∑ j,logisticWeight ⟪v j,WithLp.snd z⟫*⟪v j,WithLp.snd d⟫^2 := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  have hi : ⟪WithLp.snd d-WithLp.fst d,WithLp.snd d⟫-
      ⟪WithLp.snd d-WithLp.fst d,WithLp.fst d⟫=‖WithLp.snd d-WithLp.fst d‖^2 := by
    rw [← inner_sub_right,real_inner_self_eq_norm_sq]
  rw [← hi]
  ring

/-- A finite logistic likelihood grows at most linearly in its scalar predictor. -/
theorem logisticLoss_le_linear (y u : ℝ) :
    logisticLoss y u≤Real.log 2+(1+|y|)*|u| := by
  have he : 1+Real.exp u≤2*Real.exp |u| := by
    have h0 : 1≤Real.exp |u| := by simp
    have h1 := Real.exp_le_exp.mpr (le_abs_self u)
    linarith
  have hh := Real.log_le_log (by positivity : 0<1+Real.exp u) he
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hh
  have hm : -y*u≤|y| *|u| := by
    calc -y*u=-(y*u) := by ring
         _≤|y*u| := neg_le_abs _
         _=|y| *|u| := abs_mul _ _
  unfold logisticLoss
  nlinarith

/-- Along a common parameter/latent translation the prior is constant and observations grow at most linearly. -/
theorem jointPotential_diagonal_growth (tau : ℝ) (v : J→E) (y : J→ℝ) (w : E) (t : ℝ) :
    jointPotential tau v y (WithLp.toLp 2 (t • w,t • w))≤
      (Fintype.card J:ℝ)*Real.log 2+|t| *∑ j,(1+|y j|)*|⟪v j,w⟫| := by
  simp only [jointPotential,potential,sub_self,norm_zero,
    ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero,zero_add,inner_smul_right]
  calc
    _≤∑ j,(Real.log 2+(1+|y j|)*|t*⟪v j,w⟫|) :=
      Finset.sum_le_sum (fun j _ ↦ logisticLoss_le_linear _ _)
    _=_ := by simp [abs_mul,Finset.sum_add_distrib,Finset.mul_sum,mul_left_comm]

/-- In every nonzero latent dimension the unregularized finite logistic model fails global positive strong convexity. -/
theorem jointPotential_not_strongConvex (tau : ℝ) (v : J→E) (y : J→ℝ)
    (w : E) (hw : w≠0) (m : ℝ) (hm : 0<m) :
    ¬StrongConvexOn Set.univ m (jointPotential tau v y) := by
  intro hsc
  let C := ∑ j,(1+|y j|)*|⟪v j,w⟫|
  have hC : 0≤C := Finset.sum_nonneg (fun j _ ↦ mul_nonneg (by positivity) (abs_nonneg _))
  have hD : 0<‖w‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
  let t := (C+1)/(m*‖w‖^2)
  have ht : 0<t := div_pos (by linarith) (mul_pos hm hD)
  have hmt : m*‖w‖^2*t=C+1 := by dsimp [t]; field_simp
  let z : Joint E := WithLp.toLp 2 ((-t) • w,(-t) • w)
  let z' : Joint E := WithLp.toLp 2 (t • w,t • w)
  rcases hsc with ⟨_,hsc⟩
  have hv := hsc (Set.mem_univ z) (Set.mem_univ z')
    (a:=(1/2:ℝ)) (b:=(1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hmid : (1/2:ℝ) • z+(1/2:ℝ) • z'=0 := by
    apply WithLp.ofLp_injective 2
    simp [z,z',WithLp.ofLp_add,WithLp.ofLp_smul]
  have hzero : jointPotential tau v y 0=(Fintype.card J:ℝ)*Real.log 2 := by
    simp [jointPotential,potential,logisticLoss]
    norm_num
  have hnorm : ‖z-z'‖^2=8*t^2*‖w‖^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖(-t) • w-t • w‖^2+‖(-t) • w-t • w‖^2=8*t^2*‖w‖^2
    simp only [← sub_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have h1 : jointPotential tau v y z≤(Fintype.card J:ℝ)*Real.log 2+t*C := by
    simpa only [z,abs_neg,abs_of_pos ht] using jointPotential_diagonal_growth tau v y w (-t)
  have h2 : jointPotential tau v y z'≤(Fintype.card J:ℝ)*Real.log 2+t*C := by
    simpa only [z',abs_of_pos ht] using jointPotential_diagonal_growth tau v y w t
  rw [hmid,hzero] at hv
  change _≤(1/2:ℝ)*_+(1/2:ℝ)*_-(1/2:ℝ)*(1/2:ℝ)*(m/2*‖z-z'‖^2) at hv
  rw [hnorm] at hv
  have hmt2 := congrArg (fun r : ℝ ↦ r*t) hmt
  nlinarith

end KIPLMC.LogisticExample
