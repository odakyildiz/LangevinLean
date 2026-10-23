import KineticLangevin.Thermostat
import KineticLangevin.OUMarginal
import KineticLangevin.LpDynamics

/-! # A stationary free-OU velocity from its actual initial/noise joint law -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace KineticLangevin
section Gaussian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Adding an independent thermal innovation preserves the actual standard Gaussian law. -/
theorem stdGaussian_add_thermal (a : ℝ) (ha : a^2≤1) :
    ((stdGaussian E).prod ((stdGaussian E).map (fun z ↦ Real.sqrt (1-a^2) • z))).map
      (fun p ↦ a • p.1+p.2) = stdGaussian E := by
  have hp := Measure.map_prod_map (stdGaussian E) (stdGaussian E) measurable_id
    (f:=id) (g:=fun z ↦ Real.sqrt (1-a^2) • z) (by fun_prop)
  rw [Measure.map_id] at hp
  rw [hp,Measure.map_map (by fun_prop) (measurable_id.prodMap (by fun_prop))]
  apply stdGaussian_linear_combination
  rw [Real.sq_sqrt (sub_nonneg.mpr ha)]
  ring
end Gaussian

section Velocity
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω)

/-- The exact homogeneous OU velocity, retaining the actual filtered innovation. -/
def freeOUVelocity (γ : ℝ) (V : Lp E 2 P) (N : ℝ→Lp E 2 P) (t : ℝ) : Lp E 2 P :=
  psi γ 0 t • V+N t

theorem continuous_freeOUVelocity (γ : ℝ) (V : Lp E 2 P) (N : ℝ→Lp E 2 P)
    (hN : Continuous N) : Continuous (freeOUVelocity P γ V N) :=
  ((continuous_psi γ 0).smul continuous_const).add hN

/-- The free OU position increment is the true primitive of its velocity, on the same source. -/
theorem freeOUVelocity_primitive [CompleteSpace E] (γ : ℝ) (V : Lp E 2 P) (N : ℝ→Lp E 2 P)
    (hN : Continuous N) (t : ℝ) :
    (∫ s in 0..t,freeOUVelocity P γ V N s)=psi γ 1 t • V+∫ s in 0..t,N s := by
  change (∫ s in 0..t,psi γ 0 s • V+N s)=_
  have hi : IntervalIntegrable (fun s ↦ psi γ 0 s • V) volume 0 t :=
    ((continuous_psi γ 0).smul continuous_const).intervalIntegrable 0 t
  rw [intervalIntegral.integral_add hi (hN.intervalIntegrable 0 t),intervalIntegral.integral_smul_const]
  rfl
end Velocity

/-- The exact OU combination has the standard Gaussian marginal once the actual initial/fresh-noise joint law is proved. -/
theorem freeOUVelocity_hasLaw {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (γ : ℝ) (hγ : 0≤γ) (V : Lp E 2 P) (N : ℝ→Lp E 2 P)
    (t : ℝ) (ht : 0≤t)
    (hpair : HasLaw (fun ω ↦ (V ω,N t ω))
      ((stdGaussian E).prod ((stdGaussian E).map (fun z ↦ Real.sqrt (1-(psi γ 0 t)^2) • z))) P) :
    HasLaw (freeOUVelocity P γ V N t) (stdGaussian E) P := by
  have hp : (psi γ 0 t)^2≤1 := by
    have hlo := psi_nonneg γ 0 ht
    have hhi := psi_zero_le_one hγ ht
    nlinarith
  have hsum : HasLaw (fun p : E×E ↦ psi γ 0 t • p.1+p.2) (stdGaussian E)
      ((stdGaussian E).prod ((stdGaussian E).map (fun z ↦ Real.sqrt (1-(psi γ 0 t)^2) • z))) :=
    ⟨(by fun_prop),stdGaussian_add_thermal (psi γ 0 t) hp⟩
  apply (hsum.comp hpair).congr
  filter_upwards [Lp.coeFn_add (psi γ 0 t • V) (N t),Lp.coeFn_smul (psi γ 0 t) V] with ω hadd hsmul
  change (psi γ 0 t • V+N t) ω=psi γ 0 t • V ω+N t ω
  rw [hadd,Pi.add_apply,hsmul]
  rfl

end KineticLangevin
