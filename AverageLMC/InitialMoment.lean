import AverageLMC.PathwiseEnergy
import AverageLMC.SquaredTransport
import AverageLMC.CenteredPerturbation
import ProximalLangevin.SharpConcentration
import UnadjustedLangevin.ProductBrownian

set_option linter.style.header false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace AverageLMC
open ULA ULA.Hilbert

/-- An arbitrary initial law's squared radius about the true minimizer is
controlled by its actual transport distance and the sharp Gibbs radius. -/
theorem initial_radius_le {p : ℕ} (f : State p → ℝ) (m : ℝ) (hm : 0 < m)
    (hf : Differentiable ℝ f) (hsc : StrongConvexOn univ m f)
    (anchor : State p) (hanchor : ∀ x, f anchor ≤ f x)
    (μ : Measure (State p)) [IsProbabilityMeasure μ]
    (hfinite : wasserstein2 μ (gibbsMeasure f) ≠ ⊤) :
    (∫ x, ‖x - anchor‖ ^ 2 ∂μ) ≤
      2 * wasserstein2Real μ (gibbsMeasure f) ^ 2 + 2 * (p : ℝ) / m := by
  have hπ := memLp_id_gibbsMeasure f m hm hf hsc
  have hμ := memLp_id_of_wasserstein2_ne_top μ (gibbsMeasure f) hfinite hπ
  have hradius := ProximalLangevin.sharp_integral_sq_dist_gibbs_le
    f m hm hf.continuous hsc anchor hanchor
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hradius
  apply real_bound_of_finite_couplings μ (gibbsMeasure f)
    (∫ x, ‖x - anchor‖ ^ 2 ∂μ) 2 (2 * (p : ℝ) / m) hfinite
  intro c hc
  have : IsProbabilityMeasure c.joint := c.isProbabilityMeasure
  have hfst : MemLp (fun z : State p × State p ↦ z.1) 2 c.joint := by
    have h := hμ
    rw [← c.fst] at h
    exact h.comp_of_map measurable_fst.aemeasurable
  have hsnd : MemLp (fun z : State p × State p ↦ z.2) 2 c.joint := by
    have h := hπ
    rw [← c.snd] at h
    exact h.comp_of_map measurable_snd.aemeasurable
  have hdiff := hfst.sub hsnd
  have hfst' := hfst.sub (memLp_const anchor)
  have hsnd' := hsnd.sub (memLp_const anchor)
  have hi := integral_mono_ae
    (hfst'.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))
    (((hdiff.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul 2).add
      ((hsnd'.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul 2))
    (ae_of_all _ fun z ↦ show ‖z.1 - anchor‖ ^ 2 ≤
      2 * ‖z.1 - z.2‖ ^ 2 + 2 * ‖z.2 - anchor‖ ^ 2 from by
        have h := ProximalLangevin.norm_add_sq_le_weighted (z.1 - z.2) (z.2 - anchor)
          (by norm_num : (0 : ℝ) < 1)
        simpa only [one_add_one_eq_two, inv_one, sub_add_sub_cancel] using h)
  change (∫ z : State p × State p, ‖z.1 - anchor‖ ^ 2 ∂c.joint) ≤
    ∫ z : State p × State p, 2 * ‖z.1 - z.2‖ ^ 2 + 2 * ‖z.2 - anchor‖ ^ 2 ∂c.joint at hi
  rw [integral_add (f := fun z : State p × State p ↦ 2 * ‖z.1 - z.2‖ ^ 2)
    (g := fun z : State p × State p ↦ 2 * ‖z.2 - anchor‖ ^ 2)
    ((hdiff.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul 2)
    ((hsnd'.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul 2),
    integral_const_mul, integral_const_mul] at hi
  have hleft : (∫ z : State p × State p, ‖z.1 - anchor‖ ^ 2 ∂c.joint) =
      ∫ x, ‖x - anchor‖ ^ 2 ∂μ := by
    calc
      _ = ∫ x, ‖x - anchor‖ ^ 2 ∂(c.joint.map Prod.fst) :=
        (integral_map measurable_fst.aemeasurable (by fun_prop)).symm
      _ = _ := by rw [c.fst]
  have hright : (∫ z : State p × State p, ‖z.2 - anchor‖ ^ 2 ∂c.joint) =
      ∫ x, ‖x - anchor‖ ^ 2 ∂gibbsMeasure f := by
    calc
      _ = ∫ x, ‖x - anchor‖ ^ 2 ∂(c.joint.map Prod.snd) :=
        (integral_map measurable_snd.aemeasurable (by fun_prop)).symm
      _ = _ := by rw [c.snd]
  have hcost : (couplingCost c.joint).toReal ^ 2 =
      ∫ z : State p × State p, ‖z.1 - z.2‖ ^ 2 ∂c.joint :=
    eLpNorm_toReal_sq_eq_integral c.joint _ hdiff
  rw [hleft, hright, ← hcost] at hi
  have hr := mul_le_mul_of_nonneg_left hradius (by norm_num : (0 : ℝ) ≤ 2)
  convert hi.trans (add_le_add (le_refl (2 * (couplingCost c.joint).toReal ^ 2)) hr) using 1 <;> ring

end AverageLMC
