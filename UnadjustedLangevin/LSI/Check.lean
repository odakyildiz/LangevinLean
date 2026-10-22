import UnadjustedLangevin.LSI.Theorem
import UnadjustedLangevin.LSI.Regularity
import UnadjustedLangevin.LSI.RegularizedTheorem
import UnadjustedLangevin.LSI.GaussianDrift
import UnadjustedLangevin.LSI.InterpolationData
import UnadjustedLangevin.LSI.ConditionalDrift
import UnadjustedLangevin.LSI.InterpolationDensity
import UnadjustedLangevin.LSI.InteriorEntropy
import UnadjustedLangevin.LSI.GradientMoment
import UnadjustedLangevin.LSI.UnconditionalTheorem

/-! Kernel dependency audit for the complete actual Gaussian ULA LSI proof.
The final theorem derives its interpolation estimates from the original
potential and LSI assumptions. Every audited theorem uses only Lean's standard
logical axioms, with no `sorryAx` or added mathematical axiom. -/

#print axioms ULA.LSI.IsLogSobolev.entropy_le_fisher
#print axioms ULA.LSI.densityEntropy_eq_integral
#print axioms ULA.LSI.relativeFisher_toReal_eq_integral
#print axioms ULA.LSI.LocalEntropyRegularity.hasDerivAt_entropy
#print axioms ULA.LSI.densityEntropy_derivative_bound_of_regular_weak_equation
#print axioms ULA.LSI.relative_entropy_decay_of_dissipation
#print axioms ULA.LSI.interpolationLaw_endpoint
#print axioms ULA.LSI.one_step_entropy_of_interpolation
#print axioms ULA.LSI.discrete_entropy_recurrence_bound
#print axioms ULA.LSI.ula_kl_finite_of_interpolation
#print axioms ULA.LSI.ula_kl_one_step_of_interpolation
#print axioms ULA.LSI.ula_kl_bound_of_interpolation
#print axioms ULA.LSI.ula_kl_bound_of_regular_interpolation
#print axioms ULA.LSI.frozen_displacement_second_moment
#print axioms ULA.LSI.frozen_gradient_error_energy
#print axioms ULA.LSI.RegularInterpolationData.kl_finite
#print axioms ULA.LSI.RegularInterpolationData.kl_bound
#print axioms ULA.LSI.RegularInterpolationData.one_step

#print axioms ULA.LSI.exists_conditional_mean_with_energy
#print axioms ULA.LSI.conditional_mean_setIntegral
#print axioms ULA.LSI.conditional_mean_inner_integral
#print axioms ULA.LSI.exists_frozen_drift_error
#print axioms ULA.LSI.exists_frozen_drift_error_of_density
#print axioms ULA.LSI.interpolationLaw_eq_withDensity
#print axioms ULA.LSI.interpolationDensity_pos
#print axioms ULA.LSI.interpolationDensity_ne_top
#print axioms ULA.LSI.interpolationLaw_eq_real_withDensity
#print axioms ULA.LSI.interpolationLaw_absolutelyContinuous
#print axioms ULA.LSI.gibbsPartition_ne_top_of_probability
#print axioms ULA.LSI.interpolationRelativeDensity_pos
#print axioms ULA.LSI.tiltedMeasure_interpolationRelativeDensity
#print axioms ULA.LSI.interpolationRelativeDensity_isProbability
#print axioms ULA.LSI.affine_decay_of_deriv_le_interior
#print axioms ULA.LSI.densityEntropy_hasDerivAt_of_regular_interior

#print axioms ULA.LSI.interpolationLebesgueDensity_eq_integral
#print axioms ULA.LSI.interpolationLebesgueDensity_continuous
#print axioms ULA.LSI.interpolationRelativeDensity_continuous
#print axioms ULA.LSI.gradient_moment_bound_of_coupling
#print axioms ULA.LSI.gibbs_gradient_moment_bound_of_coupling
#print axioms ULA.LSI.gibbs_gradient_moment_bound_of_entropy_coupling

#print axioms ULA.LSI.IsLogSobolev.constant_le_smoothness
#print axioms ULA.LSI.gibbs_gradient_moment_bound_of_finite_kl
#print axioms ULA.LSI.interpolationLebesgueDensity_contDiff
#print axioms ULA.LSI.hasDerivAt_interpolationLebesgueDensity_time
#print axioms ULA.LSI.integrable_interpolationRelativeScoreField_energy_spacetime
#print axioms ULA.LSI.interpolationLebesgueDensity_weak_identity
#print axioms ULA.LSI.integral_frozenGaussianScore_pairing_independent
#print axioms ULA.LSI.interpolationEntropy_integral_identity
#print axioms ULA.LSI.interpolationEntropy_local_chain_rule
#print axioms ULA.LSI.interpolationEntropy_derivative_bound_ae
#print axioms ULA.LSI.interpolationLaw_entropy_eventually_le_majorant
#print axioms ULA.LSI.one_step_entropy_of_ae_interpolation
#print axioms ULA.LSI.ula_kl_finite
#print axioms ULA.LSI.interpolation_kl_one_step
#print axioms ULA.LSI.ula_kl_one_step
#print axioms ULA.LSI.ula_kl_bound
