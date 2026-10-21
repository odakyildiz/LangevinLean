import UnadjustedLangevin.LSI.Theorem
import UnadjustedLangevin.LSI.Regularity
import UnadjustedLangevin.LSI.RegularizedTheorem
import UnadjustedLangevin.LSI.GaussianDrift

/-! Kernel dependency audit for the conditional LSI development.
The analytic assumptions are visible in the theorem statements; none is
introduced as an axiom. Every audited theorem uses only Lean's standard
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
