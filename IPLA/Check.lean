import IPLA

/-! # Kernel dependency and final-hypothesis audit

The final theorem derives stationarity, the reference construction, finite
transport, and marginal concentration from the stated joint assumptions.
Only `propext`, `Classical.choice`, and `Quot.sound` may appear below.
-/

#check @IPLA.theorem1

#print axioms IPLA.theorem1
#print axioms ULA.Hilbert.dalalyan
#print axioms ULA.Hilbert.canonicalProductReference
#print axioms ULA.lp_langevin_gibbs_stationary
#print axioms ULA.Hilbert.brownianSegments_eq_global
#print axioms ULA.CanonicalBrownian.coordinate_isPreBrownian
#print axioms ULA.malaOneStep_gibbs_invariant
#print axioms ULA.measure_map_Lp_eq_of_coupling_cost_tendsto
#print axioms ULA.integral_langevinGenerator_dirichlet_gibbs
#print axioms ULA.constant_gibbs_isWeakFokkerPlanckSolution
#print axioms IPLA.gibbsTarget_infinitesimalInvariant
#print axioms IPLA.gibbsTarget_isProbability
#print axioms IPLA.gibbsTarget_memLp
#print axioms ULA.wasserstein2_ne_top_of_memLp
#print axioms IPLA.laws_eq_ulaLawStep
#print axioms IPLA.gibbsTarget_parameter_marginal
#print axioms IPLA.marginalPartition_ne_top
#print axioms IPLA.Prekopa.prekopa_leindler
#print axioms IPLA.marginalPotential_strongConvex
#print axioms IPLA.existsUnique_marginalMaximizer
#print axioms ULA.integral_sq_dist_gibbs_le_of_continuous_strongConvex_mode
#print axioms IPLA.gibbsTarget_parameter_concentration
#print axioms IPLA.joint_norm_sq_sum
#print axioms IPLA.potential_strongConvex
#print axioms IPLA.potential_gradient_lipschitz
#print axioms IPLA.scaled_bias_eq
#print axioms IPLA.parameterRMS_zero_dimension
#print axioms IPLA.zero_dimensions_bound
