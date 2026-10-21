import UnadjustedLangevin

/-! Kernel dependency audit. Every listed theorem must depend only on Lean's
standard logical axioms, never on `sorryAx` or an added mathematical axiom. -/

#print axioms ULA.strong_gradient_monotone
#print axioms ULA.strong_smooth_gradient_interpolation
#print axioms ULA.ula_shared_noise_contract_sharp
#print axioms ULA.ula_shared_noise_contract_sharp_large
#print axioms ULA.wasserstein2_le_random_cost
#print axioms ULA.synchronous_l2_bound_real
#print axioms ULA.ulaChain_error_memLp
#print axioms ULA.localDefect_euler_identity
#print axioms ULA.localDefect_dalalyan_bound
#print axioms ULA.lpDrift_lipschitz
#print axioms ULA.lpUlaChain_coe
#print axioms ULA.gaussian_vector_second_moment
#print axioms ULA.brownianVector_increment_scaled_l2_norm
#print axioms ULA.affine_recurrence_bound
#print axioms ULA.wasserstein2_affine_bound_real_of_finite_couplings
#print axioms ULA.ula_wasserstein_bound_of_reference
#print axioms ULA.dalalyan_small_step_of_integral_reference
#print axioms ULA.dalalyan_large_step_of_integral_reference

-- Foundations proved from the potential assumptions and actual Brownian laws.
#print axioms ULA.strongConvex_le_lipschitz
#print axioms ULA.gibbsPartition_ne_top
#print axioms ULA.isProbabilityMeasure_gibbsMeasure
#print axioms ULA.memLp_id_gibbsMeasure
#print axioms ULA.memLp_id_of_wasserstein2_ne_top
#print axioms ULA.brownianCoordinatesRealLp_continuous
#print axioms ULA.brownianCoordinatesRealLp_increment_scaled_norm
#print axioms ULA.exists_langevin_integral
#print axioms ULA.exists_lp_langevin_integral_of_brownian

#print axioms ULA.integral_norm_sq_gradient_gibbs_le_of_strongConvex
#print axioms ULA.lpDrift_norm_le_of_strongConvex_gibbs_law
#print axioms ULA.langevin_integral_unique
#print axioms ULA.lp_langevin_integral_stability

-- Generator integration is proved, not an assumed stationarity property.
#print axioms ULA.integrable_langevinGenerator_gibbsMeasure
#print axioms ULA.integral_laplacian_sub_gradient_gibbs_eq_zero
#print axioms ULA.integral_langevinGenerator_dirichlet_gibbs
#print axioms ULA.integral_langevinGenerator_symmetric_gibbs
#print axioms ULA.integral_langevinGenerator_dissipative_gibbs
#print axioms ULA.measure_eq_of_integral_contDiff_two_eq
#print axioms ULA.constant_gibbs_isWeakFokkerPlanckSolution
#print axioms ULA.gibbs_stationary_of_weakFokkerPlanckUniqueness
#print axioms ULA.noiseDrivenChain_law_of_iid
#print axioms ULA.lpUlaChain_law_of_iid
#print axioms ULA.initialExtension_joint
#print axioms ULA.initialExtension_independent
#print axioms ULA.initialExtension_lp_cost
#print axioms ULA.initialExtension_chainLaw
#print axioms ULA.normalizedBrownianIncrement_hasLaw
#print axioms ULA.normalizedBrownianIncrements_independent
#print axioms ULA.normalizedBrownianIncrement_second_moment
#print axioms ULA.normalizedBrownianIncrements_hasLaw


-- Closed stochastic construction and unconditional algorithm endpoints.
#print axioms ULA.GaussianHilbert.isonormal_hasLaw
#print axioms ULA.CanonicalBrownian.isPreBrownian
#print axioms ULA.CanonicalBrownian.coordinate_paths_independent
#print axioms ULA.gaussian_proposal_density
#print axioms ULA.gaussian_proposal_pair_density
#print axioms ULA.metropolisOutput_density_eq_initial
#print axioms ULA.malaOneStep_gibbs_invariant
#print axioms ULA.malaRejectionDisplacement_pointwise
#print axioms ULA.malaCoupledChain_distance_integral_le
#print axioms ULA.additiveEulerChain_tendsto
#print axioms ULA.chainLaw_eq_markovLaws
#print axioms ULA.measure_map_Lp_eq_of_coupling_cost_tendsto
#print axioms ULA.lp_langevin_gibbs_stationary
#print axioms ULA.Hilbert.brownianSegments_eq_global
#print axioms ULA.Hilbert.productReference_of_independent_brownian
#print axioms ULA.Hilbert.canonicalProductReference
#print axioms ULA.Hilbert.dalalyan_output_finite
#print axioms ULA.Hilbert.dalalyan
#print axioms ULA.Hilbert.dalalyan_large_step
#print axioms ULA.Hilbert.dalalyan_of_gaussian_innovations
#print axioms ULA.Hilbert.dalalyan_large_step_of_gaussian_innovations
#check @ULA.Hilbert.dalalyan
#check @ULA.Hilbert.dalalyan_large_step
#check @ULA.Hilbert.dalalyan_of_gaussian_innovations
#print axioms ULA.wasserstein2_eq_zero_of_subsingleton
#print axioms ULA.wasserstein2Real_eq_zero_of_subsingleton
