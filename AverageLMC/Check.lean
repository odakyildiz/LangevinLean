import AverageLMC

set_option linter.style.header false

/-! Kernel axiom audit of the actual-law main sampling statements, their
analytic dependencies, and the separate source counterexamples. -/

#print axioms AverageLMC.coordinate_upper_bound
#print axioms AverageLMC.gradient_lipschitz_globalSmoothness
#print axioms AverageLMC.averageSmoothness_le_globalSmoothness
#print axioms AverageLMC.strongConvex_le_averageSmoothness
#print axioms AverageLMC.trace_hessian
#print axioms AverageLMC.gradient_step
#print axioms AverageLMC.gradient_descent
#print axioms AverageLMC.constant_step_normalized
#print axioms AverageLMC.variable_step_normalized
#print axioms AverageLMC.variable_step_accuracy
#print axioms AverageLMC.counterexampleComponent_contDiff
#print axioms AverageLMC.counterexampleComponent_convex
#print axioms AverageLMC.counterexampleComponent_derivative_bound
#print axioms AverageLMC.counterexamplePotential_eq_sum
#print axioms AverageLMC.gradient_counterexamplePotential
#print axioms AverageLMC.fderiv_gradient_counterexamplePotential
#print axioms AverageLMC.counterexamplePotential_hessian_lipschitz_lower
#print axioms AverageLMC.stdGaussian_norm_sq_variance
#print axioms AverageLMC.stdGaussian_cube_bound_fails
#print axioms AverageLMC.no_uniform_stdGaussian_cube_bound
#print axioms AverageLMC.gaussianDesign_row_law
#print axioms AverageLMC.gaussianDesign_rows_independent
#print axioms AverageLMC.glmHessianBound_probability_lt_half
#print axioms AverageLMC.no_uniform_glmHessian_bound
#print axioms AverageLMC.lmc_one_step
#print axioms AverageLMC.lmc_constant_step
#print axioms AverageLMC.lmc_constant_step_extended
#print axioms AverageLMC.lmc_variable_step
#print axioms AverageLMC.lmc_variable_step_accuracy_extended_initial
#print axioms AverageLMC.integral_stdGaussian_smoothing
#print axioms AverageLMC.score_laplacian_identity_and_bounds
#print axioms AverageLMC.wasserstein2_sq_centered_perturbation
#print axioms AverageLMC.sgld_one_step
#print axioms AverageLMC.sgld_one_step_rms
#print axioms AverageLMC.sgld_constant_step_extended
#print axioms AverageLMC.sgld_constant_step_paper
#print axioms AverageLMC.averageSmoothness_div_nat
#print axioms AverageLMC.lp_langevin_weighted_dynkin_compact
#print axioms AverageLMC.score_vector_compact_approximation
#print axioms AverageLMC.lp_stationary_gradient_pairing_bound
#print axioms AverageLMC.laplacian_coupling_step
#print axioms AverageLMC.lmc_laplacian
#print axioms AverageLMC.lmc_laplacian_extended
#print axioms AverageLMC.gaussian_empirical_fourth_event_fails
#print axioms AverageLMC.sgld_transient_comparison_counterexample
