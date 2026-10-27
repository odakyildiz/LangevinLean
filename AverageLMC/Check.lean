import AverageLMC

set_option linter.style.header false

/-! Kernel axiom audit of the actual-law main sampling statements and their
analytic dependencies. -/

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
