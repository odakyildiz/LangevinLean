import AverageLMC

set_option linter.style.header false

/-! Kernel axiom audit of the exact deterministic lemmas, conditional scalar
recurrences, and actual-potential Gaussian design obstruction. This file does
not assert that the three paper-level sampling theorems have been proved. -/

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
