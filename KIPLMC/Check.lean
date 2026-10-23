import KIPLMC

/-! Kernel axiom audit of the algorithms, targets, and complete actual-law
diffusion and numerical parameter-error theorems. -/

#print axioms KIPLMC.averagePotential_strongConvex
#print axioms KIPLMC.gradient_averagePotential
#print axioms KIPLMC.force_lipschitz
#print axioms KIPLMC.force_particle
#print axioms KIPLMC.exists_kipld_integral
#print axioms KIPLMC.kipld_synchronous_position_decay
#print axioms KIPLMC.kipldPositionLaw_wasserstein2Real
#print axioms KIPLMC.kiplmc1Step_parameter_velocity
#print axioms KIPLMC.kiplmc1Step_particle_velocity
#print axioms KIPLMC.kiplmc1Step_particle_position
#print axioms KIPLMC.halfVelocity_parameter
#print axioms KIPLMC.halfVelocity_particle
#print axioms KIPLMC.kiplmc2Step_velocity
#print axioms KIPLMC.exponentialStep_conjugate
#print axioms KIPLMC.obaboDamping_scaled
#print axioms KIPLMC.gibbsPhaseTarget_probability
#print axioms KIPLMC.gibbsPhaseTarget_parameter
#print axioms KIPLMC.existsUnique_mmle
#print axioms KIPLMC.parameter_secondMoment_le
#print axioms KIPLMC.parameter_concentration
#print axioms KIPLMC.velocityTarget_unscale
#print axioms KIPLMC.thermal_velocity_Lp_norm
#print axioms KIPLMC.kiplmc1_reference_parameter_bound
#print axioms KIPLMC.kiplmc1Chain_law
#print axioms KIPLMC.kiplmc2Chain_law
#print axioms KIPLMC.exponentialNoise_coordinate_law
#print axioms KIPLMC.exponentialNoiseBlocks_independent
#print axioms KIPLMC.kiplmc2Laws_probability
#print axioms KIPLMC.kiplmc2Step_synchronous_contraction
#print axioms KIPLMC.kiplmc2Chain_synchronous_contraction
#print axioms KIPLMC.kiplmc2Chain_position_decay
#print axioms KIPLMC.kiplmc2Chain_unitTemperature
#print axioms KIPLMC.kineticTarget_rescaleVelocity
#print axioms KIPLMC.kiplmc2Laws_unitTemperature
#print axioms KIPLMC.kiplmc1_parameter_bound
#print axioms KIPLMC.kiplmc1_parameter_bound_independent
#print axioms KIPLMC.kiplmc2_position_sampling_bound
#print axioms KIPLMC.kiplmc2_parameter_bound
#print axioms KIPLMC.kiplmc2_parameter_paper_bound

#print axioms KIPLMC.kipldBrownianFlow_integral

#print axioms KIPLMC.kipldBrownianFlow_initial_hasLaw

#print axioms KIPLMC.kipldBrownianFlow_stationary

#print axioms KIPLMC.kipld_parameter_sampling_bound

#print axioms KIPLMC.kipld_parameter_RMS_bound

#print axioms KIPLMC.kiplmc1_accuracy

#print axioms KIPLMC.kiplmc2_accuracy

#print axioms KIPLMC.LogisticExample.jointPotential_gradient_lipschitz

#print axioms KIPLMC.LogisticExample.jointPotential_fderiv_gradient

#print axioms KIPLMC.LogisticExample.jointHessian_quadratic

#print axioms KIPLMC.LogisticExample.potential_strictConvex_of_span

#print axioms KIPLMC.LogisticExample.jointPotential_not_strongConvex
