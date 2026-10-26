import PBGSO.RawPathSolutionTransfer
import PBGSO.RawStationaryUniqueness
import PBGSO.NaturalFiniteWorkArbitraryLaw
import PBGSO.RawSamplerGrowthArbitraryLaw
import PBGSO.RawConstructedParticleBounds
import PBGSO.RawConstructedParticleParameter
import PBGSO.RawConstructedParticleJointLimit
import PBGSO.SmallGainSpectrum
import PBGSO.ProjectedFiniteWork
import PBGSO.HypocoerciveCriterion
import PBGSO.ContinuousFlowMeasure
import PBGSO.DiscreteVolume

/-!
# Original paper endpoints: compact check entry point

This file imports the repository proofs. The exporter can instead produce a
single Mathlib-only file containing all transitive local definitions and proofs.
No theorem is renamed or weakened by this checking file.

The exact hypotheses remain in the printed theorem types. In particular, A1
is used as actual strong existence/pathwise uniqueness on the named sources;
A2 is actual frozen SDE invariance; the constant-diffusion law theorem uses
the explicitly named ordinary finite signed-work reading of universal A3.
The source3 distance compares the native empirical cloud with the independently
copied empirical cloud, rather than with its population law. Original native
particle-solution existence and synchronous initial coordinates are explicit.
Source4 includes the actual target and original observation variance. The
joint-limit family contains original equations, not a final error premise.
-/

-- Main Theorem 1.
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

#check @PBGSO.RawLocalStationarity.stationary_product_law_of_weak_frozen
#print axioms PBGSO.RawLocalStationarity.stationary_product_law_of_weak_frozen
-- Main Theorem 2: both source alternatives.
#check @PBGSO.NaturalFiniteWorkArbitraryLaw.law_distance_decay
#print axioms PBGSO.NaturalFiniteWorkArbitraryLaw.law_distance_decay
#check @PBGSO.RawSamplerGrowthArbitraryLaw.law_distance_decay
#print axioms PBGSO.RawSamplerGrowthArbitraryLaw.law_distance_decay
#check @PBGSO.RawStationaryUniqueness.stationary_laws_unique_constant
#print axioms PBGSO.RawStationaryUniqueness.stationary_laws_unique_constant
#check @PBGSO.RawStationaryUniqueness.stationary_laws_unique_linearGrowth
#print axioms PBGSO.RawStationaryUniqueness.stationary_laws_unique_linearGrowth
-- Main Theorem 3: original native empirical trajectories.
#check @PBGSO.RawConstructedParticleBounds.original_finite_particle_interaction_bound
#print axioms PBGSO.RawConstructedParticleBounds.original_finite_particle_interaction_bound
-- Main Theorem 4: both source alternatives and its limit consequence.
#check @PBGSO.RawConstructedParticleParameter.original_parameter_bound_constant
#print axioms PBGSO.RawConstructedParticleParameter.original_parameter_bound_constant
#check @PBGSO.RawConstructedParticleParameter.original_parameter_bound_linearGrowth
#print axioms PBGSO.RawConstructedParticleParameter.original_parameter_bound_linearGrowth
#check @PBGSO.RawConstructedParticleJointLimit.parameter_joint_limit
#print axioms PBGSO.RawConstructedParticleJointLimit.parameter_joint_limit
-- Appendix corollaries and the heavy-ball proposition.
#check @PBGSO.separated_source_criterion
#print axioms PBGSO.separated_source_criterion
#check @PBGSO.CanonicalProjected.canonical_projected_source_criterion_finite
#print axioms PBGSO.CanonicalProjected.canonical_projected_source_criterion_finite
#check @PBGSO.heavyBall_source_criterion
#print axioms PBGSO.heavyBall_source_criterion
-- Continuous and discrete volume lemma.
#check @PBGSO.ContinuousFlowMeasure.phase_flow_measurePreserving_source
#print axioms PBGSO.ContinuousFlowMeasure.phase_flow_measurePreserving_source
#check @PBGSO.interwovenBAB_fderiv_det_one
#print axioms PBGSO.interwovenBAB_fderiv_det_one
