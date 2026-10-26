import PBGSO.FullyConstructedHigherOrder

/-!
# Theorem New B: final printed HOL-MYPGD endpoint

This is a compact repository check entry point, not a self-contained proof file.
Run `python3 scripts/check-pbgso-standalone.py --endpoint new-b --check`.
For one Mathlib-only file containing the entire local proof closure, use
`--output /tmp/pbgso-new-b --check`. See PBGSO/README.md.

The checked endpoint uses the actual printed affine coefficients and verified
Gaussian covariance. Its inputs are independent globally jointly Lipschitz
forces; a positive population with the flattened Euclidean encoding; alpha > 0,
gamma >= 0; P2 initial/target laws; an actual frozen invariant sampler; zero
target mean observation; positive source A3; and uniform reference observation
variance. Processes, references, Gaussian coupling and mesh-uniform constants
are constructed. The error rate is O(sqrt h) on each fixed horizon.

The stationary target can be biased by hybrid smoothing. The separately
checked original-target corollary adds L*epsilon/m from actual coupled target
observations, their expectation identities, and positive gradient monotonicity;
it does not assume or derive a model-specific Moreau coupling radius.
-/

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

#check @PBGSO.FullyConstructedHigherOrder.parameter_bound
#print axioms PBGSO.FullyConstructedHigherOrder.parameter_bound
#check @PBGSO.FullyConstructedHigherOrder.original_parameter_bound
#print axioms PBGSO.FullyConstructedHigherOrder.original_parameter_bound
