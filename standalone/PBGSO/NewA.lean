import PBGSO.FullyConstructedMomentum

/-!
# Theorem New A: final M-MFPO/OBABO endpoint

This is a compact repository check entry point, not a self-contained proof file.
Run `python3 scripts/check-pbgso-standalone.py --endpoint new-a --check`.
For one Mathlib-only file containing the entire local proof closure, use
`--output /tmp/pbgso-new-a --check`. See PBGSO/README.md.

The checked endpoint constructs the process, actual Gaussian innovations,
integral references, and mesh-uniform finite-horizon constants. Its inputs are
independent globally jointly Lipschitz forces; a positive population with the
flattened Euclidean encoding; gamma >= 0; P2 initial/target laws; an actual
frozen invariant sampler; zero target mean observation; positive source A3;
and uniform reference observation variance. The target is stationary, with
zero optimizer momentum. The bound is finite-horizon O(sqrt h), not a claim
of uniform-in-time numerical mixing or arbitrary nonsmooth-force accuracy.
-/

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

#check @PBGSO.FullyConstructedMomentum.numerical_parameter_bound
#print axioms PBGSO.FullyConstructedMomentum.numerical_parameter_bound
