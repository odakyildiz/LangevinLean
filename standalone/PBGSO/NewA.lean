import PBGSO.FullyUniformMomentum

/-!
# Theorem New A: time-uniform actual particle implementation bound

Repository verification entry point. For a Mathlib-only single file containing
its complete exact proof closure, run:
  python3 scripts/check-pbgso-standalone.py --endpoint new-a --output /tmp/pbgso-new-a --check

The final endpoint constructs its physical particle process, actual Gaussian
coupling, A3 contracting metric, exact restarts, local consistency coefficients,
and time-uniform reference moments. Independent globally jointly Lipschitz
forces, finite-dimensional optimiser/sampler coordinates, physical coefficient
signs, positive particle count/rate, P2 initial/target laws, an actual frozen
invariant trajectory with zero mean observation, and A5 are explicit.

The final error is D*sqrt(h) plus the original continuous relaxation and
particle floor for every iteration, for 0<h<=h_max. The constructed D and
positive h_max depend only on the fixed data, never h,n or a time horizon.
Their dependence on N is not asserted uniform. No numerical contractivity,
local-defect, uniform-moment, reference-matching or error-recurrence conclusion
is assumed. The target is the stationary critical point of the forces used.
-/

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

#check @PBGSO.FullyUniformMomentum.numerical_parameter_bound
#print axioms PBGSO.FullyUniformMomentum.numerical_parameter_bound
