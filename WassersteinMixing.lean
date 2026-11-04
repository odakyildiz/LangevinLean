import WassersteinMixing.Theorem
import WassersteinMixing.IPLA
import WassersteinMixing.IPLATheorem

set_option linter.style.header false

/-! # Wasserstein mixing for ordinary Gaussian ULA

The exact source bias, convergence, and accuracy bounds follow from the
original twice continuously differentiable potential and Hessian bounds.
The stationary diffusion, reversible semigroup, Poisson corrector, synchronous
comparison, ULA invariant law, and transport geometry are constructed.
The IPLA application proves a linear-step parameter rate for the actual
Gaussian particle algorithm, with explicit accuracy and comparison bounds,
also stated with Project 03's binders and fully written right-hand sides.
-/
