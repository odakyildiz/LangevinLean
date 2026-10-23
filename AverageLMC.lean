import AverageLMC.Assumptions
import AverageLMC.GradientStep
import AverageLMC.Recurrence
import AverageLMC.Complexity
import AverageLMC.GLMObstruction
import AverageLMC.GaussianObstruction
import AverageLMC.GLMCounterexample

set_option linter.style.header false

/-! # Average smoothness LMC: partial development and a source obstruction

This library does not claim a complete formalization of the supplied paper.
The deterministic lemmas and conditional scalar recurrences are checked.
The quadratic-plus-sine GLM and its Gaussian norm obstruction explain why
the printed isotropic Hessian Lipschitz bound cannot hold with the stated
dimension independent constants. See `AverageLMC/exposition/reference_audit.json`.

The actual-law convergence endpoints of Theorems 1, 2 and 3 remain unproved.
-/
