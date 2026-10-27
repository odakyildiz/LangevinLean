import AverageLMC.Assumptions
import AverageLMC.GradientStep
import AverageLMC.Recurrence
import AverageLMC.Complexity
import AverageLMC.Theorem
import AverageLMC.SGLDTheorem
import AverageLMC.LaplacianTheorem

set_option linter.style.header false

/-! # Average-smoothness sampling laws

The main convergence statements are developed for the actual Gaussian LMC
and finite-index control-variate SGLD laws, using the exact source constants.
The source audit records their individual status and the separate scope of
auxiliary lemmas outside the main sampling results.
-/
