import UnadjustedLangevin.HilbertDalalyan

set_option linter.style.header false

/-! # Compatibility exports for the shared ULA Dalalyan module

All generic implementation and proofs live in
`UnadjustedLangevin.HilbertDalalyan`, under `ULA.Hilbert`.
These aliases preserve the earlier IPLA API without duplicating its proofs.
-/

namespace IPLA

export ULA.Hilbert (
  lpChain
  lpChain_succ
  L2Reference
  l2_reference_bound
  dalalyan_small_step_of_integral_reference
  dalalyan_large_step_of_integral_reference)

end IPLA
