import UnadjustedLangevin.ULAFromBrownian
import IPLA.BrownianReference

set_option linter.style.header false

/-! # Compatibility exports for the shared ULA ULAFromBrownian module

All generic implementation and proofs live in
`UnadjustedLangevin.ULAFromBrownian`, under `ULA.Hilbert`.
These aliases preserve the earlier IPLA API without duplicating its proofs.
-/

namespace IPLA

export ULA.Hilbert (
  dalalyan_of_constructed_brownian_reference)

end IPLA
