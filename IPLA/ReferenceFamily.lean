import UnadjustedLangevin.ReferenceFamily
import IPLA.Dalalyan

set_option linter.style.header false

/-! # Compatibility exports for the shared ULA ReferenceFamily module

All generic implementation and proofs live in
`UnadjustedLangevin.ReferenceFamily`, under `ULA.Hilbert`.
These aliases preserve the earlier IPLA API without duplicating its proofs.
-/

namespace IPLA

export ULA.Hilbert (
  FiniteCoupling
  ReferenceFamily
  dalalyan_small_step_of_reference_family)

namespace ReferenceFamily
export ULA.Hilbert.ReferenceFamily (output_finite)
end ReferenceFamily

end IPLA
