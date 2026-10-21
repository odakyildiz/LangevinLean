import UnadjustedLangevin.BrownianReference
import IPLA.Dalalyan

set_option linter.style.header false

/-! # Compatibility exports for the shared ULA BrownianReference module

All generic implementation and proofs live in
`UnadjustedLangevin.BrownianReference`, under `ULA.Hilbert`.
These aliases preserve the earlier IPLA API without duplicating its proofs.
-/

namespace IPLA

export ULA.Hilbert (
  brownianSegmentFrom
  brownianSegmentFrom_spec
  brownianKnots
  brownianSegments
  brownianSegments_start
  brownianSegments_initial
  brownianEulerNoise
  brownianEulerNoise_endpoint
  brownianReference
  brownianReference_of_strongConvex)

end IPLA
