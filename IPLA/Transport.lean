import UnadjustedLangevin.Projection

set_option linter.style.header false

/-! # Compatibility exports for the shared ULA projection estimates

All generic quadratic-transport and projection implementation lives in
`UnadjustedLangevin.Projection`, under `ULA.Hilbert`.
IPLA reuses those estimates when projecting its lifted chain to the parameter.
-/

namespace IPLA

export ULA.Hilbert (
  projectedRMS
  projectedRMSReal
  projectedDifference_le
  projectedRMS_le_coupling
  projectedRMS_le_wasserstein2
  projectedRMS_ne_top
  projectedRMSReal_eq_sqrt_integral
  projectedRMS_le_of_secondMoment
  projectedRMSReal_le_wasserstein2Real_add)

end IPLA
