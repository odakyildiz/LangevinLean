import UnadjustedLangevin.ProductBrownian
import IPLA.ProductReference
import IPLA.BrownianReference
import IPLA.ULAAdapter

set_option linter.style.header false

/-! # Compatibility exports for the shared ULA ProductBrownian module

All generic implementation and proofs live in
`UnadjustedLangevin.ProductBrownian`, under `ULA.Hilbert`.
These aliases preserve the earlier IPLA API without duplicating its proofs.
-/

namespace IPLA

export ULA.Hilbert (
  preBrownian_comp_measurePreserving
  brownianCoordinatesLp_pullback
  brownianEulerNoise_pullback
  sourceEulerNoise
  sourceEulerNoise_memLp
  sourceEulerNoise_coe
  sourceEulerNoise_coordinate_coe
  sourceEulerNoise_coordinate_coe_nnreal
  sourceEulerNoise_normalized_coordinate
  sourceEulerNoise_coordinateLaw
  sourceEulerNoise_independent
  productPreBrownian
  productNoise_eq_brownianEulerNoise
  productEulerNoise_coordinateLaw
  productEulerNoise_independent
  productEulerNoise_independentInitial
  productGibbsMemLp
  brownianProductL2Reference
  productReference_of_constructed_brownian
  dalalyan_of_constructed_product_brownian)

end IPLA
