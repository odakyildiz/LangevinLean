import UnadjustedLangevin.ProductReference
import IPLA.Dalalyan

set_option linter.style.header false

/-! # Compatibility exports for the shared ULA ProductReference module

All generic implementation and proofs live in
`UnadjustedLangevin.ProductReference`, under `ULA.Hilbert`.
These aliases preserve the earlier IPLA API without duplicating its proofs.
-/

namespace IPLA

export ULA.Hilbert (
  pointwiseUpdate
  pointwiseUpdate_measurable
  productNoise_memLp
  productNoise
  productNoise_coe
  productOutputLaw
  product_chain_coe
  product_chain_outputLaw
  ProductReference
  dalalyan_small_step_of_product_reference)

namespace ProductReference
export ULA.Hilbert.ProductReference (output_finite)
end ProductReference

end IPLA
