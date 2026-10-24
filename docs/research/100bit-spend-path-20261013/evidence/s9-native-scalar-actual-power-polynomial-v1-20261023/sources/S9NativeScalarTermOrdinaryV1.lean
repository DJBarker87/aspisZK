import S9ActualScalarNativeReadsV1
import S9NativeDecodedScalarProductV1
set_option autoImplicit false
namespace AspisR1S9NativeScalarTermOrdinaryV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9NativeDecodedScalarProductV1
/-- Literal carrier-only identity of the existing scalar-factor contribution
and the already proved ordinary native product. No new field algebra. -/
theorem nativeTerm_eq_source_product (p : NativeW) (q : NativeQ) :
    AspisR1S9ActualScalarNativeReadsV1.nativeTerm p q=
      AspisR1FastDotsTailFieldProductRootV1.scalarProduct
        (AspisR1S9NativeInputProductWitnessV1.sourcePair (p,q)) := by rfl

theorem nativeTerm_eq_decoded_mul_embed (p : NativeW) (q : NativeQ) :
    AspisR1S9ActualScalarNativeReadsV1.nativeTerm p q=decodeNative p*scalarEmbed q :=
  (nativeTerm_eq_source_product p q).trans (native_scalar_product_eq_decoded_mul_embed p q)
#print axioms nativeTerm_eq_source_product
#print axioms nativeTerm_eq_decoded_mul_embed
end AspisR1S9NativeScalarTermOrdinaryV1
