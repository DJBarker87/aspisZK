import NHE_DotState
import NFE_NFC_RawAssociation
set_option autoImplicit false
namespace NHE_DotRaw
open Aeneas Aeneas.Std Result AspisR1

theorem raw (a b : FIo_Native.fast_pairing.canonical.Q) :
 FIo_Native.fast_pairing.canonical.Q.raw a b=
 AspisR1EbyKPushDecodedProductUpdate.QRaw a b := by
 rw [NFE_NFC_RawAssociation.source_eq]
 rfl

#print axioms raw
end NHE_DotRaw
