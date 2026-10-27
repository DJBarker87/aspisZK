import FIo_NativeFuns
import JGi_QRawSourceForwardTotalityV1
set_option autoImplicit false
namespace AspisR1.LPi_RawAssociation
open Aeneas Aeneas.Std Result

theorem source_eq (a b : FIo_Native.fast_pairing.canonical.Q) :
    FIo_Native.fast_pairing.canonical.Q.raw a b =
      AspisR1CanonicalQRawUnified.canonical.Q.raw a b := by
  simp only [FIo_Native.fast_pairing.canonical.Q.raw,FIo_QRaw.canonical.Q.raw,
    AspisR1CanonicalQRawUnified.canonical.Q.raw,
    FIo_QRaw.canonical.Q.raw.PP,AspisR1CanonicalQRawUnified.canonical.Q.raw.PP,
    FIo_QRaw.canonical.P,AspisR1CanonicalQRawUnified.canonical.P]
  rfl

#print axioms source_eq
end AspisR1.LPi_RawAssociation
