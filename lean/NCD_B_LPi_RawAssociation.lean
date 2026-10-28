-- Inherited body, import-only deployed-cohort retarget.
import RPz7_FIo_NativeFuns
import LPi_RawCallbacks
set_option autoImplicit false
namespace AspisR1.LPi_RawAssociation
open Aeneas Aeneas.Std Result

theorem source_eq (a b : FIo_Native.fast_pairing.canonical.Q) :
    FIo_Native.fast_pairing.canonical.Q.raw a b =
      AspisR1CanonicalQRawUnified.canonical.Q.raw a b := by
  simp only [FIo_Native.fast_pairing.canonical.Q.raw,FIo_QRaw.canonical.Q.raw,
    AspisR1CanonicalQRawUnified.canonical.Q.raw,LPi_RawCallbacks.left,
    LPi_RawCallbacks.right,LPi_RawCallbacks.pp,LPi_RawCallbacks.fold_callback,
    FIo_QRaw.canonical.P,AspisR1CanonicalQRawUnified.canonical.P]

#print axioms source_eq
end AspisR1.LPi_RawAssociation
