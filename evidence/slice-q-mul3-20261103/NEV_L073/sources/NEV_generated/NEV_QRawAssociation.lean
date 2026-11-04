import NEV_QRaw.Funs
import LPi_RawAssociation
import LPi_RawValues
set_option autoImplicit false
noncomputable section
namespace NEV_QRawAssociation
open Aeneas Aeneas.Std Result AspisR1
/-- New actual frozen raw extraction is the SAME already adopted raw function.
All arithmetic proofs are retained; no multiplication is asked of Kani. -/
theorem actual (a b : NEV_QRaw.fast_pairing.canonical.Q) :
    NEV_QRaw.fast_pairing.canonical.Q.raw a b =
      FIo_Native.fast_pairing.canonical.Q.raw a b := by rfl

theorem cohort (a b : NEV_QRaw.fast_pairing.canonical.Q) :
    NEV_QRaw.fast_pairing.canonical.Q.raw a b =
      AspisR1CanonicalQRawUnified.canonical.Q.raw a b :=
  (actual a b).trans (LPi_RawAssociation.source_eq a b)

#print axioms actual
#print axioms cohort
end NEV_QRawAssociation
end
