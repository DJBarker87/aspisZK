import NEV_QRawMaps
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
      FIo_Native.fast_pairing.canonical.Q.raw a b := by
  obtain ⟨a0,a1,a2,a3,ha⟩ := LPf_ArrayFour.shape a
  obtain ⟨b0,b1,b2,b3,hb⟩ := LPf_ArrayFour.shape b
  subst a;subst b
  simp only [FIo_Native.fast_pairing.canonical.Q.raw,FIo_QRaw.canonical.Q.raw,
    NEV_QRaw.fast_pairing.canonical.Q.raw,NEV_QRawMaps.left,NEV_QRawMaps.right,bind_tc_ok,
    NEV_QRawMaps.fold]
  simp only [NEV_QRaw.fast_pairing.canonical.Q.raw.PP,FIo_QRaw.canonical.Q.raw.PP,
    NEV_QRaw.fast_pairing.canonical.P,FIo_QRaw.canonical.P]
  rfl

theorem cohort (a b : NEV_QRaw.fast_pairing.canonical.Q) :
    NEV_QRaw.fast_pairing.canonical.Q.raw a b =
      AspisR1CanonicalQRawUnified.canonical.Q.raw a b :=
  (actual a b).trans (LPi_RawAssociation.source_eq a b)

#print axioms actual
#print axioms cohort
end NEV_QRawAssociation
end
