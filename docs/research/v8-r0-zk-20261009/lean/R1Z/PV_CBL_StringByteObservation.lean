import R1Z.PV_CBL_StringByteRoundtrip
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_StringByteObservation
open PV_CBL_StringBytesAdapter
set_option autoImplicit false
/-- Transport exact byte equality, with no ignored error/result branch. -/
theorem decode_of_bytes (native : String) (bytes : alloc.vec.Vec U8)
    (h : bytes.val=encodeList native) : decode bytes=ok native := by
  simp only [decode,h,PV_CBL_StringByteRoundtrip.array_roundtrip]
  simp only [String.fromUTF8?,dif_pos native.isValidUTF8]
  first | rfl | skip
#print axioms decode_of_bytes
end R1Z.PV_CBL_StringByteObservation
