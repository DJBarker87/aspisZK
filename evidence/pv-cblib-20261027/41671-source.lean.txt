import R1Z.PV_CBL_StringBytesAdapter
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_StringByteRoundtrip
open PV_CBL_StringBytesAdapter
set_option autoImplicit false
theorem list_roundtrip (s : String) :
    (encodeList s).map decodeByte = s.toByteArray.data.toList := by
  simp [encodeList,List.map_map,Function.comp_def,byte_roundtrip]
theorem array_roundtrip (s : String) :
    ((encodeList s).map decodeByte).toArray = s.toByteArray.data := by
  rw [list_roundtrip]
theorem decode_encode (s : String) (h : (encodeList s).length ≤ Usize.max) :
    (do let v ← encode s; decode v) = ok s := by
  simp only [encode,dif_pos h,bind_tc_ok,decode,array_roundtrip]
  simp only [String.fromUTF8?,dif_pos s.isValidUTF8]
  first | rfl | skip
#print axioms list_roundtrip
#print axioms array_roundtrip
#print axioms decode_encode
end R1Z.PV_CBL_StringByteRoundtrip
