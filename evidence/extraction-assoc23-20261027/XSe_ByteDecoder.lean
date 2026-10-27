import XSe_KitBytes
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_ByteDecoder
/-- Complete arbitrary-input byte decoder equality, including wrong lengths. -/
theorem source (s : Slice U8) :
 XSc_RecordByteLength.mapped s=
 _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes s := by
 by_cases size : s.val.length=32
 · exact (XSe_OldBytes.source s size).trans (XSe_KitBytes.source s size).symm
 · exact XSc_RecordByteLength.source s size
#print axioms source
end XSe_ByteDecoder
