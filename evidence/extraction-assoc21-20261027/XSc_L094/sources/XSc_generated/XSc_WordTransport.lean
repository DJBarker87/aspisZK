import XSc_RecordFieldTypes
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSc_WordTransport
/-- Symbolic four-byte bridge needed by the old aggregate decoder carrier. -/
theorem source (a b c d : U8) :
 core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])=XRn_Join_word [a,b,c,d] := by
 apply UScalar.eq_of_val_eq
 simp [core.num.U32.from_le_bytes,XRn_Join_word,XRn_Join_Bytes.le32,BitVec.fromLEBytes]
#print axioms source
end XSc_WordTransport
