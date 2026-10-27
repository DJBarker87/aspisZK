import XSc_RecordFieldTypes
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSc_WordTransport
/-- Symbolic four-byte bridge needed by the old aggregate decoder carrier. -/
theorem source (a b c d : U8) :
 core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])=XRn_Join_word [a,b,c,d] := by
 apply UScalar.eq_of_val_eq
 change (BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv]).toNat = (XRn_Join_word [a,b,c,d]).val
 simp [BitVec.fromLEBytes,BitVec.toNat_append,XRn_Join_word,XRn_Join_Bytes.le32]

#print axioms source
end XSc_WordTransport
