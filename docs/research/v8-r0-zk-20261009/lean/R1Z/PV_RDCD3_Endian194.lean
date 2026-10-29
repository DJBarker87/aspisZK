import Aeneas

namespace R1Z.PV_RDCD3_Endian194
set_option autoImplicit false
open Aeneas Aeneas.Std

/-- Owned little-endian word interpretation: all four bytes and their order
are retained. Native from_ne_bytes/transmute at the recorded little-endian
1.94.1 target is the existing integer-layout/compiler primitive boundary. -/
def word (bytes : Array U8 4#usize) : U32 :=
  (BitVec.cast (by
    have h := bytes.property
    simp_all [UScalarTy.numBits])
    (BitVec.fromLEBytes (bytes.val.map U8.bv)))#uscalar

/-- Exact imported byte-vector interface, not a test on selected byte values. -/
theorem binding (bytes : Array U8 4#usize) :
    word bytes = core.num.U32.from_le_bytes bytes := rfl

#print axioms binding
end R1Z.PV_RDCD3_Endian194
