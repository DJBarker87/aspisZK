import Aeneas
set_option autoImplicit false
namespace AspisR1.LPr_WordValue
open Aeneas Aeneas.Std

/-- Four arbitrary native bytes; no canonical-field or decoder-success premise. -/
theorem bits (a b c d : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).bv =
      d.bv ++ c.bv ++ b.bv ++ a.bv := by
  change (BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv] : BitVec 32) = _
  ext i hi
  interval_cases i <;>
    simp [BitVec.fromLEBytes_getElem, BitVec.getElem_append,
      BitVec.getElem_eq_testBit_toNat, Byte.testBit]

#print axioms bits
end AspisR1.LPr_WordValue
