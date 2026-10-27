import Aeneas
set_option autoImplicit false
namespace AspisR1.LPr_WordValue
open Aeneas Aeneas.Std

/-- Four arbitrary native bytes; no canonical-field or decoder-success premise. -/
theorem bits (a b c d : U8) :
    (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).bv =
      d.bv ++ c.bv ++ b.bv ++ a.bv := by
  simp only [core.num.U32.from_le_bytes, Array.make, List.map_cons, List.map_nil]
  simp only [BitVec.fromLEBytes, List.length_cons, List.length_nil]
  bv_decide

#print axioms bits
end AspisR1.LPr_WordValue
