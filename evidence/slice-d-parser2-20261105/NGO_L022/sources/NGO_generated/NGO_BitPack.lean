import NGO_QRef.Funs
import NGD_QDecodeLaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_BitPack
/-- Four arbitrary bytes; no concrete enumeration or decoder success premise. -/
theorem pack (a b c d : U8) :
    (core.convert.num.FromU32U8.from a |||
      U32.wrapping_shl (core.convert.num.FromU32U8.from b) 8#u32 |||
      U32.wrapping_shl (core.convert.num.FromU32U8.from c) 16#u32 |||
      U32.wrapping_shl (core.convert.num.FromU32U8.from d) 24#u32) =
    core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d]) := by
  apply UScalar.eq_of_val_eq
  change ((((a.bv.setWidth 32 ||| (b.bv.setWidth 32).shiftLeft 8) |||
    (c.bv.setWidth 32).shiftLeft 16) ||| (d.bv.setWidth 32).shiftLeft 24).toNat =
      (BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv]).toNat
  apply congrArg BitVec.toNat
  simp only [BitVec.fromLEBytes]
  bv_decide
#print axioms pack
end NGO_BitPack
