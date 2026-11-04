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
  change (((a.bv.setWidth 32 ||| (b.bv.setWidth 32).shiftLeft 8) |||
    (c.bv.setWidth 32).shiftLeft 16) ||| (d.bv.setWidth 32).shiftLeft 24).toNat =
      (BitVec.fromLEBytes [a.bv,b.bv,c.bv,d.bv]).toNat
  apply congrArg BitVec.toNat
  simp only [BitVec.fromLEBytes,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  by_cases h8 : i<8 <;> by_cases h16 : i<16 <;>
    by_cases h24 : i<24 <;> by_cases h32 : i<32 <;>
    simp (disch := omega) [h8,h16,h24,h32,BitVec.getLsbD_or,BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth,Nat.sub_sub,Nat.add_comm]
#print axioms pack
end NGO_BitPack
