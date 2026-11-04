import NGO_QRef.Funs
import NGD_QDecodeLaw
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_BitPack
#print U32.wrapping_shl
#print BitVec.fromLEBytes
run_cmd do
 for (n,ci) in (← Lean.getEnv).constants.toList do
  if n.toString.startsWith "Aeneas.Std.UScalar.eq_of_bv" ||
     n.toString.startsWith "Aeneas.Std.UScalar.ofBitVec_val" then
   Lean.logInfo m!"{n}: {ci.type}"
/-- Four arbitrary bytes; no concrete enumeration or decoder success premise. -/
theorem pack (a b c d : U8) :
    (core.convert.num.FromU32U8.from a |||
      U32.wrapping_shl (core.convert.num.FromU32U8.from b) 8#u32 |||
      U32.wrapping_shl (core.convert.num.FromU32U8.from c) 16#u32 |||
      U32.wrapping_shl (core.convert.num.FromU32U8.from d) 24#u32) =
    core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d]) := by
  apply UScalar.eq_of_val_eq
  simp only [U32.wrapping_shl,UScalar.wrapping_shl,UScalar.or,
    core.convert.num.FromU32U8.from,core.num.U32.from_le_bytes,Array.make,List.map_cons,List.map_nil]
  trace_state
  bv_decide
#print axioms pack
end NGO_BitPack
