import R1Z.ProverRwDictionaryBytesSource
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteWord72
open Aeneas Aeneas.Std

theorem complete (x : U32) : core.num.U32.from_le_bytes (core.num.U32.to_le_bytes x)=x := by
  cases x with
  | mk word =>
    apply congrArg UScalar.mk
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_cast,U8.bv,U32.bv,List.map_map,Function.comp_def,List.map_id]
    rw [BitVec.fromLEBytes_toLEBytes (by decide)]
    rfl

#print axioms complete
end R1Z.PV_RunJoin_ByteWord72
