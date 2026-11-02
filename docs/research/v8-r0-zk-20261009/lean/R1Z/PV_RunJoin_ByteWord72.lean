import R1Z.ProverRwDictionaryBytesSource
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteWord72
open Aeneas Aeneas.Std

theorem complete (x : U32) : core.num.U32.from_le_bytes (core.num.U32.to_le_bytes x)=x := by
  have mapped (xs : List (BitVec 8)) :
      List.map U8.bv (List.map (fun b : BitVec 8 => (UScalar.mk b : U8)) xs)=xs := by
    induction xs with
    | nil => rfl
    | cons b bs ih =>
      change b::List.map U8.bv (List.map (fun c : BitVec 8 => (UScalar.mk c : U8)) bs)=b::bs
      rw [ih]
  cases x with
  | mk word =>
    unfold core.num.U32.from_le_bytes core.num.U32.to_le_bytes
    apply congrArg UScalar.mk
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_cast,U8.bv,U32.bv,List.map_map,Function.comp_def,List.map_id]
    rw [mapped]
    rw [BitVec.fromLEBytes_toLEBytes (by decide : UScalarTy.U32.numBits%8=0) word]
    rfl

#print axioms complete
end R1Z.PV_RunJoin_ByteWord72
