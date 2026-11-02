import R1Z.ProverRwDictionaryBytesSource
import Std.Tactic.BVDecide
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteWord72
open Aeneas Aeneas.Std

theorem complete (x : U32) : core.num.U32.from_le_bytes (core.num.U32.to_le_bytes x)=x := by
  cases x with
  | mk word =>
    apply congrArg UScalar.mk
    simp only [core.num.U32.from_le_bytes,core.num.U32.to_le_bytes,
      List.map_map,Function.comp_def,BitVec.fromLEBytes,BitVec.toLEBytes]
    all_goals bv_decide

#print axioms complete
end R1Z.PV_RunJoin_ByteWord72
