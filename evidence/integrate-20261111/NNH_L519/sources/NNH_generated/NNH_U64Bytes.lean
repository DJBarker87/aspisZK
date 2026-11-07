import NNH_AuthSeeds
set_option autoImplicit false
namespace NNH_U64Bytes
open Aeneas Aeneas.Std AdapterRw NND_Carrier

theorem value (x : U64) :
 bytes (Array.to_slice (core.num.U64.to_le_bytes x))=RSL.u64le (slot x) := by
 simp only [bytes,Array.to_slice,core.num.U64.to_le_bytes,RSL.u64le,slot,byte]
 simp only [BitVec.toLEBytes.eq_1,Nat.reduceLT,Nat.reduceSub,if_true,if_false,List.map_map,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append]
 simp only [List.cons.injEq,List.nil_append]
 repeat' constructor
 all_goals bv_decide
#print axioms value
end NNH_U64Bytes
