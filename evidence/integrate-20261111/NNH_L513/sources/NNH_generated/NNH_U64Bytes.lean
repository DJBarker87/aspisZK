import NNH_AuthSeeds
set_option autoImplicit false
namespace NNH_U64Bytes
open Aeneas Aeneas.Std AdapterRw NND_Carrier

theorem value (x : U64) :
 bytes (Array.to_slice (core.num.U64.to_le_bytes x))=RSL.u64le (slot x) := by
 simp only [bytes,Array.to_slice,core.num.U64.to_le_bytes,RSL.u64le,slot,byte]
 simp only [BitVec.toLEBytes,List.map_map,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil]
 congr 1 <;> bv_decide
#print axioms value
end NNH_U64Bytes
