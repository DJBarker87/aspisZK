import NNH_ToLEBytes8
set_option autoImplicit false
namespace NNH_U64BytesKernel
open Aeneas Aeneas.Std AdapterRw NND_Carrier

theorem value (x : U64) :
 bytes (Array.to_slice (core.num.U64.to_le_bytes x))=RSL.u64le (slot x) := by
 simp only [bytes,Array.to_slice,core.num.U64.to_le_bytes,RSL.u64le,slot,byte]
 simp only [NNH_ToLEBytes8.expand,List.map_map,List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,List.nil_append,List.cons_append]
 simp only [List.cons.injEq,List.nil_append]
 repeat' constructor
 all_goals simp only [byte,Nat.toUInt64,UInt64.ofNat,U8.bv,UScalar.bv]
 all_goals apply UInt8.eq_of_toBitVec_eq
 all_goals simp only [UInt64.toBitVec_toUInt8,UInt64.toBitVec_shiftRight,UInt64.toBitVec_ofNat']
 all_goals apply BitVec.eq_of_getLsbD_eq_iff.mpr
 all_goals intro i hi
 all_goals interval_cases i
 all_goals simp [BitVec.getLsbD_setWidth,BitVec.getLsbD_extractLsb',BitVec.getLsbD_ushiftRight,BitVec.ushiftRight_eq']
#print axioms value
end NNH_U64BytesKernel
