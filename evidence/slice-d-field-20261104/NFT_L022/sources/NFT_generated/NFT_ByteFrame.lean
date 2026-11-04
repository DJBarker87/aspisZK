import NFT_QBytes
set_option autoImplicit false
namespace NFT_Bytes
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted
/-- Full emitted mutable slice writer; arbitrary old bytes, no canonicality restriction. -/
theorem cm_frame (q : aspis_core.field.CM31) (out : Slice U8)
    (length : 8≤out.val.length) :
    ∃ final, aspis_core.field.CM31.write_le_bytes q out=ok final ∧ final.val=cmBytes q ++ out.val.drop 8 := by
  simp [lift,bind_tc_ok,aspis_core.field.CM31.write_le_bytes,
    aspis_core.field.M31.to_le_bytes,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.to_slice,
    Slice.len,Slice.length,cmBytes,core.num.U32.to_le_bytes,
    BitVec.toLEBytes,List.setSlice!,List.slice,length,show 4≤out.val.length by omega]


#print axioms cm_frame
end NFT_Bytes
