import NFT_ByteFrame
set_option autoImplicit false
namespace NFT_Bytes
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted
/-- Full emitted mutable slice writer; arbitrary old bytes, no canonicality restriction. -/
theorem qm_frame (q : aspis_core.field.QM31) (out : Slice U8)
    (length : 16≤out.val.length) :
    ∃ final, aspis_core.field.QM31.write_le_bytes q out=ok final ∧ final.val=qmBytes q ++ out.val.drop 16 := by
  simp [lift,bind_tc_ok,aspis_core.field.QM31.write_le_bytes,aspis_core.field.CM31.write_le_bytes,
    aspis_core.field.M31.to_le_bytes,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.to_slice,
    Slice.len,Slice.length,qmBytes,cmBytes,core.num.U32.to_le_bytes,
    BitVec.toLEBytes,List.setSlice!,List.slice,length,show 8≤out.val.length by omega,show 4≤out.val.length by omega,show min 8 (out.val.length-8)=8 from Nat.min_eq_left (by omega),show min 4 (out.val.length-4)=4 from Nat.min_eq_left (by omega),show min 4 (out.val.length-12)=4 from Nat.min_eq_left (by omega)]



#print axioms qm_frame
end NFT_Bytes
