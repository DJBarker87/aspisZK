import NFT_Bytes
set_option autoImplicit false
namespace NFT_Bytes
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted
/-- Full emitted mutable slice writer; arbitrary old bytes, no canonicality restriction. -/
theorem qm_value (q : aspis_core.field.QM31) (out : Slice U8)
    (length : out.val.length=16) :
    ∃ final, aspis_core.field.QM31.write_le_bytes q out=ok final ∧ final.val=qmBytes q := by
  simp [lift,bind_tc_ok,aspis_core.field.QM31.write_le_bytes,aspis_core.field.CM31.write_le_bytes,
    aspis_core.field.M31.to_le_bytes,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.to_slice,
    Slice.len,Slice.length,qmBytes,cmBytes,core.num.U32.to_le_bytes,
    BitVec.toLEBytes,List.setSlice!,List.slice,length]


#print axioms qm_value
end NFT_Bytes
