import NFQ_STAGE2_IMPORT
set_option autoImplicit false
namespace NFT_Bytes
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted

def cmBytes (q : aspis_core.field.CM31) : List U8 :=
  (core.num.U32.to_le_bytes q.a).val ++ (core.num.U32.to_le_bytes q.b).val

def qmBytes (q : aspis_core.field.QM31) : List U8 :=
  cmBytes q.c0 ++ cmBytes q.c1

/-- Full emitted mutable slice writer; arbitrary old bytes, no canonicality restriction. -/
theorem cm_value (q : aspis_core.field.CM31) (out : Slice U8)
    (length : out.val.length=8) :
    ∃ final, aspis_core.field.CM31.write_le_bytes q out=ok final ∧ final.val=cmBytes q := by
  simp [lift,bind_tc_ok,aspis_core.field.CM31.write_le_bytes,
    aspis_core.field.M31.to_le_bytes,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.to_slice,
    Slice.len,Slice.length,cmBytes,core.num.U32.to_le_bytes,
    BitVec.toLEBytes,List.setSlice!,List.slice,length]

#print axioms cm_value
end NFT_Bytes
