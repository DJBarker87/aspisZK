import OraclePortCkptAbi5Codec

set_option autoImplicit false
namespace AspisR1.CheckpointP6EncodeK
open Aeneas Aeneas.Std Result
open OraclePortCkptAbi2Extracted

def bytes (q : aspis_core.field.QM31) : List U8 :=
  (core.num.U32.to_le_bytes q.c0.a).val ++
  (core.num.U32.to_le_bytes q.c0.b).val ++
  (core.num.U32.to_le_bytes q.c1.a).val ++
  (core.num.U32.to_le_bytes q.c1.b).val

/-- The actual emitted nested mutable writer, with all checked sub-slices
and back-writes; every raw U32 word is allowed. -/
theorem encode_k_total (q : aspis_core.field.QM31) :
    ∃ out, encode_k q=ok out ∧ out.val=bytes q := by
  simp [lift, bind_tc_ok, encode_k,aspis_core.field.QM31.write_le_bytes,
    aspis_core.field.CM31.write_le_bytes,aspis_core.field.M31.to_le_bytes,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.to_slice_mut,Array.to_slice,
    Array.from_slice,Array.repeat,Slice.len,Slice.length,bytes,
    core.num.U32.to_le_bytes,BitVec.toLEBytes,List.setSlice!,List.slice]

#print axioms encode_k_total
end AspisR1.CheckpointP6EncodeK
