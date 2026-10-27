import CheckpointP6EncodeK
import CheckpointBytesETotal
set_option autoImplicit false
namespace AspisR1.LPi_WriterValues
open Aeneas Aeneas.Std Result OraclePortCkptAbi2Extracted

def cbytes (x : aspis_core.field.CM31) : List U8 :=
  (core.num.U32.to_le_bytes x.a).val ++ (core.num.U32.to_le_bytes x.b).val

/-- Arbitrary initial bytes in the exact eight-byte mutable caller slice. -/
theorem cm_writer (x : aspis_core.field.CM31) (out : Slice U8)
    (size : out.val.length = 8) :
    ∃ z, aspis_core.field.CM31.write_le_bytes x out = ok z ∧ z.val = cbytes x := by
  simp [lift,bind_tc_ok,aspis_core.field.CM31.write_le_bytes,
    aspis_core.field.M31.to_le_bytes,core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.to_slice,Slice.len,Slice.length,
    cbytes,core.num.U32.to_le_bytes,BitVec.toLEBytes,List.setSlice!,List.slice,size]

theorem qm_writer (x : aspis_core.field.QM31) (out : Slice U8)
    (size : out.val.length = 16) :
    ∃ z, aspis_core.field.QM31.write_le_bytes x out = ok z ∧
      z.val = CheckpointP6EncodeK.bytes x := by
  simp [lift,bind_tc_ok,aspis_core.field.QM31.write_le_bytes,
    aspis_core.field.CM31.write_le_bytes,aspis_core.field.M31.to_le_bytes,
    core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.to_slice,Slice.len,Slice.length,
    CheckpointP6EncodeK.bytes,core.num.U32.to_le_bytes,BitVec.toLEBytes,
    List.setSlice!,List.slice,size]

#print axioms qm_writer
#print axioms cm_writer
end AspisR1.LPi_WriterValues
