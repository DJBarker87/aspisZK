import JFw_HeaderCast
import NDO_JFw_Frames
import JFw_Record
import NDO_JFz_Row02
import ExtractedRecordFraming
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_NativeRow02
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical JFw_Frames
def payload : Slice U8 := window 63 32
theorem payload_length : payload.length = 32 := window_length 63 32 (by decide)
def record : Slice U8 := frame 1#u8 32#u8 0#u8 0#u8 0#u8 payload (by rw [payload_length];decide)
theorem source_shape : AspisR1RecordParser.r1_wire.row_shape 2#u8 = ok (some (1#u8,32#usize)) := by
  rw [ExtractedRecordFraming.parser_row_shape_table]
  rfl
theorem accepted : AspisR1PrefixAggregateParser.r1_wire.parse_record 2#u8 record = ok (.Ok payload) := by
  apply JFw_CurrentValidation.record
  apply JFw_Record.success 2#u8 1#u8 32#u8 0#u8 0#u8 0#u8 32#usize record payload source_shape (by decide) payload_length rfl
  · apply JFw_HeaderCast.eq;scalar_tac
  · intro h;scalar_tac
theorem bytes : bytesOf record.val = PSem_Rows.expandedRow 2 (slice JFz_RowGeometry.wire 58 6973) := by
  have head : (slice JFz_RowGeometry.wire 58 6973).take 5 = bytesOf [1#u8,32#u8,0#u8,0#u8,0#u8] := by
    rw [JFz_RowGeometry.slice_take _ 58 5 6973 (by decide)]
    simp only [slice,JFz_RowGeometry.wire,bytesOf,←List.map_drop,←List.map_take,JFz_Row02.header]
  simp only [PSem_Rows.expandedRow,JFz_Row02.shape,Prod.snd,if_neg (by decide : ¬ 14 ≤ 2),head]
  rw [JFz_RowGeometry.slice_slice _ 58 6973 5 32 (by decide)]
  change bytesOf ([1#u8,32#u8,0#u8,0#u8,0#u8] ++ payload.val) = _
  rw [MultiproofConeExpandModel.bytes_append,payload,window_bytes]
#print axioms payload_length
#print axioms source_shape
#print axioms accepted
#print axioms bytes
end AspisR1.JFw_NativeRow02
end
