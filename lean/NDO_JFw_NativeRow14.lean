import JFw_HeaderCast
import NDO_JFw_Frames
import JFw_Record
import NDO_JFz_Row14
import ExtractedRecordFraming
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_NativeRow14
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical JFw_Frames
def payload : Slice U8 := expandedPayload 1 155 (by decide) (by decide)
theorem payload_length : payload.length = 32 := expanded_length 1 155 (by decide) (by decide)
theorem fields : AspisR1RecordParser.r1_wire.validate_record_fields 14#u8 payload = ok (.Ok ()) := by
  apply JFw_BlockValidation.success 1 (window 155 16).val payload 14#u8
  · exact window_length 155 16 (by decide)
  · scalar_tac
  · rw [window_bytes];exact JFz_Scan47.canonical_selected
  · exact JFw_Blocks.bytes 1 _
def record : Slice U8 := frame 3#u8 32#u8 0#u8 0#u8 0#u8 payload (by rw [payload_length];decide)
theorem source_shape : AspisR1RecordParser.r1_wire.row_shape 14#u8 = ok (some (3#u8,32#usize)) := by
  rw [ExtractedRecordFraming.parser_row_shape_table]
  rfl
theorem accepted : AspisR1PrefixAggregateParser.r1_wire.parse_record 14#u8 record = ok (.Ok payload) := by
  apply JFw_CurrentValidation.record
  apply JFw_Record.success 14#u8 3#u8 32#u8 0#u8 0#u8 0#u8 32#usize record payload source_shape (by decide) payload_length rfl
  · apply JFw_HeaderCast.eq;scalar_tac
  · intro _;exact fields
theorem bytes : bytesOf record.val = PSem_Rows.expandedRow 14 (slice JFz_RowGeometry.wire 150 6881) := by
  have head : (slice JFz_RowGeometry.wire 150 6881).take 5 = bytesOf [3#u8,32#u8,0#u8,0#u8,0#u8] := by
    rw [JFz_RowGeometry.slice_take _ 150 5 6881 (by decide)]
    simp only [slice,JFz_RowGeometry.wire,bytesOf,←List.map_drop,←List.map_take,JFz_Row14.header]
  simp only [PSem_Rows.expandedRow,JFz_Row14.shape,Prod.snd,if_pos (by decide : 14 ≤ 14),head]
  rw [JFz_RowGeometry.slice_slice _ 150 6881 5 16 (by decide)]
  have pbytes := expanded_bytes 1 155 (by decide) (by decide)
  change bytesOf ([3#u8,32#u8,0#u8,0#u8,0#u8] ++ payload.val) = _
  rw [MultiproofConeExpandModel.bytes_append]
  exact congrArg (fun tail => bytesOf [3#u8,32#u8,0#u8,0#u8,0#u8] ++ tail) pbytes
#print axioms payload_length
#print axioms fields
#print axioms source_shape
#print axioms accepted
#print axioms bytes
end AspisR1.JFw_NativeRow14
end
