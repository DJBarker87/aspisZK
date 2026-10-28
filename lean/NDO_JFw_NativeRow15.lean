import JFw_HeaderCast
import NDO_JFw_Frames
import JFw_Record
import NDO_JFz_Row15
import ExtractedRecordFraming
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_NativeRow15
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical JFw_Frames
def payload : Slice U8 := expandedPayload 28 176 (by decide) (by decide)
theorem payload_length : payload.length = 896 := expanded_length 28 176 (by decide) (by decide)
theorem fields : AspisR1RecordParser.r1_wire.validate_record_fields 15#u8 payload = ok (.Ok ()) := by
  apply JFw_BlockValidation.success 28 (window 176 448).val payload 15#u8
  · exact window_length 176 448 (by decide)
  · scalar_tac
  · rw [window_bytes];exact JFz_Scan48.canonical_selected
  · exact JFw_Blocks.bytes 28 _
def record : Slice U8 := frame 2#u8 128#u8 3#u8 0#u8 0#u8 payload (by rw [payload_length];decide)
theorem source_shape : AspisR1RecordParser.r1_wire.row_shape 15#u8 = ok (some (2#u8,896#usize)) := by
  rw [ExtractedRecordFraming.parser_row_shape_table]
  rfl
theorem accepted : AspisR1PrefixAggregateParser.r1_wire.parse_record 15#u8 record = ok (.Ok payload) := by
  apply JFw_CurrentValidation.record
  apply JFw_Record.success 15#u8 2#u8 128#u8 3#u8 0#u8 0#u8 896#usize record payload source_shape (by decide) payload_length rfl
  · apply JFw_HeaderCast.eq;scalar_tac
  · intro _;exact fields
theorem bytes : bytesOf record.val = PSem_Rows.expandedRow 15 (slice JFz_RowGeometry.wire 171 6860) := by
  have head : (slice JFz_RowGeometry.wire 171 6860).take 5 = bytesOf [2#u8,128#u8,3#u8,0#u8,0#u8] := by
    rw [JFz_RowGeometry.slice_take _ 171 5 6860 (by decide)]
    simp only [slice,JFz_RowGeometry.wire,bytesOf,←List.map_drop,←List.map_take,JFz_Row15.header]
  simp only [PSem_Rows.expandedRow,JFz_Row15.shape,Prod.snd,if_pos (by decide : 14 ≤ 15),head]
  rw [JFz_RowGeometry.slice_slice _ 171 6860 5 448 (by decide)]
  have pbytes := expanded_bytes 28 176 (by decide) (by decide)
  change bytesOf ([2#u8,128#u8,3#u8,0#u8,0#u8] ++ payload.val) = _
  rw [MultiproofConeExpandModel.bytes_append]
  exact congrArg (fun tail => bytesOf [2#u8,128#u8,3#u8,0#u8,0#u8] ++ tail) pbytes
#print axioms payload_length
#print axioms fields
#print axioms source_shape
#print axioms accepted
#print axioms bytes
end AspisR1.JFw_NativeRow15
end
