import JFw_HeaderCast
import NDO_JFw_Frames
import JFw_Record
import NDO_JFz_Row25
import ExtractedRecordFraming
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_NativeRow25
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical JFw_Frames
def payload : Slice U8 := expandedPayload 116 4706 (by decide) (by decide)
theorem payload_length : payload.length = 3712 := expanded_length 116 4706 (by decide) (by decide)
theorem fields : AspisR1RecordParser.r1_wire.validate_record_fields 25#u8 payload = ok (.Ok ()) := by
  apply JFw_BlockValidation.success 116 (window 4706 1856).val payload 25#u8
  · exact window_length 4706 1856 (by decide)
  · scalar_tac
  · rw [window_bytes];exact JFz_Scan58.canonical_selected
  · simpa only [payload,expandedPayload] using JFw_Blocks.bytes 116 (window 4706 1856).val
def record : Slice U8 := frame 4#u8 128#u8 14#u8 0#u8 0#u8 payload (by rw [payload_length];decide)
theorem source_shape : AspisR1RecordParser.r1_wire.row_shape 25#u8 = ok (some (4#u8,3712#usize)) := by
  rw [ExtractedRecordFraming.parser_row_shape_table]
  rfl
theorem accepted : AspisR1PrefixAggregateParser.r1_wire.parse_record 25#u8 record = ok (.Ok payload) := by
  apply JFw_CurrentValidation.record
  apply JFw_Record.success 25#u8 4#u8 128#u8 14#u8 0#u8 0#u8 3712#usize record payload source_shape (by decide) payload_length rfl
  · apply JFw_HeaderCast.eq;scalar_tac
  · intro _;exact fields
theorem bytes : bytesOf record.val = PSem_Rows.expandedRow 25 (slice JFz_RowGeometry.wire 4701 2330) := by
  have head : (slice JFz_RowGeometry.wire 4701 2330).take 5 = bytesOf [4#u8,128#u8,14#u8,0#u8,0#u8] := by
    rw [JFz_RowGeometry.slice_take _ 4701 5 2330 (by decide)]
    simp only [slice,JFz_RowGeometry.wire,bytesOf,←List.map_drop,←List.map_take,JFz_Row25.header]
  simp only [PSem_Rows.expandedRow,JFz_Row25.shape,Prod.snd,if_pos (by decide : 14 ≤ 25),head]
  rw [JFz_RowGeometry.slice_slice _ 4701 2330 5 1856 (by decide)]
  have pbytes := expanded_bytes 116 4706 (by decide) (by decide)
  change bytesOf ([4#u8,128#u8,14#u8,0#u8,0#u8] ++ payload.val) = _
  rw [MultiproofConeExpandModel.bytes_append]
  exact congrArg (fun tail => bytesOf [4#u8,128#u8,14#u8,0#u8,0#u8] ++ tail) pbytes
#print axioms payload_length
#print axioms fields
#print axioms source_shape
#print axioms accepted
#print axioms bytes
end AspisR1.JFw_NativeRow25
end
