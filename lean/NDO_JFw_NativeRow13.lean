import JFw_HeaderCast
import NDO_JFw_Frames
import JFw_Record
import NDO_JFz_Row13
import ExtractedRecordFraming
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_NativeRow13
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical JFw_Frames
def payload : Slice U8 := window 150 0
theorem payload_length : payload.length = 0 := window_length 150 0 (by decide)
def record : Slice U8 := frame 0#u8 0#u8 0#u8 0#u8 0#u8 payload (by rw [payload_length];decide)
theorem source_shape : AspisR1RecordParser.r1_wire.row_shape 13#u8 = ok (some (0#u8,0#usize)) := by
  rw [ExtractedRecordFraming.parser_row_shape_table]
  rfl
theorem accepted : AspisR1PrefixAggregateParser.r1_wire.parse_record 13#u8 record = ok (.Ok payload) := by
  apply JFw_CurrentValidation.record
  apply JFw_Record.success 13#u8 0#u8 0#u8 0#u8 0#u8 0#u8 0#usize record payload source_shape (by decide) payload_length rfl
  · apply JFw_HeaderCast.eq;scalar_tac
  · intro h;scalar_tac
theorem bytes : bytesOf record.val = PSem_Rows.expandedRow 13 (slice JFz_RowGeometry.wire 145 6886) := by
  have head : (slice JFz_RowGeometry.wire 145 6886).take 5 = bytesOf [0#u8,0#u8,0#u8,0#u8,0#u8] := by
    rw [JFz_RowGeometry.slice_take _ 145 5 6886 (by decide)]
    simp only [slice,JFz_RowGeometry.wire,bytesOf,←List.map_drop,←List.map_take,JFz_Row13.header]
  simp only [PSem_Rows.expandedRow,JFz_Row13.shape,Prod.snd,if_neg (by decide : ¬ 14 ≤ 13),head]
  rw [JFz_RowGeometry.slice_slice _ 145 6886 5 0 (by decide)]
  change bytesOf ([0#u8,0#u8,0#u8,0#u8,0#u8] ++ payload.val) = _
  rw [MultiproofConeExpandModel.bytes_append,payload,window_bytes]
#print axioms payload_length
#print axioms source_shape
#print axioms accepted
#print axioms bytes
end AspisR1.JFw_NativeRow13
end
