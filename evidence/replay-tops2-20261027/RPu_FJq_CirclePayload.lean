import RPu_FJq_DecodeChunk
import R1CircleRecordCodec
import RPu_FIq_S_RecordFrameDropPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJq_CirclePayload
open Aeneas Aeneas.Std AspisR1PublicPreparation
/-- The literal row decoder and installed reader remove the SAME five bytes. -/
theorem value (row : Fin 2) (record : r1_wire.ValidatedRecord)
    (payload : CircleRecordCodec.Payload row)
    (parsed : CircleRecordCodec.decode row (record.framed.val.map ExtractedRecordByteValue.rawByte)=some payload) :
    SelectedFieldSequenceCodec.decodeLow (CircleRecordCodec.count row)
      ((record.framed.val.drop 5).map ExtractedRecordByteValue.rawByte)=some payload := by
  have encoded:=CircleRecordCodec.encode_of_decode row _ payload parsed
  have data:=congrArg (fun xs : List SemanticCoefficientCodec.Byte=>xs.drop 5) encoded
  have same : SelectedFieldSequenceCodec.encodeLow payload=
      (record.framed.val.drop 5).map ExtractedRecordByteValue.rawByte := by
    simpa only [CircleRecordCodec.encode,RecordFrameDropPayload.drop_frame,List.map_drop] using data
  rw [←same]
  exact SelectedFieldSequenceCodec.decodeLow_encode payload
#print axioms value
end AspisR1.FJq_CirclePayload
end
