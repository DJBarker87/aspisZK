import TypedSemanticPolynomialRowFrame
import RecordFrameDropPayload

set_option autoImplicit false
set_option maxHeartbeats 20000
namespace AspisR1.TypedSemanticMaskRowPayload
open AspisR1.SemanticRecordCodec
open AspisR1.SemanticCoefficientCodec

/-- The existing claimAt14_payload theorem supplies the constructor identity. -/
theorem typed_mask_row_frame (row : Fin 25)
    (record : AspisR1.SemanticRecordCodec.Bytes) (typedRow : RowPayload row)
    (value : LowWide) (hmask : typedRow.val = Payload.maskSum value)
    (htyped : AspisR1.SemanticRecordCodec.decode row record = some typedRow) :
    AspisR1.RecordFrameCodec.frame 3 (encodeLow value) = record := by
  have he := encode_of_decode row record typedRow htyped
  change AspisR1.RecordFrameCodec.frame (payloadTag typedRow.val)
    (payloadBytes typedRow.val) = record at he
  simpa only [hmask, payloadTag, payloadBytes] using he

theorem typed_mask_row_payload (row : Fin 25)
    (record : AspisR1.SemanticRecordCodec.Bytes) (typedRow : RowPayload row)
    (value : LowWide) (hmask : typedRow.val = Payload.maskSum value)
    (htyped : AspisR1.SemanticRecordCodec.decode row record = some typedRow) :
    decodeLow (record.drop 5) = some value := by
  have hframe := typed_mask_row_frame row record typedRow value hmask htyped
  have hbytes : record.drop 5 = encodeLow value :=
    (congrArg (fun raw => raw.drop 5) hframe.symm).trans
      (AspisR1.RecordFrameDropPayload.drop_frame 3 (encodeLow value))
  exact (congrArg decodeLow hbytes).trans (decodeLow_encode value)

#print axioms typed_mask_row_frame
#print axioms typed_mask_row_payload
end AspisR1.TypedSemanticMaskRowPayload
