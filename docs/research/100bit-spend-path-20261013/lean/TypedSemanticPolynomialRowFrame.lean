import R1SemanticRecordCodec
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 256
namespace AspisR1.TypedSemanticPolynomialRowFrame
open AspisR1.SemanticRecordCodec
open AspisR1.SemanticCoefficientCodec

/-- Constructor identity is supplied by the existing coeffAt_payload theorem.
No case split over unrelated semantic payload constructors is needed. -/
theorem typed_row_frame (row : Fin 25)
    (record : AspisR1.SemanticRecordCodec.Bytes) (typedRow : RowPayload row)
    (coefficients : Coefficients)
    (hpoly : typedRow.val = Payload.polynomial coefficients)
    (htyped : AspisR1.SemanticRecordCodec.decode row record = some typedRow) :
    AspisR1.RecordFrameCodec.frame 2 (encodeCoefficients coefficients) = record := by
  have he := encode_of_decode row record typedRow htyped
  have hframe : AspisR1.RecordFrameCodec.frame 2 (encodeCoefficients coefficients) = record := by
    change AspisR1.RecordFrameCodec.frame (payloadTag typedRow.val)
      (payloadBytes typedRow.val) = record at he
    simpa only [hpoly, payloadTag, payloadBytes] using he
  exact hframe

#print axioms typed_row_frame
end AspisR1.TypedSemanticPolynomialRowFrame
