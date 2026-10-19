import R1SemanticRecordCodec
set_option autoImplicit false
namespace AspisR1.TypedSemanticPolynomialRowPayload
open AspisR1.SemanticRecordCodec
open AspisR1.SemanticCoefficientCodec

/-- Constructor identity is supplied by the existing coeffAt_payload theorem.
No case split over unrelated semantic payload constructors is needed. -/
theorem typed_row_payload (row : Fin 25)
    (record : AspisR1.SemanticRecordCodec.Bytes) (typedRow : RowPayload row)
    (coefficients : Coefficients)
    (hpoly : typedRow.val = Payload.polynomial coefficients)
    (htyped : AspisR1.SemanticRecordCodec.decode row record = some typedRow) :
    decodeCoefficients (record.drop 5) = some coefficients := by
  have he := encode_of_decode row record typedRow htyped
  have hframe : AspisR1.RecordFrameCodec.frame 2 (encodeCoefficients coefficients) = record := by
    change AspisR1.RecordFrameCodec.frame (payloadTag typedRow.val)
      (payloadBytes typedRow.val) = record at he
    simpa only [hpoly, payloadTag, payloadBytes] using he
  have hdrop :
      (AspisR1.RecordFrameCodec.frame 2 (encodeCoefficients coefficients)).drop 5 =
        encodeCoefficients coefficients := by
    unfold AspisR1.RecordFrameCodec.frame
    rw [List.drop_append_of_le_length (by rw [AspisR1.RecordFrameCodec.header_length])]
    rw [List.drop_eq_nil_of_le (by rw [AspisR1.RecordFrameCodec.header_length])]
    rfl
  rw [← hframe, hdrop]
  exact decodeCoefficients_encode coefficients

#print axioms typed_row_payload
end AspisR1.TypedSemanticPolynomialRowPayload
