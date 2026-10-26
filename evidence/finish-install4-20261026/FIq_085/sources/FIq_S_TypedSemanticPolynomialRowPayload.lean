import FIq_S_TypedSemanticPolynomialRowFrame
import FIq_S_RecordFrameDropPayload
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
  have hframe := AspisR1.TypedSemanticPolynomialRowFrame.typed_row_frame
    row record typedRow coefficients hpoly htyped
  have hbytes : record.drop 5 = encodeCoefficients coefficients :=
    (congrArg (fun raw => raw.drop 5) hframe.symm).trans
      (AspisR1.RecordFrameDropPayload.drop_frame 2 (encodeCoefficients coefficients))
  exact (congrArg decodeCoefficients hbytes).trans (decodeCoefficients_encode coefficients)

#print axioms typed_row_payload
end AspisR1.TypedSemanticPolynomialRowPayload
