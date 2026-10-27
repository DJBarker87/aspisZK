import RPu_FIq_S_RawActualDecodedTypedPolynomialAgreement
import RPu_FIq_S_TypedSemanticPolynomialRowPayload
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualPolynomialRowAgreement
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKTypedCoefficients
open AspisR1.SemanticCoefficientCodec
open AspisR1.SemanticRecordCodec

/-- The existing typed-view coeffAt_payload identity supplies hpoly. Actual
and typed decoding share the same whole source frame; payload equality,
strictness, length and field/polynomial equality are all derived. -/
theorem actual_polynomial_row_agrees
    (row : Fin 25) (record : RawActualDecodeKMainAdapter.MainRecord)
    (out : Array MainQM 28#usize) (typedRow : RowPayload row)
    (coefficients : Coefficients)
    (hpoly : typedRow.val = Payload.polynomial coefficients)
    (hactual : RawActualDecodeKMainAdapter.decodeMain
      28#usize record 0#usize = .ok (.Ok out))
    (htyped : AspisR1.SemanticRecordCodec.decode row
      (record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte) = some typedRow) :
    (RawSemanticCheckedStepPolynomialAdapter.exactPolynomial out).map
        (algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact) =
      AspisR1.SemanticCoefficientCodec.polynomial coefficients := by
  have hd := AspisR1.TypedSemanticPolynomialRowPayload.typed_row_payload
    row _ typedRow coefficients hpoly htyped
  have hd' : decodeCoefficients
      ((payload record).map AspisR1.ExtractedRecordByteValue.rawByte) = some coefficients := by
    simpa only [payload, List.map_drop] using hd
  exact RawActualDecodedTypedPolynomialAgreement.actual_decoded_polynomial_eq_typed
    record out coefficients hactual hd'

#print axioms actual_polynomial_row_agrees
end AspisR1PublicPreparation.RawActualPolynomialRowAgreement
end
