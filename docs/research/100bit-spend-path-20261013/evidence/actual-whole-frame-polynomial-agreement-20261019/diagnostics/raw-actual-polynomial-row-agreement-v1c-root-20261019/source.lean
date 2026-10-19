import RawActualDecodedTypedPolynomialAgreement
import R1SemanticRecordCodec

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualPolynomialRowAgreement
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKTypedCoefficients
open AspisR1.SemanticCoefficientCodec
open AspisR1.SemanticRecordCodec

/-- A typed semantic polynomial row and the actual decoder share the entire
same original frame, so their wide polynomials agree. The frame parser's
five-byte header is removed exactly once; no payload equality is assumed. -/
theorem actual_polynomial_row_agrees
    (row : Fin 25) (hrow : 15 ≤ row.val)
    (record : RawActualDecodeKMainAdapter.MainRecord)
    (out : Array MainQM 28#usize) (typedRow : RowPayload row)
    (hactual : RawActualDecodeKMainAdapter.decodeMain
      28#usize record 0#usize = .ok (.Ok out))
    (htyped : AspisR1.SemanticRecordCodec.decode row
      (record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte) = some typedRow) :
    ∃ coefficients : Coefficients,
      typedRow.val = Payload.polynomial coefficients ∧
      (RawSemanticCheckedStepPolynomialAdapter.exactPolynomial out).map
          (algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact) =
        AspisR1.SemanticCoefficientCodec.polynomial coefficients := by
  obtain ⟨typedRow, hvalid⟩ := typedRow
  cases typedRow with
  | empty => simp only [validRow] at hvalid; omega
  | c2Root root => simp only [validRow] at hvalid; omega
  | maskSum value => simp only [validRow] at hvalid; omega
  | polynomial coefficients =>
    have he := encode_of_decode row _ ⟨.polynomial coefficients, hvalid⟩ htyped
    have hdrop :
        (AspisR1.RecordFrameCodec.frame 2 (encodeCoefficients coefficients)).drop 5 =
          encodeCoefficients coefficients := by
      unfold AspisR1.RecordFrameCodec.frame
      rw [List.drop_append_of_le_length (by rw [AspisR1.RecordFrameCodec.header_length])]
      rw [List.drop_eq_nil_of_le (by rw [AspisR1.RecordFrameCodec.header_length])]
      rfl
    have hbytes :
        (payload record).map AspisR1.ExtractedRecordByteValue.rawByte =
          encodeCoefficients coefficients := by
      change (record.framed.val.drop 5).map AspisR1.ExtractedRecordByteValue.rawByte = _
      rw [List.map_drop, ← he]
      exact hdrop
    have hd : decodeCoefficients
        ((payload record).map AspisR1.ExtractedRecordByteValue.rawByte) =
          some coefficients := by
      rw [hbytes]
      exact decodeCoefficients_encode coefficients
    exact ⟨coefficients, rfl,
      RawActualDecodedTypedPolynomialAgreement.actual_decoded_polynomial_eq_typed
        record out coefficients hactual hd⟩

#print axioms actual_polynomial_row_agrees
end AspisR1PublicPreparation.RawActualPolynomialRowAgreement
end
