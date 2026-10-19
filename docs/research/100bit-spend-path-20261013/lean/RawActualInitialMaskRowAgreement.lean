import RawActualDecodeKInitialLowClaim
import TypedSemanticMaskRowPayload

set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.RawActualInitialMaskRowAgreement
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
open AspisR1PublicPreparation.RawActualDecodeKTypedCoefficients
open AspisR1.SemanticCoefficientCodec
open AspisR1.SemanticRecordCodec

/-- The initial source value equals the typed row-14 mask-sum claim on the
same original frame. The maskSum constructor identity is supplied by the
existing claimAt14_payload theorem; this does not assert that an arbitrary
claimed value is the true sum of the hidden mask. -/
theorem actual_initial_claim_agrees
    (row : Fin 25) (record : MainRecord) (out : Array MainQM 1#usize)
    (initial : MainQM) (typedRow : RowPayload row) (value : LowWide)
    (hmask : typedRow.val = Payload.maskSum value)
    (hactual : decodeMain 1#usize record 0#usize = .ok (.Ok out))
    (hindex : Array.index_usize out 0#usize = .ok initial)
    (htyped : AspisR1.SemanticRecordCodec.decode row
      (record.framed.val.map AspisR1.ExtractedRecordByteValue.rawByte) = some typedRow) :
    algebraMap AspisR1.ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact
      (AspisR1.ExtractedMaskQM31Exact.decode (mainToProbe initial)) = value.val := by
  have hd := AspisR1.TypedSemanticMaskRowPayload.typed_mask_row_payload
    row _ typedRow value hmask htyped
  have hd' : decodeLow ((payload record).map AspisR1.ExtractedRecordByteValue.rawByte) =
      some value := by
    simpa only [payload, List.map_drop] using hd
  exact RawActualDecodeKInitialLowClaim.decodeMain_one_indexed_wide_value
    record out initial value hactual hindex hd'

#print axioms actual_initial_claim_agrees
end AspisR1PublicPreparation.RawActualInitialMaskRowAgreement
end
