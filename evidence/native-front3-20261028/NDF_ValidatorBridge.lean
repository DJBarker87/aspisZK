import NDF_ValidatorReference
import NDF_ValidatorEntry
set_option autoImplicit false
namespace NDF_ValidatorBridge
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedPrefixFieldAgreement AspisR1.ExtractedPrefixRecordAgreement

theorem reference (row : U8) (payload : Slice U8) (cap : payload.val.length≤3712) :
    (do let status ← NCO_ParserRef.validate_ref row payload; ok (NCO_Framing.result status)) =
      AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload := by
  apply NDF_PrefixValidation.map_injective statusToRecord NDF_PrefixValidation.status_injective
  rw [mapResult_bind]
  simp only [mapResult_ok]
  change NDF_ValidatorReference.reference row payload =
    mapResult statusToRecord (AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload)
  rw [NDF_ValidatorReference.outcome row payload cap,NDF_ValidatorEntry.outcome row payload cap]

#print axioms reference
end NDF_ValidatorBridge
