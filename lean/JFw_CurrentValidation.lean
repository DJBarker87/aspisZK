import JFw_BlockValidation
import ExtractedPrefixParserAgreement
set_option autoImplicit false
namespace AspisR1.JFw_CurrentValidation
open Aeneas Aeneas.Std Result
open ExtractedPrefixFieldAgreement ExtractedPrefixRecordAgreement

theorem map_success {α : Type} (m : Result (core.result.Result α AspisR1PrefixAggregateParser.r1_wire.Error))
    (v : α) : mapResult statusToRecord m = ok (.Ok v) ↔ m = ok (.Ok v) := by
  cases m with
  | fail e => simp [mapResult]
  | div => simp [mapResult]
  | ok status => cases status <;> simp [mapResult,statusToRecord]

theorem validator (row : U8) (payload : Slice U8)
    (success : AspisR1RecordParser.r1_wire.validate_record_fields row payload = ok (.Ok ())) :
    AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload = ok (.Ok ()) := by
  apply (map_success _ ()).mp
  rw [validator_agreement]
  exact success

theorem record (row : U8) (frame payload : Slice U8)
    (success : AspisR1RecordParser.r1_wire.parse_record row frame = ok (.Ok payload)) :
    AspisR1PrefixAggregateParser.r1_wire.parse_record row frame = ok (.Ok payload) := by
  apply (map_success _ payload).mp
  rw [ExtractedPrefixParserAgreement.parse_record_agreement]
  exact success

#print axioms map_success
#print axioms validator
#print axioms record
end AspisR1.JFw_CurrentValidation
