import NDF_ValidatorGeometry
import NDF_PrefixValidation
set_option autoImplicit false
namespace NDF_ValidatorEntry
open Aeneas Aeneas.Std Result
open AspisR1.ExtractedPrefixFieldAgreement AspisR1.ExtractedPrefixRecordAgreement

theorem outcome (row : U8) (payload : Slice U8) (cap : payload.val.length≤3712) :
    mapResult statusToRecord (AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row payload) =
      NDF_ValidatorWindows.outcome row
        (NCO_Search.search (NDF_ValidatorWindows.bad payload) (payload.val.length/32) 0) := by
  rw [validator_agreement]
  obtain ⟨ce,chunks,windows,widths⟩ := NDF_ValidatorGeometry.decomposition payload
  unfold AspisR1RecordParser.r1_wire.validate_record_fields
  rw [chunks]
  simp only [bind_tc_ok,core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default]
  rw [NDF_ValidatorRun.source row ⟨ce,0#usize⟩ widths,windows]
  exact NDF_ValidatorWindows.scan payload row (payload.val.length/32) 0#usize (by omega) (by scalar_tac)

#print axioms outcome
end NDF_ValidatorEntry
