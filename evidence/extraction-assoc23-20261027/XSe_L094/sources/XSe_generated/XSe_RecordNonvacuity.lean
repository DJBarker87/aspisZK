import XSe_RecordTransport
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_RecordNonvacuity
def empty : Slice U8 := ⟨[],by decide⟩
/-- Actual validator success on the native empty-input domain, for every row.
This is local non-vacuity, not an accepted transaction/headline witness. -/
theorem source (row : U8) : r1_wire.validate_record_fields row empty=ok (.Ok ()) := rfl
/-- The SAME input succeeds in the old cohort, through the full checked carrier. -/
theorem cohort (row : U8) :
 AspisR1PrefixAggregateParser.r1_wire.validate_record_fields row empty=ok (.Ok ()) := by
 rw [←XSe_ValidatorTransport.source row empty (by decide),source]
 rfl
#print axioms source
#print axioms cohort
end XSe_RecordNonvacuity
