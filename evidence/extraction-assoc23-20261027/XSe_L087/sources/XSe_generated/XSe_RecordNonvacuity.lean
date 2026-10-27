import XSe_RecordTransport
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_RecordNonvacuity
def empty : Slice U8 := ⟨[],by decide⟩
def header : Slice U8 := ⟨[0#u8,0#u8,0#u8,0#u8,0#u8],by decide⟩
/-- Unconditional parser success on a real header. This is local non-vacuity,
not an accepted two-transaction or headline witness. -/
theorem source : r1_wire.parse_record 0#u8 header=ok (.Ok empty) := by rfl
/-- The SAME header is accepted by the old cohort through the checked carrier. -/
theorem cohort : AspisR1PrefixAggregateParser.r1_wire.parse_record 0#u8 header=ok (.Ok empty) := by
 rw [←XSe_RecordTransport.source,source]
 rfl
#print axioms source
#print axioms cohort
end XSe_RecordNonvacuity
