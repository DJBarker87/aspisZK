import XRu_RecordCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRu_RecordNonvacuity
def bytes : Slice U8 := ⟨[0#u8,0#u8,0#u8,0#u8,0#u8],by scalar_tac⟩
def payload : Slice U8 := ⟨[],by scalar_tac⟩
/-- A real accepted header record, not an accepted complete transaction. -/
theorem emitted : r1_wire.parse_record 0#u8 bytes=ok (.Ok payload) := by
 unfold r1_wire.parse_record
 have shape : r1_wire.row_shape 0#u8=ok (some (0#u8,0#usize)) := by rfl
 rw [shape,bind_tc_ok]
 rfl
theorem cohort : AspisR1PrefixAggregateParser.r1_wire.parse_record 0#u8 bytes=ok (.Ok payload) := by
 unfold AspisR1PrefixAggregateParser.r1_wire.parse_record
 have shape : AspisR1PrefixAggregateParser.r1_wire.row_shape 0#u8=ok (some (0#u8,0#usize)) := by rfl
 rw [shape,bind_tc_ok]
 rfl
#print axioms emitted
#print axioms cohort
end XRu_RecordNonvacuity
