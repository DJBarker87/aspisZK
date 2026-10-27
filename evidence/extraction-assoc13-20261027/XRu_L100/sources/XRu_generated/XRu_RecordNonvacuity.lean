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
 have hadd : (5#usize+0#usize : Result Usize)=ok 5#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
 rw [shape,bind_tc_ok]
 simp [bytes,payload,core.option.Option.ok_or,
  AspisR1PrefixAggregateParser.core.option.Option.ok_or,
  core.result.Result.Insts.CoreOpsTry.branch,hadd]
 rfl
theorem cohort : AspisR1PrefixAggregateParser.r1_wire.parse_record 0#u8 bytes=ok (.Ok payload) := by
 unfold AspisR1PrefixAggregateParser.r1_wire.parse_record
 have shape : AspisR1PrefixAggregateParser.r1_wire.row_shape 0#u8=ok (some (0#u8,0#usize)) := by rfl
 have hadd : (5#usize+0#usize : Result Usize)=ok 5#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
 rw [shape,bind_tc_ok]
 simp [bytes,payload,core.option.Option.ok_or,
  AspisR1PrefixAggregateParser.core.option.Option.ok_or,
  core.result.Result.Insts.CoreOpsTry.branch,hadd]
 rfl
#print axioms emitted
#print axioms cohort
end XRu_RecordNonvacuity
