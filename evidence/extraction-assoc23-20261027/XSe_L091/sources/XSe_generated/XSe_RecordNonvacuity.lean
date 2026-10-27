import XSe_RecordTransport
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_RecordNonvacuity
def empty : Slice U8 := ⟨[],by decide⟩
def header : Slice U8 := ⟨[0#u8,0#u8,0#u8,0#u8,0#u8],by scalar_tac⟩
/-- Unconditional parser success on a real header. This is local non-vacuity,
not an accepted two-transaction or headline witness. -/
theorem source : r1_wire.parse_record 0#u8 header=ok (.Ok empty) := by
 have add : (5#usize+0#usize : Result Usize)=ok 5#usize := by
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
 unfold r1_wire.parse_record
 simp only [r1_wire.row_shape,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,add]
 rfl
/-- The SAME header is accepted by the old cohort through the checked carrier. -/
theorem cohort : AspisR1PrefixAggregateParser.r1_wire.parse_record 0#u8 header=ok (.Ok empty) := by
 rw [←XSe_RecordTransport.source,source]
 rfl
#print axioms source
#print axioms cohort
end XSe_RecordNonvacuity
