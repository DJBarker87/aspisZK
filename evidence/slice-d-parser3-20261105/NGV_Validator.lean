import NGV_ValidatorLoop
import NGV_ChunkTail
import NGO_ValidatorErrors
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_Validator
open AspisR1PrefixAggregateParser
/-- Full validator result, including the same first-invalid index and ignored
trailing bytes, on the original borrowed payload. No successful reply premise. -/
theorem result (row : U8) (bytes : Slice U8) (bound : bytes.val.length≤3712) :
 r1_wire.validate_record_fields row bytes =
 NGD_ParseReference.mapResult NGO_ValidatorErrors.mapError
   (NFU_Retarget.r1_wire.validate_record_fields row bytes) := by
 obtain ⟨out,trace⟩:=NFU_Retarget.LPl.Validate.total bytes.val
 obtain ⟨ce,chunks,enumerate,values,remainder⟩:=NGV_ChunkTail.construct bytes
 have native:=NGV_ValidatorLoop.result row bytes ce values bound 0 out trace 0#usize rfl
 have initial : NGO_ScheduleState.state ce 0#usize={iter:=ce,count:=0#usize} := by
   cases ce;simp [NGO_ScheduleState.state]
 rw [initial] at native
 rw [r1_wire.validate_record_fields,chunks,bind_tc_ok,enumerate,bind_tc_ok,native,
   NFU_CompactLeaves.validate_result row bytes out bound trace]
 cases out with
 | none => rfl
 | some i =>
   simp only [NGV_ValidatorLoop.reply]
   split <;> rfl
#print axioms result
end NGV_Validator
