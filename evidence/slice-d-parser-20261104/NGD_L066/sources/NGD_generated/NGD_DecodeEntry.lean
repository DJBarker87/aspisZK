import NGD_DecodeTrace
import NGD_DecodeGuards
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGD_DecodeEntry
open AspisR1DecodeKFullV10
/-- Entry plumbing into the exact emitted iteration trace. The premises expose
only primitive checked operations, the original payload and per-step trace;
there is no accepted-output or whole-call premise. -/
theorem ready (N off start size finish : Usize)
    (r : r1_wire.ValidatedRecord) (payload window : Slice U8)
    (row : ¬r.row < 14#u8)
    (offset : Usize.checked_mul off 32#usize = some start)
    (length : Usize.checked_mul N 32#usize = some size)
    (addition : Usize.checked_add start size = some finish)
    (original : r1_wire.ValidatedRecord.payload r = ok payload)
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      payload {start, «end»:=finish} = ok (some window))
    (d : NGD_DecodeTrace.Domain N r off start)
    (final : NGD_DecodeTrace.Final N)
    (trace : NGD_DecodeTrace.Trace d {start:=0#usize,«end»:=N}
      (Array.repeat N aspis_core.field.QM31.ZERO) final) :
    r1_wire.ValidatedRecord.decode_k N r off =
      ok (match final.2 with | none => .Ok final.1 | some reply => reply) := by
  have run := NGD_DecodeTrace.loop d _ _ final trace
  simp only [r1_wire.ValidatedRecord.decode_k,row,offset,length,addition,original,get,
    lift,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    bind_tc_ok]
  rw [run]
  cases final with
  | mk out pending => cases pending <;> rfl
#print axioms ready
end NGD_DecodeEntry
