import NGO_TraceTotal
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_DecodeTotal
open AspisR1DecodeKFullV10
/-- Entry result is constructed from the original bytes. No trace observation
or desired full result is assumed. Native schedule association is separate. -/
theorem ready (N off start size finish : Usize)
    (r : r1_wire.ValidatedRecord) (payload window : Slice U8)
    (row : ¬r.row < 14#u8)
    (offset : Usize.checked_mul off 32#usize = some start)
    (length : Usize.checked_mul N 32#usize = some size)
    (addition : Usize.checked_add start size = some finish)
    (original : r1_wire.ValidatedRecord.payload r = ok payload)
    (get : core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
      payload {start, «end»:=finish} = ok (some window))
    (d : NGD_DecodeTrace.Domain N r off start) :
    ∃ final, NGD_DecodeTrace.Trace d {start:=0#usize,«end»:=N}
        (Array.repeat N aspis_core.field.QM31.ZERO) final ∧
      r1_wire.ValidatedRecord.decode_k N r off =
        ok (match final.2 with | none => .Ok final.1 | some reply => reply) := by
  obtain ⟨final,trace⟩ := NGO_TraceTotal.exists_trace d
    {start:=0#usize,«end»:=N} (Array.repeat N aspis_core.field.QM31.ZERO) rfl (by simp)
  exact ⟨final,trace,NGD_DecodeEntry.ready N off start size finish r payload window
    row offset length addition original get d final trace⟩
#print axioms ready
end NGO_DecodeTotal
