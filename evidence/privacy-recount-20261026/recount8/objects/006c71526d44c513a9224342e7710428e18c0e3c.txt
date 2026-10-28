import R1Z.PV_RunJoin_ByteRange39
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteSlice40
open Aeneas Aeneas.Std Result

/-- Exact source slice payload and length; bounds are the entire domain. -/
theorem range (logical : Slice U8) (first last : Usize)
    (ordered : first.val≤last.val) (bound : last.val≤logical.length) :
    ∃ s, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      logical {start:=first, «end»:=last}=.ok s ∧
      s.val=(logical.val.drop first.val).take (last.val-first.val) ∧
      s.length=last.val-first.val := by
  obtain ⟨s,hs,hval⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ({start:=first, «end»:=last} : core.ops.range.Range Usize) logical ordered bound)
  have hv : s.val=(logical.val.drop first.val).take (last.val-first.val) := by
    simpa only [List.slice] using hval.1
  refine ⟨s,hs,hv,?_⟩
  change s.val.length=_
  rw [hv,List.length_take,List.length_drop]
  have hlen : logical.length=logical.val.length := rfl
  rw [hlen] at bound
  omega
#print axioms range
end R1Z.PV_RunJoin_ByteSlice40
