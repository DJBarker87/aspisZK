import R1Z.PV_RunJoin_ByteSlice40
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BytePrefix40
open Aeneas Aeneas.Std Result

/-- Actual RangeTo indexing and append, retaining the exact prefix bytes. -/
theorem append (logical : Slice U8) (out : alloc.vec.Vec U8) (last : Usize)
    (bound : last.val≤logical.length) (room : out.length+last.val≤Usize.max) :
    ∃ s next, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      logical { «end» := last }=.ok s ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s=.ok next ∧
      next.val=out.val ++ logical.val.take last.val := by
  obtain ⟨s,hs,hval⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeToUsizeSlice.index.step_spec
      ({ «end» := last } : core.ops.range.RangeTo Usize) logical bound)
  have hv : s.val=logical.val.take last.val := by
    simpa only [List.slice,List.drop_zero,Nat.sub_zero] using hval.1
  have slen : s.length=last.val := by
    change s.val.length=_
    rw [hv,List.length_take]
    have hb : last.val≤logical.val.length := bound
    omega
  obtain ⟨next,hn,hnext⟩ := PV_RunJoin_ByteAppend38.append out s (by rw [slen];exact room)
  exact ⟨s,next,hs,hn,by rw [hnext,hv]⟩
#print axioms append
end R1Z.PV_RunJoin_BytePrefix40
