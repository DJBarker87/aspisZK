import R1Z.PV_RunJoin_ByteAppend38
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteRange39
open Aeneas Aeneas.Std Result

/-- Actual standard-library range indexing, with its precise bounds, followed
by the existing complete append law. The payload is an independent list slice. -/
theorem append (logical : Slice U8) (out : alloc.vec.Vec U8) (first last : Usize)
    (ordered : first.val≤last.val) (bound : last.val≤logical.length)
    (room : out.length+(last.val-first.val)≤Usize.max) :
    ∃ s next,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        logical {start := first, «end» := last}=.ok s ∧
      alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s=.ok next ∧
      next.val=out.val ++ (logical.val.drop first.val).take (last.val-first.val) := by
  obtain ⟨s,hs,hval⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      ({start := first, «end» := last} : core.ops.range.Range Usize) logical ordered bound)
  have sl : s.val=(logical.val.drop first.val).take (last.val-first.val) := by
    simpa only [List.slice] using hval.1
  have sr : out.length+s.length≤Usize.max := by
    change out.length+s.val.length≤Usize.max
    rw [sl,List.length_take,List.length_drop]
    have hlen : logical.length=logical.val.length := rfl
    rw [hlen] at bound
    omega
  obtain ⟨next,hn,hbytes⟩ := PV_RunJoin_ByteAppend38.append out s sr
  exact ⟨s,next,hs,hn,hbytes.trans (congrArg (fun t => out.val ++ t) sl)⟩

#print axioms append
end R1Z.PV_RunJoin_ByteRange39
